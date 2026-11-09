import Wiz.Compiler.Run
import Wiz.Elab.Macro

/-!
# Procedural macros

A procedural macro is a Wiz function `f : Macro`, from the prelude:

    def MacroM (A : Type) : Type := TacticM A     -- requests: `fresh`, `fail`
    def Macro : Type := Syntax → MacroM Syntax

registered for a node kind with `attribute [macro k] f`. To expand a node of kind `k`
the elaborator **runs `f` in the interpreter**: it encodes the node as a runtime
`Syntax` value, applies `f` to it, answers its requests (fresh macro scopes) until it
returns, and decodes the result. That needs the host and the prelude to agree on data
layouts:

    SyntaxF:  missing | atom (val : String) | ident (val : String)
            | node (kind : String) (args : SyntaxF .false) | nil | cons (head) (tail)
    String := String.mk (data : List Char),   Char := Char.mk (val : Nat)
    List:     nil | cons (head) (tail),        Tac: see `Elab/Tactic.lean`

and a constructor value with tag `t` and fields `f₁ … fₙ` is the flat object
`⟨t f₁ … fₙ⟩` (see `Erase.lean`).

**Hygiene.** A quotation in a Wiz term marks each identifier it introduces as `x✝`
(a scope still to be chosen). When a macro's output comes back, `x✝` becomes `x✝n`
for this expansion's scope `n`, exactly as `macro_rules` templates are scoped.
-/

namespace Wiz.Elab

/-- A constructor value: a flat object. -/
def mkCon (tag : Nat) (fields : List RVal) : RVal := .obj tag fields.toArray

def encodeString (s : String) : RVal :=
  mkCon 0 [s.toList.foldr (fun c t => mkCon 1 [mkCon 0 [.nat c.toNat], t]) (mkCon 0 [])]

/-- A host syntax tree as a runtime `Syntax` value. -/
partial def encodeSyntax : Syntax → RVal
  | .missing => mkCon 0 []
  | .atom _ v => mkCon 1 [encodeString v]
  | .ident _ n => mkCon 2 [encodeString n]
  | .node _ k args =>
    mkCon 3 [encodeString k, args.foldr (fun a t => mkCon 5 [encodeSyntax a, t]) (mkCon 4 [])]

/-- The `i`th field of a constructor value. -/
def _root_.Wiz.RVal.conField (v : RVal) (i : Nat) : RVal := v.field i

/-- **Exercise 6.3.** Decode a runtime `Syntax` value (see the layouts in the module
docstring; `RVal.tag?`, `RVal.conField` and `RVal.toString?` help). Every node gets
the source position `info` of the macro call, so errors in the expansion point there. -/
partial def decodeSyntax (info : SourceInfo) (v : RVal) : Option Syntax :=
  --<sol
  match v.tag? with
  | some 0 => some .missing
  | some 1 => return .atom info (← (v.conField 0).toString?)
  | some 2 => return .ident info (← (v.conField 0).toString?)
  | some 3 => return .node info (← (v.conField 0).toString?) (← list (v.conField 1) #[])
  | _ => none
where
  list (l : RVal) (acc : Array Syntax) : Option (Array Syntax) :=
    match l.tag? with
    | some 4 => some acc
    | some 5 => do list (l.conField 1) (acc.push (← decodeSyntax info (l.conField 0)))
    | _ => none
  --|ex
  --| sorry
  --sol>

/-- Give the identifiers a quotation introduced (`x✝`) the scope `scope`. -/
partial def scopeQuoted (scope : Nat) : Syntax → Syntax
  | .ident i n => if n.endsWith "✝" then .ident i s!"{n}{scope}" else .ident i n
  | .node i k as => .node i k (as.map (scopeQuoted scope))
  | s => s

/-- What a macro may ask about the environment (HD8): the view of an inductive type
(an `IndView` value) and the type of a declaration (a `Syntax` value), if they exist.
The command elaborator supplies them (`Elab/Reflect.lean`). -/
structure MacroEnv where
  inductive? : String → Option RVal := fun _ => none
  declType? : String → Option RVal := fun _ => none

/-- Answer a macro's requests until it returns. `v` is a `Tac` value; the result is the
syntax it returns (scoped with `scope`) and the next free scope. A macro may ask for
fresh scopes (`fresh`), fail (`fail`), `trace` (ignored here), and read the environment
(`getInductive`, `getType`). -/
partial def runMacroTac (code : Code) (env : MacroEnv) (what : String) (info : SourceInfo)
    (scope : Nat) (v : RVal) (next : Nat) : Except String (Syntax × Nat) :=
  let str (r : RVal) := (r.toString?).getD ""
  match v.tag? with
  | some 1 => -- result
    match decodeSyntax info (v.conField 0) with
    | some out => pure (scopeQuoted scope out, next)
    | none => throw s!"{what} returned a malformed syntax tree"
  | some 2 => throw (((v.conField 0).toString?).getD "macro failed") -- fail
  | some 3 => runMacroTac code env what info scope (v.conField 1) next -- trace
  | some 4 => runMacroTac code env what info scope (apply code (v.conField 0) (.nat next)) (next + 1) -- fresh
  | some 21 => -- getInductive
    let ans := (env.inductive? (str (v.conField 0))).map (mkCon 1 [·]) |>.getD (mkCon 0 [])
    runMacroTac code env what info scope (apply code (v.conField 1) ans) next
  | some 22 => -- getType
    let ans := (env.declType? (str (v.conField 0))).map (mkCon 1 [·]) |>.getD (mkCon 0 [])
    runMacroTac code env what info scope (apply code (v.conField 1) ans) next
  | some t => throw s!"{what} made a request ({t}) that only tactics can make"
  | none => throw s!"{what} returned a malformed result"

/-- Run the macro `f` on `stx`: returns the expansion and the next free scope.

`f stx : MacroM Syntax`, and `Macro.run` turns it into a `Tac` request chain ending in
`result stx'` (see `Elab/Tactic.lean`). -/
def runProcMacro (code : Code) (f : Name) (stx : Syntax) (scope : Nat) (env : MacroEnv := {}) :
    Except String (Syntax × Nat) :=
  let m := apply code (run code [] (.global f)) (encodeSyntax stx)
  runMacroTac code env s!"macro {f}" stx.info scope (apply code (run code [] (.global "Macro.run")) m) (scope + 1)

/-- Run the command macro `f : CommandMacro` on `stx`: the commands it expands to. -/
def runCommandMacro (code : Code) (f : Name) (stx : Syntax) (scope : Nat) (env : MacroEnv := {}) :
    Except String (Array Syntax × Nat) := do
  let m := apply code (run code [] (.global f)) (encodeSyntax stx)
  let (out, next) ← runMacroTac code env s!"macro {f}" stx.info scope
    (apply code (run code [] (.global "CommandMacro.run")) m) (scope + 1)
  pure (out.args, next)

/-- Run the deriver `f : Deriver` for the type `T`: the commands it produces. -/
def runDeriver (code : Code) (f : Name) (T : Name) (info : SourceInfo) (scope : Nat) (env : MacroEnv := {}) :
    Except String (Array Syntax × Nat) := do
  let m := apply code (run code [] (.global f)) (encodeString T)
  let (out, next) ← runMacroTac code env s!"deriver {f}" info scope
    (apply code (run code [] (.global "CommandMacro.run")) m) (scope + 1)
  pure (out.args, next)

end Wiz.Elab
