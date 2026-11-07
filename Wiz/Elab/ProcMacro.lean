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

and a constructor value with tag `t` and fields `f₁ … fₙ` is `⟨0 ⟨t⟩ ⟨0 f₁ … ⟨0 fₙ ◾⟩⟩⟩`
(see `Run.lean`).

**Hygiene.** A quotation in a Wiz term marks each identifier it introduces as `x✝`
(a scope still to be chosen). When a macro's output comes back, `x✝` becomes `x✝n`
for this expansion's scope `n`, exactly as `macro_rules` templates are scoped.
-/

namespace Wiz.Elab

/-- A constructor value: tag, then the fields in a right-nested chain. -/
def mkCon (tag : Nat) (fields : List RVal) : RVal :=
  .obj 0 #[.obj tag #[], fields.foldr (fun f r => .obj 0 #[f, r]) (.obj 0 #[.erased, .erased])]

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
def _root_.Wiz.RVal.conField (v : RVal) (i : Nat) : RVal :=
  (List.range i).foldl (fun r _ => r.field 1) (v.field 1) |>.field 0

/-- **Exercise 6.3.** Decode a runtime `Syntax` value (see the layouts in the module
docstring; `RVal.tag?`, `RVal.conField` and `RVal.toString?` help). Every node gets
the source position `info` of the macro call, so errors in the expansion point there. -/
partial def decodeSyntax (info : SourceInfo) (v : RVal) : Option Syntax :=
  sorry

/-- Give the identifiers a quotation introduced (`x✝`) the scope `scope`. -/
partial def scopeQuoted (scope : Nat) : Syntax → Syntax
  | .ident i n => if n.endsWith "✝" then .ident i s!"{n}{scope}" else .ident i n
  | .node i k as => .node i k (as.map (scopeQuoted scope))
  | s => s

/-- Run the macro `f` on `stx`: returns the expansion and the next free scope.

`f stx : MacroM Syntax`, and `Macro.run` turns it into a `Tac` request chain ending in
`result stx'` (see `Elab/Tactic.lean`). A macro may only ask for fresh scopes (`fresh`),
fail (`fail`), or `trace` (ignored here). -/
partial def runProcMacro (code : Code) (f : Name) (stx : Syntax) (scope : Nat) :
    Except String (Syntax × Nat) :=
  let m := apply code (run code [] (.global f)) (encodeSyntax stx)
  go (apply code (run code [] (.global "Macro.run")) m) (scope + 1)
where
  go (v : RVal) (next : Nat) : Except String (Syntax × Nat) :=
    match (v.field 0).tag? with
    | some 1 => -- result
      match decodeSyntax stx.info (v.conField 0) with
      | some out => pure (scopeQuoted scope out, next)
      | none => throw s!"macro {f} returned a malformed syntax tree"
    | some 2 => throw (((v.conField 0).toString?).getD "macro failed") -- fail
    | some 3 => go (v.conField 1) next -- trace
    | some 4 => go (apply code (v.conField 0) (.nat next)) (next + 1) -- fresh
    | some t => throw s!"macro {f} made a request ({t}) that only tactics can make"
    | none => throw s!"macro {f} returned a malformed result"

end Wiz.Elab
