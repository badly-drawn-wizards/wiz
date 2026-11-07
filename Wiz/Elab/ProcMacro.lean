import Wiz.Compiler.Run
import Wiz.Elab.Macro

/-!
# Procedural macros

A procedural macro is a Wiz function `f : Macro`, from the prelude:

    def MacroM (A : Type) : Type := Nat → Except String (A × Nat)
    def Macro : Type := Syntax → MacroM Syntax

registered for a node kind with `attribute [macro k] f`. To expand a node of kind `k`
the elaborator **runs `f` in the interpreter**: it encodes the node as a runtime
`Syntax` value, applies `f` to it and to the next free macro scope, and decodes the
result. That needs the host and the prelude to agree on data layouts:

    SyntaxF:  missing | atom (val : String) | ident (val : String)
            | node (kind : String) (args : SyntaxF .false) | nil | cons (head) (tail)
    String := String.mk (data : List Char),   Char := Char.mk (val : Nat)
    List:     nil | cons (head) (tail),        Except: error (e) | ok (a)

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
  --<sol
  match (v.field 0).tag? with
  | some 0 => some .missing
  | some 1 => return .atom info (← (v.conField 0).toString?)
  | some 2 => return .ident info (← (v.conField 0).toString?)
  | some 3 => return .node info (← (v.conField 0).toString?) (← list (v.conField 1) #[])
  | _ => none
where
  list (l : RVal) (acc : Array Syntax) : Option (Array Syntax) :=
    match (l.field 0).tag? with
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

/-- Run the macro `f` on `stx`: returns the expansion and the next free scope. -/
def runProcMacro (code : Code) (f : Name) (stx : Syntax) (scope : Nat) :
    Except String (Syntax × Nat) := do
  let r := apply code (apply code (run code [] (.global f)) (encodeSyntax stx)) (.nat (scope + 1))
  match (r.field 0).tag? with
  | some 0 => throw (((r.conField 0).toString?).getD "macro failed")
  | some 1 =>
    let p := r.conField 0
    let some out := decodeSyntax stx.info (p.field 0) | throw s!"macro {f} returned a malformed syntax tree"
    let next := ((p.field 1).toNat?).getD (scope + 1)
    pure (scopeQuoted scope out, max next (scope + 1))
  | _ => throw s!"macro {f} returned a malformed result"

end Wiz.Elab
