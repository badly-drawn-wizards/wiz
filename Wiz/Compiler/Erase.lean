import Wiz.Core.Check

/-!
# Erasure

Stage 5 starts compilation. A kernel-checked term is turned into an **untyped**
program (`ETerm`) by erasing everything with no runtime content:

* types (anything whose type is a `Sort`), proofs (anything whose type is a `Prop`),
  sizes, quantities, and universe levels all become `◾` (`ETerm.erased`);
* arguments to, and `let`s of, quantity `0` become `◾`. QTT guarantees an erased
  variable is never needed at runtime, so this is the payoff of stage 1.

Binders are kept (an erased argument is passed as `◾`), so de Bruijn indices don't
change. A later pass can drop them.

**Data representation.** A value of `μ D i` is just its payload: nested pairs
`(tag, f₁, …, fₙ, ◾, ◾)`. Pairs are 2-field objects and tags are 0-field objects.
That suits anonymous types. The generic eliminators (`ind`, `Desc.elim`, the `map`
behind coiteration) become runtime **primitives** that walk the description, which
is itself an ordinary runtime value. A real backend (stage 8) specialises them for
known descriptions.

Erasure is **type-directed**, so it is bidirectional like the kernel: `eraseCheck`
knows the expected type, `eraseInfer` computes it with the kernel's `infer`.
-/

namespace Wiz

/-- Runtime primitives: the generic eliminators, interpreted by walking descriptions. -/
inductive Prim where
  /-- `ind D m i x` -/
  | ind
  /-- `delim mret marg mrec D` -/
  | delim
  /-- `coit D step i s` -/
  | coit
  /-- `scofix f i a` -/
  | scofix
  /-- `out x` -/
  | out
  /-- reached an absurd case -/
  | unreachable
  deriving Repr, BEq, Inhabited

inductive ETerm where
  | erased
  | var (ix : Nat)
  | global (name : Name)
  | lam (x : Name) (body : ETerm)
  | app (f a : ETerm)
  | letE (x : Name) (val body : ETerm)
  /-- an object with a tag and fields: pairs are `obj 0 #[a, b]`, tags `obj i #[]` -/
  | obj (tag : Nat) (fields : Array ETerm)
  | proj (i : Nat) (t : ETerm)
  /-- branch on the tag of an object -/
  | case (scrut : ETerm) (branches : Array ETerm)
  /-- `fix x. body`: general recursion (termination was checked by the kernel) -/
  | fix (x : Name) (body : ETerm)
  | prim (op : Prim) (args : Array ETerm)
  /-- a numeral, a native number at runtime -/
  | natLit (n : Nat)
  deriving Repr, Inhabited

namespace ETerm

/-- Shift free variables (`≥ cut`) up by `k`. -/
partial def lift (k : Nat) (cut : Nat := 0) : ETerm → ETerm
  | var i => if i ≥ cut then var (i + k) else var i
  | lam x b => lam x (lift k (cut + 1) b)
  | app f a => app (lift k cut f) (lift k cut a)
  | letE x v b => letE x (lift k cut v) (lift k (cut + 1) b)
  | obj t fs => obj t (fs.map (lift k cut))
  | proj i t => proj i (lift k cut t)
  | case s bs => case (lift k cut s) (bs.map (lift k cut))
  | fix x b => fix x (lift k (cut + 1) b)
  | prim op as => prim op (as.map (lift k cut))
  | t => t

def apps (f : ETerm) (as : List ETerm) : ETerm := as.foldl app f

partial def toString : ETerm → String
  | erased => "◾"
  | var i => s!"#{i}"
  | global n => n
  | lam x b => s!"(λ{x}. {toString b})"
  | app f a => s!"({toString f} {toString a})"
  | letE x v b => s!"(let {x} := {toString v}; {toString b})"
  | obj t fs => s!"⟨{t}{String.join (fs.toList.map (" " ++ toString ·))}⟩"
  | proj i t => s!"{toString t}.{i}"
  | case s bs => s!"(case {toString s} [{", ".intercalate (bs.toList.map toString)}])"
  | fix x b => s!"(fix {x}. {toString b})"
  | prim op as => s!"({reprStr op}{String.join (as.toList.map (" " ++ toString ·))})"
  | natLit n => s!"{n}"

instance : ToString ETerm := ⟨toString⟩

end ETerm

variable {R : Type} [QRig R] [DecidableEq R] [ToString R] [QuantitySyntax R]

/-- Values of this type have no runtime content: types, proofs, sizes, quantities. -/
def erasable (ctx : Ctx R) (ty : VTy R) : Bool :=
  match ty with
  | .sort _ | .size | .sizeLt _ | .qty => true
  | _ => isProp ctx.globals ctx.tys ty

private def isZeroQ (q : Val R) : Bool := q.toPoly? == some []

mutual

/-- **Exercise 5.1a.** Erase `t`, checking it against `ty`.

* if `ty` is `erasable`, the result is `◾`;
* `lam` against a Π: erase the body under the binder;
* `pair` against a Σ: an object `obj 0 #[a, b]`, with `a` erased if the Σ's quantity
  is `0`;
* `con x` against `μ D i` (and `cocon` against `ν`): just the erased payload, checked
  against `⟦D⟧ (μ D) i`;
* `dret`/`darg`/`drec` against `Desc I`: descriptions are runtime data, as
  `obj 0 #[i]`, `obj 1 #[◾, D]` and `obj 2 #[j, D]`;
* `tt` is `◾`; `letE` keeps the binder (with `◾` for a `0` let);
* everything else: `eraseInfer`. -/
partial def eraseCheck (ctx : Ctx R) (t : Term R) (ty : VTy R) : TCM ETerm := do
  if erasable ctx ty then return .erased
  sorry

/-- **Exercise 5.1b.** Erase `t`, computing its type with the kernel's `infer`.

* variables, globals, applications (an argument to a `0`-quantity Π is `◾`);
* `fst`/`snd` are `proj 0`/`proj 1`; `split` binds the projections with `let`s;
* `ecase` on a tag is `case`; `cast` is its argument; `ann` is its term;
* the eliminators `ind`, `Desc.elim`, `out`, `coit`, `scofix` become primitives;
  `sfix` becomes a `fix`, and `scase` applies its method to the payload. -/
partial def eraseInfer (ctx : Ctx R) (t : Term R) : TCM (ETerm × VTy R) := do
  let (ty, _) ← infer ctx t
  if erasable ctx ty then return (.erased, ty)
  if let .natLit n := t then return (.natLit n, ty)
  sorry

/-- Erase a term in inference mode, keeping only the program. -/
partial def eraseE (ctx : Ctx R) (t : Term R) : TCM ETerm := return (← eraseInfer ctx t).1

end

/-- Erase a global definition. -/
def eraseDecl (g : Globals R) (d : Decl R) : TCM ETerm := do
  let some v := d.value | return .prim .unreachable #[]
  let ctx : Ctx R := { globals := g }
  -- universe polymorphism has no runtime content, but `Sort 0` would make motives
  -- propositions (and everything erasable): erase the `Type` instance
  let us := d.levelParams.map fun _ => Level.succ .zero
  eraseCheck ctx (v.instLevels d.levelParams us) (ctx.eval (d.type.instLevels d.levelParams us))

end Wiz
