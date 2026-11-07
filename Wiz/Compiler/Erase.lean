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
  /-- `delim mret marg mrec mhrec D` -/
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
* `dret`/`darg`/`drec`/`dhrec` against `Desc I`: descriptions are runtime data, as
  `obj 0 #[i]`, `obj 1 #[◾, D]`, `obj 2 #[j, D]` and `obj 3 #[◾, j, D]`;
* `tt` is `◾`; `letE` keeps the binder (with `◾` for a `0` let);
* everything else: `eraseInfer`. -/
partial def eraseCheck (ctx : Ctx R) (t : Term R) (ty : VTy R) : TCM ETerm := do
  if erasable ctx ty then return .erased
  --<sol
  let g := ctx.globals
  match t, ty with
  | .lam x b, .pi _ _ q dom cod =>
    let some p := q.toPoly? | throw (.other "erasure: unknown quantity")
    let b' ← eraseCheck (ctx.bind x p dom) b (Closure.inst g cod (Val.var ctx.lvl))
    return .lam x b'
  | .pair a b, .sigma _ q A B =>
    let a' ← if isZeroQ q then pure .erased else eraseCheck ctx a A
    let b' ← eraseCheck ctx b (Closure.inst g B (ctx.eval a))
    return .obj 0 #[a', b']
  | .con x, .mu l I D i s _ =>
    eraseCheck ctx x (vInterp g l I D (muFamilyAt l I D ((sizePred? s).getD .szInf)) i)
  | .cocon x, .nu l I D i s _ =>
    eraseCheck ctx x (vInterp g l I D (nuFamilyAt l I D ((sizePred? s).getD .szInf)) i)
  | .dret i, .desc _ I => return .obj 0 #[← eraseCheck ctx i I]
  | .darg _ S D, .desc l I =>
    let D' ← eraseCheck ctx D (.pi "s" .default (.qlit QuantitySyntax.explicitDefault) (ctx.eval S)
      (.mk [I] (.desc l (.var 1))))
    return .obj 1 #[.erased, D']
  | .drec _ j D, .desc l I =>
    return .obj 2 #[← eraseCheck ctx j I, ← eraseCheck ctx D (.desc l I)]
  | .dhrec _ H j D, .desc l I =>
    let jTy : VTy R := .pi "h" .default (.qlit QuantitySyntax.explicitDefault) (ctx.eval H) (.mk [I] (.var 1))
    return .obj 3 #[.erased, ← eraseCheck ctx j jTy, ← eraseCheck ctx D (.desc l I)]
  | .tt, _ => return .erased
  | .letE x q ty' v b, _ =>
    let vTy := ctx.eval ty'
    let some p := (ctx.eval q).toPoly? | throw (.other "erasure: unknown quantity")
    let v' ← if p == [] then pure .erased else eraseCheck ctx v vTy
    let b' ← eraseCheck (ctx.define x p vTy (ctx.eval v)) b ty
    return .letE x v' b'
  | _, _ => return (← eraseInfer ctx t).1
  --|ex
  --| sorry
  --sol>

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
  --<sol
  let g := ctx.globals
  let e : ETerm ← match t with
    | .var ix => pure (.var ix)
    | .const n _ => pure (.global n)
    | .app f a => do
      let (f', fty) ← eraseInfer ctx f
      match fty with
      | .pi _ _ q dom _ =>
        let a' ← if isZeroQ q then pure .erased else eraseCheck ctx a dom
        pure (.app f' a')
      | _ => throw (.other "erasure: application of a non-function")
    | .ann tm ty' => eraseCheck ctx tm (ctx.eval ty')
    | .letE .. => eraseCheck ctx t ty
    | .fst p => pure (.proj 0 (← eraseInfer ctx p).1)
    | .snd p => pure (.proj 1 (← eraseInfer ctx p).1)
    | .split _ s _ _ x y b => do
      let (s', sty) ← eraseInfer ctx s
      let .sigma _ q A B := sty | throw (.other "erasure: split of a non-pair")
      let some pq := q.toPoly? | throw (.other "erasure: unknown quantity")
      -- let s := s'; let x := s.0; let y := s.1; b   (b lives under x, y: lift past s)
      let vx := Val.var ctx.lvl
      let ctx₂ := (ctx.bind x pq A).bind y [] (Closure.inst g B vx)
      let (b', _) ← eraseInfer ctx₂ b
      pure (.letE "s" s' (.letE x (.proj 0 (.var 0)) (.letE y (.proj 1 (.var 1)) (b'.lift 1 2))))
    | .ecase _ m s bs => do
      let (s', sty) ← eraseInfer ctx s
      let .enum ls := sty | throw (.other "erasure: case on a non-tag")
      let mc : Closure R := .mk ctx.env m
      let bs' ← bs.toArray.mapIdxM fun k b => eraseCheck ctx b (Closure.inst g mc (.tag ls k))
      pure (.case s' bs')
    | .cast _ _ _ x => pure (← eraseInfer ctx x).1
    | .absurd .. => pure (.prim .unreachable #[])
    -- eliminators: their function arguments are erased against the kernel's types
    | .ind l I D v P m i x => do
      let w := QuantitySyntax.explicitDefault
      let (vI, vD, vP) := (ctx.eval I, ctx.eval D, ctx.eval P)
      pure (.prim .ind #[← eraseCheck ctx D (.desc l vI), ← eraseCheck ctx m (indMethodTy g l v vI vD vP w),
        ← eraseCheck ctx i vI, ← eraseE ctx x])
    | .delim v P a b c h D => do
      let (dty, _) ← infer ctx D
      let .desc l I := dty | throw (.other "erasure: Desc.elim on a non-description")
      let (ta, tb, tc, th) := delimMethodTys g l I (ctx.eval P) QuantitySyntax.explicitDefault
      let _ := v
      pure (.prim .delim #[← eraseCheck ctx a ta, ← eraseCheck ctx b tb, ← eraseCheck ctx c tc,
        ← eraseCheck ctx h th, ← eraseE ctx D])
    | .out x => pure (.prim .out #[← eraseE ctx x])
    | .coit l I D S st i s => do
      let (vI, vD) := (ctx.eval I, ctx.eval D)
      let stTy := coitStepTy g l vI vD (ctx.eval S) QuantitySyntax.explicitDefault
      pure (.prim .coit #[← eraseCheck ctx D (.desc l vI), ← eraseCheck ctx st stTy, ← eraseCheck ctx i vI,
        ← eraseCheck ctx s (vApp g (ctx.eval S) (ctx.eval i))])
    | .scofix l I D A f _ i a => do
      let (vI, vD, vA) := (ctx.eval I, ctx.eval D, ctx.eval A)
      let fTy := scofixFunTy g l vI vD vA QuantitySyntax.explicitDefault
      pure (.prim .scofix #[← eraseCheck ctx f fTy, ← eraseCheck ctx i vI,
        ← eraseCheck ctx a (vApp g vA (ctx.eval i))])
    | .sfix l I D v P f _ i x => do
      -- (fix self. λ i x. f ◾ (λ j i y. self i y) i x) i x
      let (vI, vD, vP) := (ctx.eval I, ctx.eval D, ctx.eval P)
      let f' ← eraseCheck ctx f (sfixFunTy g l vI vD vP QuantitySyntax.explicitDefault)
      let recE : ETerm := .lam "j" (.lam "i" (.lam "y" (.apps (.var 5) [.var 1, .var 0])))
      let body : ETerm := .lam "i" (.lam "x" (.apps (f'.lift 3) [.erased, recE, .var 1, .var 0]))
      pure (.apps (.fix "self" body) [← eraseCheck ctx i vI, ← eraseE ctx x])
    | .scase l I D v P m s i x => do
      -- m ◾ i payload   (a value of μ is its payload)
      let (vI, vD, vP) := (ctx.eval I, ctx.eval D, ctx.eval P)
      let mTy := scaseMethodTy g l vI vD vP (ctx.eval s) QuantitySyntax.explicitDefault
      let _ := v
      pure (.apps (← eraseCheck ctx m mTy) [.erased, ← eraseCheck ctx i vI, ← eraseE ctx x])
    | .tag _ i => pure (.obj i #[])
    | _ => throw (.other s!"erasure: unexpected term {ctx.showTerm t}")
  return (e, ty)
  --|ex
  --| sorry
  --sol>

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
