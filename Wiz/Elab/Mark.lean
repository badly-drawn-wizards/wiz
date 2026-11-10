import Wiz.Core.Check

/-!
# The marking pass (P2)

The kernel never evaluates a proof, and it makes that checkable: outside a proof, a term
whose sort may be `0` must be **marked** (`prf.{l} t`, `l` the sort of its type) or
neutral-shaped (`Check.lean`, "the proof marker"). The elaborator does not write the
markers while it elaborates: metavariables hide types, and terms read back from values or
built by hand (constructors, recursors, match compilation, instances, tactics) carry
none. This pass inserts them, in every declaration, just before the kernel.

It is a typed traversal that mirrors the kernel's `infer` and `check`, without the
checks: it only needs the type of each subterm, to see its sort.

* It is **total**: where it cannot compute a type (an ill-typed term), it leaves the
  term alone, and the kernel reports the real error.
* It is **untrusted**: a missing marker is the kernel's error "unmarked proof", and a
  wrong one is rejected by the kernel's rule for `prf`.
* It does not go inside a proof (a term it marks at level `0`): proofs are the bulk of a
  library, and nothing in them needs a marker.
* It evaluates the terms it has already marked, so it never runs a proof either.
* With `Globals.fillSorts` (off) it also writes the sort of every `Π`/`Σ` it passes through
  and can compute the sort of (`Sorts` in `Basic.lean` stops at a `fun`, whose variable
  has no type written down; this pass knows it). Off, because writing some sorts and not
  others is worse than writing none: see `Globals.fillSorts`.
-/

namespace Wiz

variable {R : Type} [QRig R] [DecidableEq R] [ToString R] [QuantitySyntax R]

namespace Mark

/-- Does `t`, at the type `ty`, get a marker (and at which level), and is there anything
to mark inside it? Nothing inside a proof (level `0`). -/
def decide (ctx : Ctx R) (t : Term R) (ty : VTy R) : Option Level × Bool :=
  if (if ctx.globals.strictProofs then (t matches .prf ..) else t.neutralShaped) then (none, true) else
  match ctx.sortOf? ty with
  | none => (none, true)
  | some s => if s.isNeverZero then (none, true) else (some s, !s.isZero)

private def sortLevel? (ty : Option (VTy R)) : Option Level :=
  match ty.map whnf with
  | some (.sort l) => some l
  | _ => none

mutual

/-- Mark `t`, which is checked against `ty`. (`ctx.marked`: `t` is the body of a marked
`fun`, which needs no marker of its own; `Check.lean`.) -/
partial def check (ctx : Ctx R) (t : Term R) (ty : VTy R) : Term R :=
  match t with
  | .prf .. => t
  | _ =>
    let (w, inside) := if ctx.marked then (none, true) else decide ctx t ty
    -- below a marker, and below the `fun`s it wraps, the bodies are exempt
    let ctx' := { ctx with marked := (ctx.marked || w.isSome) && (t matches .lam ..) }
    let t := if inside then checkCore ctx' t ty else t
    match w with
    | some l => .prf l t
    | none => t

partial def checkCore (ctx : Ctx R) (t : Term R) (ty : VTy R) : Term R :=
  let g := ctx.globals
  match t, whnf ty with
  | .lam x body, .pi _ _ _ dom cod _ =>
    -- (`ctx.marked` goes on to the body)
    .lam x (check (ctx.bind x [] dom) body (Closure.inst g cod (Val.var ctx.lvl)))
  | t, ty => checkRest { ctx with marked := false } t ty

partial def checkRest (ctx : Ctx R) (t : Term R) (ty : VTy R) : Term R :=
  let g := ctx.globals
  match t, ty with
  | .up a, .ulift _ A => .up (check ctx a A)
  | .letE x q T v b, _ =>
    let (T, _) := type ctx T
    let vT := ctx.eval T
    let v := check ctx v vT
    .letE x q T v (check (ctx.define x [] vT (ctx.eval v)) b ty)
  | .pair a b, .sigma _ _ A B _ =>
    let a := check ctx a A
    .pair a (check ctx b (ctx.instArg B a))
  | .tt, _ => t
  | _, .sizeLt _ => t
  | .dret i, .desc _ I => .dret (check ctx i I)
  | .darg q S D, .desc l I =>
    let (S, _) := type ctx S
    .darg q S (check ctx D (.pi "s" .default (.qlit QuantitySyntax.explicitDefault) (ctx.eval S) (.mk [I] (.desc l (.var 1))) none))
  | .drec q j D, .desc l I => .drec q (check ctx j I) (check ctx D (.desc l I))
  | .dhrec q H j D, .desc l I =>
    let (H, _) := type ctx H
    .dhrec q H (check ctx j (.pi "h" .default (.qlit QuantitySyntax.explicitDefault) (ctx.eval H) (.mk [I] (.var 1)) none))
      (check ctx D (.desc l I))
  | .con x, .mu l I D i s _ => match sizePred? s with
    | some s' => .con (check ctx x (vInterp g l I D (muFamilyAt l I D s') i))
    | none => t
  | .cocon x, .nu l I D i s _ => match sizePred? s with
    | some s' => .cocon (check ctx x (vInterp g l I D (nuFamilyAt l I D s') i))
    | none => t
  | _, _ => (inferCore ctx t).1

/-- Mark `t`, and compute its type (`none`: it could not be computed). -/
partial def infer (ctx : Ctx R) (t : Term R) : Term R × Option (VTy R) :=
  match t with
  | .prf _ t' => (t, (infer ctx t').2)
  | _ =>
    let (t', ty?) := inferCore ctx t
    match ty? with
    | some ty => match (decide ctx t ty).1 with
      | some l => (.prf l t', ty?)
      | none => (t', ty?)
    | none => (t', none)

/-- Mark a type, and compute its level. -/
partial def type (ctx : Ctx R) (t : Term R) : Term R × Option Level :=
  let (t, ty) := infer ctx t
  (t, sortLevel? ty)

partial def inferCore (ctx : Ctx R) (t : Term R) : Term R × Option (VTy R) :=
  let g := ctx.globals
  let w : R := QuantitySyntax.explicitDefault
  match t with
  | .var ix => (t, ctx.types[ix]?)
  | .const n us => (t, (g.find? n).bind fun d =>
      if d.levelParams.length == us.length then some (eval g [] (d.type.instLevels d.levelParams us)) else none)
  | .natLit _ => (t, (g.builtins.lookup "nat").map fun N => ctx.eval (.const N []))
  | .sort l => (t, some (.sort (.succ l)))
  | .pi x bi q A B s =>
    let (A, lA) := type ctx A
    let (B, lB) := type (ctx.bind x [] (ctx.eval A)) B
    let lvl := s.orElse fun _ => return .imax (← lA) (← lB)
    (.pi x bi q A B (if g.fillSorts then lvl else s), lvl.map .sort)
  | .sigma x q A B s =>
    let (A, lA) := type ctx A
    let (B, lB) := type (ctx.bind x [] (ctx.eval A)) B
    let lvl := s.orElse fun _ => return .max (← lA) (← lB)
    (.sigma x q A B (if g.fillSorts then lvl else s), lvl.map .sort)
  | .app f a =>
    let (f, fty) := infer ctx f
    match fty.map whnf with
    | some (.pi _ _ _ dom cod _) =>
      let a := check ctx a dom
      (.app f a, some (ctx.instArg cod a))
    | _ => (.app f a, none)
  | .letE x q T v b =>
    let (T, _) := type ctx T
    let vT := ctx.eval T
    let v := check ctx v vT
    let (b, bty) := infer (ctx.define x [] vT (ctx.eval v)) b
    (.letE x q T v b, bty)
  | .ann tm T =>
    let (T, _) := type ctx T
    let vT := ctx.eval T
    (.ann (check ctx tm vT) T, some vT)
  | .fst p =>
    let (p, ty) := infer ctx p
    match ty.map whnf with
    | some (.sigma _ _ A _ _) => (.fst p, some A)
    | _ => (.fst p, none)
  | .snd p =>
    let (p, ty) := infer ctx p
    match ty.map whnf with
    | some (.sigma _ _ _ B _) => (.snd p, some (Closure.inst g B (vFst (ctx.eval p))))
    | _ => (.snd p, none)
  | .split q s z m x y b =>
    let (s, sty?) := infer ctx s
    match sty?, sty?.map whnf with
    | some sty, some (.sigma _ _ A B _) =>
      let (m, _) := type (ctx.bind z [] sty) m
      let mc : Closure R := .mk ctx.env m
      let vx : Val R := Val.var ctx.lvl
      let vy : Val R := Val.var (ctx.lvl + 1)
      let ctx₂ := (ctx.bind x [] A).bind y [] (Closure.inst g B vx)
      let b := check ctx₂ b (Closure.inst g mc (.pair vx vy))
      (.split q s z m x y b, some (Closure.inst g mc (ctx.eval s)))
    | _, _ => (.split q s z m x y b, none)
  | .unit l | .empty l => (t, some (.sort l))
  | .absurd m e =>
    let (m, _) := type ctx m
    let (e, _) := infer ctx e
    (.absurd m e, some (ctx.eval m))
  | .eq A a b =>
    let (A, _) := type ctx A
    let vA := ctx.eval A
    (.eq A (check ctx a vA) (check ctx b vA), some (.sort 0))
  | .eqTy A B => (.eqTy (type ctx A).1 (type ctx B).1, some (.sort 0))
  | .refl A a =>
    let (A, _) := type ctx A
    let vA := ctx.eval A
    let a := check ctx a vA
    let va := ctx.eval a
    (.refl A a, some (vEq g vA va va))
  | .reflTy X =>
    let (X, _) := type ctx X
    let vX := ctx.eval X
    (.reflTy X, some (vEqType g vX vX))
  | .cast A B e x =>
    -- (the equation is never evaluated: nothing to mark in it)
    let (A, _) := type ctx A
    let (B, _) := type ctx B
    (.cast A B e (check ctx x (ctx.eval A)), some (ctx.eval B))
  | .transp A a P p b e =>
    -- (`p` and `e` are never evaluated)
    let (A, _) := type ctx A
    let vA := ctx.eval A
    let a := check ctx a vA
    let va := ctx.eval a
    let motiveTy : Val R := .pi "b" .default (.qlit 0) vA
      (.mk [va, vA] (.pi "_" .default (.qlit 0) (.eq (.var 2) (.var 1) (.var 0)) (.sort 0) none)) none
    let P := check ctx P motiveTy
    let b := check ctx b vA
    (.transp A a P p b e, some (vApp g (vApp g (ctx.eval P) (ctx.eval b)) (suspend g ctx.env e)))
  | .qty | .size | .enum _ => (t, some (.sort 1))
  | .sizeLt _ => (t, some (.sort 1))
  | .qlit _ => (t, some .qty)
  | .szInf | .szSuc _ => (t, some .size)
  | .tag ls _ => (t, some (.enum ls))
  | .ecase z m s bs =>
    let (s, sty?) := infer ctx s
    match sty?, sty?.map whnf with
    | some sty, some (.enum ls) =>
      let (m, _) := type (ctx.bind z [] sty) m
      let mc : Closure R := .mk ctx.env m
      let bs := bs.zipIdx.map fun (b, k) => check ctx b (Closure.inst g mc (.tag ls k))
      (.ecase z m s bs, some (Closure.inst g mc (ctx.eval s)))
    | _, _ => (.ecase z m s bs, none)
  | .desc l I => (.desc l (type ctx I).1, some (.sort (.succ (.succ l))))
  | .delim v P a b c h D =>
    let (D, dty) := infer ctx D
    match dty.map whnf with
    | some (.desc l I) =>
      let P := check ctx P (delimMotiveTy l v I w)
      let vP := ctx.eval P
      let (ta, tb, tc, th) := delimMethodTys g l I vP w
      (.delim v P (check ctx a ta) (check ctx b tb) (check ctx c tc) (check ctx h th) D, some (vApp g vP (ctx.eval D)))
    | _ => (.delim v P a b c h D, none)
  | .mu l I D i s h =>
    let (I, _) := type ctx I
    let vI := ctx.eval I
    (.mu l I (check ctx D (.desc l vI)) (check ctx i vI) s h, some (.sort (.succ l)))
  | .nu l I D i s h =>
    let (I, _) := type ctx I
    let vI := ctx.eval I
    (.nu l I (check ctx D (.desc l vI)) (check ctx i vI) s h, some (.sort (.succ l)))
  | .ind l I D v P m i x =>
    let (I, _) := type ctx I
    let vI := ctx.eval I
    let D := check ctx D (.desc l vI)
    let vD := ctx.eval D
    let P := check ctx P (indMotiveTy g l v vI vD w)
    let vP := ctx.eval P
    let m := check ctx m (indMethodTy g l v vI vD vP w)
    let i := check ctx i vI
    let vi := ctx.eval i
    let x := check ctx x (.mu l vI vD vi .szInf none)
    (.ind l I D v P m i x, some (vApp g (vApp g vP vi) (ctx.eval x)))
  | .out x =>
    let (x, ty) := infer ctx x
    match ty.map whnf with
    | some (.nu l I D i s _) => match sizePred? s with
      | some s' => (.out x, some (vInterp g l I D (nuFamilyAt l I D s') i))
      | none => (.out x, none)
    | _ => (.out x, none)
  | .sfix l I D v P f s i x =>
    let (I, _) := type ctx I
    let vI := ctx.eval I
    let D := check ctx D (.desc l vI)
    let vD := ctx.eval D
    let P := check ctx P (indMotiveTy g l v vI vD w)
    let vP := ctx.eval P
    let f := check ctx f (sfixFunTy g l vI vD vP w)
    let i := check ctx i vI
    let vi := ctx.eval i
    let x := check ctx x (.mu l vI vD vi (ctx.eval s) none)
    (.sfix l I D v P f s i x, some (vApp g (vApp g vP vi) (ctx.eval x)))
  | .scase l I D v P m s i x =>
    let (I, _) := type ctx I
    let vI := ctx.eval I
    let D := check ctx D (.desc l vI)
    let vD := ctx.eval D
    let P := check ctx P (indMotiveTy g l v vI vD w)
    let vP := ctx.eval P
    let vs := ctx.eval s
    let m := check ctx m (scaseMethodTy g l vI vD vP vs w)
    let i := check ctx i vI
    let vi := ctx.eval i
    let x := check ctx x (.mu l vI vD vi vs none)
    (.scase l I D v P m s i x, some (vApp g (vApp g vP vi) (ctx.eval x)))
  | .scofix l I D A f s i a =>
    let (I, _) := type ctx I
    let vI := ctx.eval I
    let D := check ctx D (.desc l vI)
    let vD := ctx.eval D
    let A := check ctx A (coitStateTy l vI w)
    let vA := ctx.eval A
    let f := check ctx f (scofixFunTy g l vI vD vA w)
    let i := check ctx i vI
    let vi := ctx.eval i
    let a := check ctx a (vApp g vA vi)
    (.scofix l I D A f s i a, some (.nu l vI vD vi (ctx.eval s) none))
  | .coit l I D S st i s =>
    let (I, _) := type ctx I
    let vI := ctx.eval I
    let D := check ctx D (.desc l vI)
    let vD := ctx.eval D
    let S := check ctx S (coitStateTy l vI w)
    let vS := ctx.eval S
    let st := check ctx st (coitStepTy g l vI vD vS w)
    let i := check ctx i vI
    let vi := ctx.eval i
    let s := check ctx s (vApp g vS vi)
    (.coit l I D S st i s, some (.nu l vI vD vi .szInf none))
  | .ulift l A => (.ulift l (type ctx A).1, some (.sort l))
  | .down x =>
    let (x, ty) := infer ctx x
    match ty.map whnf with
    | some (.ulift _ A) => (.down x, some A)
    | _ => (.down x, none)
  -- checked only (no type to compute), metavariables, and the evaluator's own `natOp`
  | .lam .. | .pair .. | .tt | .up _ | .dret _ | .darg .. | .drec .. | .dhrec .. | .con _ | .cocon _
  | .mvar _ | .natOp .. | .prf .. => (t, none)

end

end Mark

/-- A declaration with its proof markers (and the `Π`/`Σ` sorts the pass can compute):
what the kernel requires (`Check.lean`, "the proof marker"). -/
def Decl.withMarks (g : Globals R) (d : Decl R) : Decl R :=
  let ctx : Ctx R := { globals := g }
  let type := (Mark.type ctx d.type).1
  let ty := ctx.eval type
  { d with type, value := d.value.map (Mark.check ctx · ty),
           impl := d.impl.map (Mark.check ctx · ty),
           witness := d.witness.map (Mark.check ctx · ty) }

end Wiz
