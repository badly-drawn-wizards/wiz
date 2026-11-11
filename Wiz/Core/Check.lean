import Wiz.Rig
import Wiz.Core.Conv
import Wiz.Core.Usage
import Wiz.Core.Pretty

/-!
# Bidirectional QTT type checking

Two mutually recursive judgments, each also producing a **usage vector**:

    Γ ⊢ t ⇐ A  ⊣ U      check : Ctx → Term → VTy → TCM (Usage R)
    Γ ⊢ t ⇒ A  ⊣ U      infer : Ctx → Term → TCM (VTy × Usage R)

`U` says how many times `t` uses each variable of `Γ` (head = innermost).

## Rules (`n = |Γ|`, `0ₙ` = `Usage.zeros n`, `q·U` = `Usage.scale q U`)

    ──────────────────────────────── var
    Γ ⊢ x_ix ⇒ Γ[ix].type ⊣ single n ix

    c.{u₁…uₖ} has k level parameters
    ──────────────────────────────── const
    Γ ⊢ c.{us} ⇒ type(c)[us] ⊣ 0ₙ      (globals are not tracked locally)

    ──────────────────────────────── sort
    Γ ⊢ Sort l ⇒ Sort (l+1) ⊣ 0ₙ

    Γ ⊢ A type@i     Γ, x:A ⊢ B type@j
    ──────────────────────────────── pi        (types are erased: usage 0ₙ)
    Γ ⊢ (x :q A) → B ⇒ Sort (imax i j) ⊣ 0ₙ

    Γ, x :q A ⊢ b ⇐ B ⊣ (u :: U)     le u q
    ──────────────────────────────── lam
    Γ ⊢ λx. b ⇐ (x :q A) → B ⊣ U

    Γ ⊢ f ⇒ (x :q A) → B ⊣ U₁     Γ ⊢ a ⇐ A ⊣ U₂
    ──────────────────────────────── app
    Γ ⊢ f a ⇒ B[a/x] ⊣ U₁ + q·U₂

    Γ ⊢ T type   Γ ⊢ v ⇐ T ⊣ U₁   Γ, x :q T := v ⊢ b ⇐ A ⊣ (u :: U₂)   le u q
    ──────────────────────────────── let     (and the ⇒ version)
    Γ ⊢ let x :q T := v; b ⇐ A ⊣ q·U₁ + U₂

    Γ ⊢ T type    Γ ⊢ t ⇐ T ⊣ U
    ──────────────────────────────── ann
    Γ ⊢ (t : T) ⇒ T ⊣ U

    Γ ⊢ t ⇒ A' ⊣ U     A ≡ A'
    ──────────────────────────────── switch
    Γ ⊢ t ⇐ A ⊣ U

## Structural types (stage 4b)

    Γ ⊢ A type@i     Γ, x:A ⊢ B type@j
    ──────────────────────────────── sigma
    Γ ⊢ (q x : A) × B ⇒ Sort (max i j) ⊣ 0ₙ

    Γ ⊢ a ⇐ A ⊣ U₁     Γ ⊢ b ⇐ B[a/x] ⊣ U₂
    ──────────────────────────────── pair      (check only)
    Γ ⊢ (a, b) ⇐ (q x : A) × B ⊣ q·U₁ + U₂

    Γ ⊢ t ⇒ (q x : A) × B ⊣ U     le 1 q  (or Γ is erased)
    ──────────────────────────────── fst       (an erased field can't be projected at runtime)
    Γ ⊢ t.1 ⇒ A ⊣ U
    (`t.1` drops `t.2`: if `B` holds a field that must be used (`mustUse`), `t.1 ⊣ ω·U`,
    so only an unrestricted pair may drop it)

    Γ ⊢ t ⇒ (q x : A) × B ⊣ U     le 0 q  (or Γ is erased)
    ──────────────────────────────── snd       (`t.2` drops the first field: it must allow that)
    Γ ⊢ t.2 ⇒ B[t.1/x] ⊣ U
    (otherwise `t.2 ⊣ ω·U`: only an unrestricted pair, whose field is ω·q, may drop it)

    Γ ⊢ s ⇒ (p x : A) × B ⊣ U₁     Γ, z : (p x : A) × B ⊢ M type
    Γ, x :(q·p) A, y :q B ⊢ b ⇐ M[(x, y)/z] ⊣ (u_y :: u_x :: U₂)
    le u_y q     le u_x (q·p)
    ──────────────────────────────── split
    Γ ⊢ let q (x, y) := s; b ⇒ M[s/z] ⊣ q·U₁ + U₂

    Γ ⊢ Unit_l ⇒ Sort l      Γ ⊢ () ⇐ Unit_l      Γ ⊢ Empty_l ⇒ Sort l

    Γ ⊢ M type     Γ⁰ ⊢ t ⇒ Empty_l
    ──────────────────────────────── absurd    (`t` is never evaluated: an erased position)
    Γ ⊢ absurd M t ⇒ M ⊣ 0ₙ

## Observational equality (stage 4c)

    Γ ⊢ A type@l   l ≠ 0 at every level instance (`isNeverZero`)   Γ ⊢ a, b ⇐ A
    ──────────────────────────────── eq            (a proposition)
    Γ ⊢ a = b ⇒ Prop ⊣ 0ₙ

    Γ ⊢ A type@l    Γ ⊢ B type@l
    ──────────────────────────────── eqTy
    Γ ⊢ A = B ⇒ Prop ⊣ 0ₙ

    Γ ⊢ A type@l (isNeverZero l)   Γ ⊢ a ⇐ A
    ──────────────────────────────── refl          Γ ⊢ X type ⇒ Γ ⊢ reflTy X ⇒ (X = X) ⊣ 0ₙ
    Γ ⊢ refl A a ⇒ (a = a) ⊣ 0ₙ

    Γ ⊢ A, B type@l    Γ ⊢ e ⇐ (A = B)    Γ ⊢ t ⇐ A ⊣ U
    ──────────────────────────────── cast
    Γ ⊢ cast A B e t ⇒ B ⊣ U

    Γ ⊢ a, b ⇐ A    Γ ⊢ P ⇐ (b :0 A) → (_ :0 a = b) → Prop
    Γ ⊢ p ⇐ P a (refl a)    Γ ⊢ e ⇐ (a = b)
    ──────────────────────────────── transp
    Γ ⊢ transp A a P p b e ⇒ P b e ⊣ 0ₙ

Proofs carry no usage: they are erased, and conversion never looks at them.

## Data (stage 4d)

    Γ ⊢ Enum ls ⇒ Type        Γ ⊢ tag ls i ⇒ Enum ls   (i < |ls|)

    Γ ⊢ t ⇒ Enum ls ⊣ U    Γ, z ⊢ M type    Γ ⊢ bₖ ⇐ M[tag k] ⊣ Vₖ
    ──────────────────────────────── ecase     (⊔ = least upper bound in `le`)
    Γ ⊢ ecase t [b…] ⇒ M[t] ⊣ U + (V₀ ⊔ … ⊔ Vₙ)

    Γ ⊢ I type@(l+1) ⇒ Γ ⊢ Desc.{l} I ⇒ Type (l+1); ret/arg/rec/hrec check against it
    Γ ⊢ Desc.elim P mret marg mrec mhrec D ⇒ P D                 (method types: `delimMethodTys`)
    Γ ⊢ μ.{l} I D i ⇒ Type l           Γ ⊢ con x ⇐ μ D i  if  Γ ⊢ x ⇐ ⟦D⟧ (μ D) i
    Γ ⊢ ind P m i x ⇒ P i x ⊣ ω·Uₘ + Uₓ                    (`indMotiveTy`, `indMethodTy`)
    Γ ⊢ ν.{l} I D i ⇒ Type l           Γ ⊢ out x ⇒ ⟦D⟧ (ν D) i
    (at a size: Γ ⊢ μ^s.{l} I D i ⇒ Type l and Γ ⊢ ν^s.{l} I D i ⇒ Type l if also Γ⁰ ⊢ s ⇐ Size)
    Γ ⊢ coit S step i s ⇒ ν D i ⊣ ω·U_step + U_s

## Sizes (stage 4f)

    Γ ⊢ Size, Size< s ⇒ Type      Γ ⊢ ∞, ↑s ⇒ Size      (s is checked erased: Γ⁰ ⊢ s ⇐ Size)
    Γ⁰ ⊢ t ⇐ Size   t is below s (`sizeBelow`; ∞ is not below itself)  ⇒  Γ ⊢ t ⇐ Size< s ⊣ 0ₙ
    Γ ⊢ con x ⇐ μ^s D i  if  s = ↑s' and Γ ⊢ x ⇐ ⟦D⟧ (μ^s' D) i;  cocon x ⇐ ν^s D i likewise
    Γ ⊢ sfix P f s i x ⇒ P i x ⊣ ω·U_f + Uₓ        (`sfixFunTy`; x ⇐ μ^s D i)
    Γ ⊢ scase P m s i x ⇒ P i x ⊣ Uₘ + Uₓ          (`scaseMethodTy`: the method runs once)
    Γ ⊢ scofix A f s i a ⇒ ν^s D i ⊣ ω·U_f + Uₐ    (`scofixFunTy`)

A `Π`/`Σ` may carry its sort; if it does, the sort must be the one the rule computes
(`checkSortNote`).

A method may run once per node, so its usage is scaled by ω (`QRig.many?`, the rig's
unrestricted quantity; a rig without one, like exact counting, rejects methods that use
local variables outside erased positions). Branches of `ecase` are alternatives, so a
case uses the *join* of its branches' usages: with `{0, 1, ω}` a linear variable must be used the same way in
every branch, and an ω variable may be used differently.

`split` is how linear pairs are consumed: `fst p` and `snd p` each use `p`, so
using both on a linear pair uses it twice, and `snd p` alone would drop a linear first
field, so then it uses `p` ω times.

`Γ ⊢ A type@i` means `A ⇒ Sort i`, with its usage **thrown away**: types live in
the erased (0) fragment, so they may mention 0-quantity variables freely.

## Simplification vs. Atkey

Atkey's system indexes judgments by σ ∈ {0, 1} and, in the σ = 0 fragment, doesn't
check linearity at all. We instead check everything in "σ = 1 mode" and then discard
the usage of type positions. That is sound but rejects a few erased terms that Atkey
would accept (e.g. a non-linear lambda *inside a type*, under a linear binder). Fixing
this is an optional exercise.
-/

namespace Wiz

variable {R : Type}

inductive TypeError where
  | unboundGlobal (name : Name)
  | typeMismatch (expected inferred : String)
  | notAFunction (term type : String)
  | notAType (term type : String)
  | cannotInfer (term : String)
  | quantityMismatch (var : Name) (declared used : String)
  | duplicateDecl (name : Name)
  | other (msg : String)
  deriving Repr, BEq, Inhabited

instance : ToString TypeError where
  toString
    | .unboundGlobal n => s!"unbound global: {n}"
    | .typeMismatch e i => s!"type mismatch\n  expected: {e}\n  inferred: {i}"
    | .notAFunction t ty => s!"not a function: {t}\n  has type: {ty}"
    | .notAType t ty => s!"not a type: {t}\n  has type: {ty}"
    | .cannotInfer t => s!"cannot infer a type for {t}; add an annotation"
    | .quantityMismatch x d u => s!"variable {x} declared with quantity {d} but used {u}"
    | .duplicateDecl n => s!"duplicate declaration: {n}"
    | .other m => m

abbrev TCM := Except TypeError

/-- The typing context. All the lists are aligned: index 0 is the innermost binder. -/
structure Ctx (R : Type) where
  globals : Globals R
  /-- values of locals, for evaluating types that mention them -/
  env   : Env R := []
  names : List Name := []
  qtys  : List (QPoly R) := []
  types : List (VTy R) := []
  /-- number of locals in scope = the next fresh de Bruijn level -/
  lvl   : Lvl := 0
  /-- checking an erased position (a type, or an argument to a `0` binder)? There,
  erased fields may be projected. (A light version of Atkey's σ = 0 mode.) -/
  erased : Bool := false

namespace Ctx

variable [QRig R] [DecidableEq R] [QuantitySyntax R]

/-- Go under a binder: the new variable is a fresh neutral. -/
def bind (ctx : Ctx R) (x : Name) (q : QPoly R) (ty : VTy R) : Ctx R :=
  { ctx with
    env := Val.var ctx.lvl :: ctx.env
    names := x :: ctx.names
    qtys := q :: ctx.qtys
    types := ty :: ctx.types
    lvl := ctx.lvl + 1 }

/-- Go under a `let`: the new variable has a known value. -/
def define (ctx : Ctx R) (x : Name) (q : QPoly R) (ty : VTy R) (val : Val R) : Ctx R :=
  { ctx with
    env := val :: ctx.env
    names := x :: ctx.names
    qtys := q :: ctx.qtys
    types := ty :: ctx.types
    lvl := ctx.lvl + 1 }

def eval (ctx : Ctx R) (t : Term R) : Val R := Wiz.eval ctx.globals ctx.env t

/-- `Closure.inst c (ctx.eval a)`, evaluating `a` only if `c`'s body mentions it.
Evaluation is strict, and the codomain of a non-dependent Π (`List.cons : A → List A →
List A`) doesn't need its argument: evaluating it anyway, at every application along a
nested spine (a long list or string literal), would be quadratic in its length. -/
def instArg (ctx : Ctx R) (c : Closure R) (a : Term R) : Val R :=
  match c with
  -- (the placeholder is the stuck unknown, not a well-formed value: if `hasVar` ever
  -- missed an occurrence, the codomain would be stuck on it, not a type that checks)
  | .mk env body => Wiz.eval ctx.globals ((if body.hasVar 0 then ctx.eval a else default) :: env) body

/-- The types of the locals indexed by level, as `conv` wants them. -/
def tys (ctx : Ctx R) : Array (VTy R) := ctx.types.reverse.toArray

variable [QuantitySyntax R] [DecidableEq R]

/-- Render a value for error messages. -/
def showVal (ctx : Ctx R) (v : Val R) : String :=
  (quote ctx.globals ctx.lvl v).pretty ctx.names

def showTerm (ctx : Ctx R) (t : Term R) : String := t.pretty ctx.names

end Ctx

variable [QRig R] [DecidableEq R] [ToString R] [QuantitySyntax R]

/-- A quantity value as a polynomial, or an error if it is something else (e.g. the
result of a stuck computation). -/
def qtyPoly (ctx : Ctx R) (q : Val R) : TCM (QPoly R) :=
  match q.toPoly? with
  | some p => pure p
  | none => throw (.other s!"quantity must be a literal or a quantity variable: {ctx.showVal q}")

/-- **Exercise 1.5.** Leave the scope of a binder `x` declared at quantity `q`:
pop the binder's own usage off the head of the vector and check it is compatible
with `q` (using `QPoly.le`), returning the rest. Throw `quantityMismatch` otherwise. -/
def popUsage (x : Name) (q : QPoly R) : Usage R → TCM (Usage R)
  --<sol
  | used :: rest =>
    if QPoly.le used q then pure rest
    else throw (.quantityMismatch x (toString q) (toString used))
  | [] => throw (.other "internal error: usage vector underflow")
  --|ex
  --| | u => sorry
  --sol>

/-- A `Π`/`Σ`'s sort, when it gives one, must be its sort: type equality trusts it to
tell propositions from other types. -/
def checkSortNote (s : Option Level) (l : Level) : TCM Unit := do
  if let some s := s then
    unless s.equiv l do
      throw (.other s!"internal error: a type marked as in sort {s} is in sort {l}")

/-- The usage of an eliminator's methods (`ind`, `Desc.elim`, `sfix`, `scofix`, `coit`),
which run once per node: any number of times. Scaled by the rig's unrestricted quantity
(`QRig.many?`, ω); a rig without one (exact counting) only lets methods use local
variables in erased positions. -/
def methodUsage (ctx : Ctx R) (u : Usage R) : TCM (Usage R) :=
  match QRig.many? (R := R) with
  | some m => pure (QPoly.const m • u)
  | none =>
    match (u.zip ctx.names).find? fun (p, _) => !QPoly.le p (QPoly.const 0) with
    | some (p, x) => throw (.other s!"a method may run any number of times, so it can't use {x} ({p} times): the rig has no unrestricted quantity")
    | none => pure u

/-- (Q1) Must a value `v` of type `A` be used, i.e. is `A` a `Σ` with a field whose
quantity doesn't allow zero uses (`¬ le 0 q`), here or in its second part? `t.1` discards
`t.2`, so it may do that only when this is false (or the pair is unrestricted). The second
part of a `Σ` has no quantity of its own: a bare `A × World` counts as droppable; a
resource is "linear" here when it sits in a field declared linear. -/
partial def mustUse (ctx : Ctx R) (A : Val R) (v : Val R) : Bool :=
  match whnf A with
  | .sigma _ q _ B _ =>
    match q.toPoly? with
    | some p => !QPoly.le (QPoly.const 0) p || mustUse ctx (Closure.inst ctx.globals B (vFst v)) (vSnd v)
    | none => true
  | _ => false

/-- `mustUse` decided from the type alone, without evaluating the value. `mustUse` needs
the value only to instantiate dependent second parts, and computing it runs the term in
the evaluator at check time: `p.1` on a global builder's result (`(Circuit.netlistS c).1`
in lib/Hdl/Core.wiz) would compute the whole netlist, deep enough to overflow the stack.
So each field is instantiated with a placeholder instead, a fresh variable past the
context (levels `ctx.lvl + k`, `k ≥ 1`; the caller used `ctx.lvl` for the first field).
Evaluation commutes with substituting a variable: a canonical form reached with
placeholders is the same with the real values. So the answer is exact, except where a
placeholder might have mattered: a type stuck on anything but a context variable, axiom
or metavariable (a variable applied, a builtin or observational equality stuck on its
arguments), or a quantity that isn't a polynomial over context variables. Then the
answer is `none`, and the caller decides with the values (`mustUse`). This needs no
syntactic "does the codomain mention the variable" test (`Term.hasVar`), so a wrong
answer from one can't make it drop a linear field. -/
partial def mustUseType? (ctx : Ctx R) (A : Val R) (k : Nat) : Option Bool :=
  match whnf A with
  | .sigma _ q _ B _ =>
    match q.toPoly? with
    | some p =>
      if p.any (fun (vs, _) => vs.any (· ≥ ctx.lvl)) then none
      else if !QPoly.le (QPoly.const 0) p then some true
      else mustUseType? ctx (Closure.inst ctx.globals B (Val.var (ctx.lvl + k))) (k + 1)
    | none => none
  -- stuck, but not on a placeholder: the same with the real values
  | .neutral (.global ..) #[] | .neutral (.mvar _) #[] => some false
  | .neutral (.local l) #[] => if l < ctx.lvl then some false else none
  -- stuck on something that might be a placeholder
  | .neutral .. => none
  -- a canonical type other than `Σ` (whnf removed glued values)
  | _ => some false

/-- (D1 experiment) Is this type a universe, or a function type ending in one? A `Π`
into `Prop` over such a domain is impredicative. -/
partial def largeDomain (ctx : Ctx R) (A : Val R) (l : Nat) : Bool :=
  match whnf A with
  | .sort _ => true
  | .pi _ _ _ _ B _ => largeDomain ctx (Closure.inst ctx.globals B (Val.var l)) (l + 1)
  | _ => false

mutual

/-- **Exercise 1.6.** Check `t` against the type `ty`. Implement the `lam` and `letE`
rules here and fall back to `infer` + `convTy` for everything else. (Stage 4f
replaces `convTy` with `subTy`, sized subtyping: the inferred type must be a subtype
of the expected one.)

**Exercise 4.7a** (stage 4b): the `pair` and `tt` rules. -/
partial def check (ctx : Ctx R) (t : Term R) (ty : VTy R) : TCM (Usage R) :=
  match t, whnf ty with
  -- (given) Q4
  | .up a, .ulift _ A => check ctx a A
  --<sol
  | .lam x body, .pi _ _ q dom cod _ => do
    let q ← qtyPoly ctx q
    let u ← check (ctx.bind x q dom) body (Closure.inst ctx.globals cod (Val.var ctx.lvl))
    popUsage x q u
  | .letE x q tty val body, _ => do
    let q ← checkQty ctx q
    let _ ← checkType ctx tty
    let vty := ctx.eval tty
    let uv ← check ctx val vty
    let ub ← check (ctx.define x q vty (ctx.eval val)) body ty
    let ub ← popUsage x q ub
    pure (q • uv + ub)
  | .pair a b, .sigma _ q A B _ => do
    let q ← qtyPoly ctx q
    let ua ← check ctx a A
    let ub ← check ctx b (ctx.instArg B a)
    pure (q • ua + ub)
  | .tt, .unit _ => pure (Usage.zeros ctx.lvl)
  | t, .sizeLt s => do
    -- a size below `s` (`∞` is not below itself)
    let _ ← check { ctx with erased := true } t .size
    unless sizeBelow ctx.tys (ctx.eval t) s do
      throw (.other s!"the size {ctx.showTerm t} is not below {ctx.showVal s}")
    pure (Usage.zeros ctx.lvl)
  | .dret i, .desc _ I => check ctx i I
  | .darg q S D, .desc l I => do
    let _ ← checkQty ctx q
    let lS ← checkType ctx S
    -- a field lives exactly in `Sort (l+1)`, the universe `Desc.elim`'s `marg` takes it
    -- from (Q4: universes aren't cumulative; the elaborator lifts smaller fields)
    unless lS.equiv (.succ l) do
      throw (.other s!"a description's field type must be in Sort {(Level.succ l).format}, not Sort {lS.format} (lift it with ULift)")
    check ctx D (.pi "s" .default (.qlit QuantitySyntax.explicitDefault) (ctx.eval S) (.mk [I] (.desc l (.var 1))) none)
  | .drec q j D, .desc l I => do
    let _ ← checkQty ctx q
    let uj ← check ctx j I
    let uD ← check ctx D (.desc l I)
    pure (uj + uD)
  | .dhrec q H j D, .desc l I => do
    -- strict positivity is automatic: `H` can't mention the type being defined
    let _ ← checkQty ctx q
    let lH ← checkType ctx H
    unless lH.equiv (.succ l) do
      throw (.other s!"a description's branching type must be in Sort {(Level.succ l).format}, not Sort {lH.format} (lift it with ULift)")
    let uj ← check ctx j (.pi "h" .default (.qlit QuantitySyntax.explicitDefault) (ctx.eval H) (.mk [I] (.var 1)) none)
    let uD ← check ctx D (.desc l I)
    pure (uj + uD)
  | .con x, .mu l I D i s _ => do
    let some s' := sizePred? s
      | throw (.other s!"a constructor builds a value of size ↑s, not {ctx.showVal s}")
    check ctx x (vInterp ctx.globals l I D (muFamilyAt l I D s') i)
  | .cocon x, .nu l I D i s _ => do
    let some s' := sizePred? s
      | throw (.other s!"cocon builds a value of size ↑s, not {ctx.showVal s}")
    check ctx x (vInterp ctx.globals l I D (nuFamilyAt l I D s') i)
  | _, _ => do
    let (ty', u) ← infer ctx t
    unless subTy ctx.globals ctx.tys ty' ty do
      throw (.typeMismatch (ctx.showVal ty) (ctx.showVal ty'))
    pure u
  --|ex
  --| | .lam x body, .pi _ _ q dom cod _ => sorry
  --| | .letE x q tty val body, _ => sorry
  --| -- Exercise 4.7a
  --| | .pair a b, .sigma _ q A B _ => sorry
  --| | .tt, .unit _ => sorry
  --| -- Exercise 4.20
  --| | .dret i, .desc _ I => sorry
  --| | .darg q S D, .desc l I => sorry
  --| | .drec q j D, .desc l I => sorry
  --| | .dhrec q H j D, .desc l I => sorry
  --| | .con x, .mu l I D i _ _ => sorry
  --| | _, _ => sorry
  --sol>

/-- **Exercise 1.7.** Infer the type of `t`. See the rules in the module docstring.
`checkType` (below) handles the "`A type@i`" premises.

**Exercise 4.14** (stage 4c): `eq`, `eqTy`, `refl`, `reflTy`, `cast`, `transp`.

**Exercise 4.7b** (stage 4b): `sigma`, `fst`, `snd`, `split`, `unit`, `empty`,
`absurd`. `pair` and `tt` can only be checked. -/
partial def infer (ctx : Ctx R) (t : Term R) : TCM (VTy R × Usage R) :=
  match t with
  | .mvar m => throw (.other s!"the kernel does not accept metavariables (?m{m})")
  | .natLit _ =>
    -- a numeral means `succ (… zero)`, so it needs both constructors, as definitions
    let defined (k : Name) := match (ctx.globals.builtins.lookup k).bind ctx.globals.find? with
      | some { value := some _, .. } => true
      | _ => false
    match ctx.globals.builtins.lookup "nat" with
    | some N =>
      if defined "nat.zero" && defined "nat.succ" then pure (ctx.eval (.const N []), Usage.zeros ctx.lvl)
      else throw (.other "numerals need `builtin nat.zero := …` and `builtin nat.succ := …`")
    | none => throw (.other "numerals need `builtin nat := …`")
  | .natOp .. => throw (.cannotInfer (ctx.showTerm t))
  -- (given) Q4: lifting
  | .ulift l A => do
    let k ← checkType ctx A
    unless Level.le k l do
      throw (.other s!"ULift.{l.format} can't lift {ctx.showTerm A}, which is in Sort {k.format}")
    pure (.sort l, Usage.zeros ctx.lvl)
  | .up _ => throw (.cannotInfer (ctx.showTerm t))
  | .down x => do
    let (ty, u) ← infer ctx x
    match whnf ty with
    | .ulift _ A => pure (A, u)
    | _ => throw (.typeMismatch "a lifted type (ULift)" (ctx.showVal ty))
  --<sol
  -- (an index beyond the context is an error: `[ix]!` would panic and go on with the
  -- default value `Sort 0`, as the variable's type and as its value: a term `Prop : Prop`)
  | .var ix => match ctx.types[ix]? with
    | some ty => pure (ty, Usage.single ctx.lvl ix)
    | none => throw (.other s!"variable #{ix} is out of scope ({ctx.lvl} in scope)")
  | .const n us => match ctx.globals.find? n with
    | some d => do
      unless d.levelParams.length == us.length do
        throw (TypeError.other s!"{n} expects {d.levelParams.length} universe levels, got {us.length}")
      pure (Wiz.eval ctx.globals [] (d.type.instLevels d.levelParams us), Usage.zeros ctx.lvl)
    | none => throw (.unboundGlobal n)
  | .sort l => pure (.sort (.succ l), Usage.zeros ctx.lvl)
  | .pi x _ q dom cod s => do
    let q ← checkQty ctx q
    let i ← checkType ctx dom
    let j ← checkType (ctx.bind x q (ctx.eval dom)) cod
    -- (D1 experiment, off by default) predicative `Prop`: no quantifying over a universe
    -- into `Prop`
    if ctx.globals.predicativeProp && j.equiv 0 && largeDomain ctx (ctx.eval dom) ctx.lvl then
      throw (.other s!"impredicative Π (into Prop over {ctx.showTerm dom}) under predicative Prop")
    checkSortNote s (.imax i j)
    pure (.sort (.imax i j), Usage.zeros ctx.lvl)
  --|ex
  --| | .var ix => sorry
  --| | .const n us => sorry
  --| | .sort l => sorry
  --| | .pi x _ q dom cod s => sorry
  --sol>
  | .lam .. => throw (.cannotInfer (ctx.showTerm t))
  --<sol
  | .app f a => do
    let (fty, uf) ← infer ctx f
    match whnf fty with
    | .pi _ _ q dom cod _ =>
      let q ← qtyPoly ctx q
      let ua ← check (if q.isConst? == some 0 then { ctx with erased := true } else ctx) a dom
      pure (ctx.instArg cod a, uf + q • ua)
    | _ => throw (.notAFunction (ctx.showTerm f) (ctx.showVal fty))
  | .letE x q tty val body => do
    let q ← checkQty ctx q
    let _ ← checkType ctx tty
    let vty := ctx.eval tty
    let uv ← check ctx val vty
    let (bty, ub) ← infer (ctx.define x q vty (ctx.eval val)) body
    let ub ← popUsage x q ub
    pure (bty, q • uv + ub)
  | .ann tm tty => do
    let _ ← checkType ctx tty
    let vty := ctx.eval tty
    let u ← check ctx tm vty
    pure (vty, u)
  | .sigma x q a b s => do
    let q ← checkQty ctx q
    let i ← checkType ctx a
    let j ← checkType (ctx.bind x q (ctx.eval a)) b
    checkSortNote s (.max i j)
    pure (.sort (.max i j), Usage.zeros ctx.lvl)
  | .fst t => do
    let (ty, u) ← infer ctx t
    match whnf ty with
    | .sigma x q A B _ =>
      let q ← qtyPoly ctx q
      unless ctx.erased || QPoly.le (QPoly.const 1) q do
        throw (.other s!"cannot project the field {x}, which has quantity {q}; use let (x, y) := ... instead")
      -- `t.1` discards the second part (Q1): if that holds a field that must be used,
      -- only an unrestricted pair may drop it, so `t` counts as used ω times
      -- (from the type alone when it can be decided so: `ctx.eval t` would run `t`)
      if ctx.erased then pure (A, u) else
      let mustUse? : Bool := match mustUseType? ctx (Closure.inst ctx.globals B (Val.var ctx.lvl)) 1 with
        | some b => b
        | none => let v := ctx.eval t; mustUse ctx (Closure.inst ctx.globals B (vFst v)) (vSnd v)
      if !mustUse? then pure (A, u) else
      match QRig.many? (R := R) with
      | some m => pure (A, QPoly.const m • u)
      | none => throw (.other s!"cannot discard the second part of {ctx.showTerm t}, which holds a linear field; use let (x, y) := ... instead")
    | _ => throw (.other s!"not a pair: {ctx.showTerm t}\n  has type: {ctx.showVal ty}")
  | .snd t => do
    let (ty, u) ← infer ctx t
    match whnf ty with
    | .sigma x q _ B _ =>
      -- `t.2` discards the first field: only allowed if the field may go unused
      let q ← qtyPoly ctx q
      let ty := Closure.inst ctx.globals B (vFst (ctx.eval t))
      if ctx.erased || QPoly.le (QPoly.const 0) q then pure (ty, u) else
      -- a field that must be used can be dropped only from an unrestricted pair (whose
      -- fields are ω·q): so `t` counts as used ω times
      match QRig.many? (R := R) with
      | some m => pure (ty, QPoly.const m • u)
      | none => throw (.other s!"cannot discard the field {x}, which has quantity {q}; use let (x, y) := ... instead")
    | _ => throw (.other s!"not a pair: {ctx.showTerm t}\n  has type: {ctx.showVal ty}")
  | .split q s z m x y b => do
    let q ← checkQty ctx q
    let (sty, us) ← infer ctx s
    match whnf sty with
    | .sigma _ p A B _ =>
      let p ← qtyPoly ctx p
      let _ ← checkType (ctx.bind z [] sty) m
      let mc : Closure R := .mk ctx.env m
      let vx : Val R := Val.var ctx.lvl
      let vy : Val R := Val.var (ctx.lvl + 1)
      let ctx₂ := (ctx.bind x (q * p) A).bind y q (Closure.inst ctx.globals B vx)
      let ub ← check ctx₂ b (Closure.inst ctx.globals mc (.pair vx vy))
      let ub ← popUsage y q ub
      let ub ← popUsage x (q * p) ub
      pure (Closure.inst ctx.globals mc (ctx.eval s), q • us + ub)
    | _ => throw (.other s!"not a pair: {ctx.showTerm s}\n  has type: {ctx.showVal sty}")
  | .unit l => pure (.sort l, Usage.zeros ctx.lvl)
  | .empty l => pure (.sort l, Usage.zeros ctx.lvl)
  | .absurd m t => do
    let _ ← checkType ctx m
    -- `t` can never be evaluated (nothing inhabits the empty type): an erased position
    let (ty, _) ← infer { ctx with erased := true } t
    match whnf ty with
    | .empty _ => pure (ctx.eval m, Usage.zeros ctx.lvl)
    | _ => throw (.typeMismatch "an empty type" (ctx.showVal ty))
  | .pair .. | .tt => throw (.cannotInfer (ctx.showTerm t))
  | .eq A a b => do
    let l ← checkType ctx A
    unless l.isNeverZero do
      throw (.other s!"equality is for types in Type u, not propositions: {ctx.showTerm A}")
    let vA := ctx.eval A
    let _ ← check ctx a vA
    let _ ← check ctx b vA
    pure (.sort 0, Usage.zeros ctx.lvl)
  | .eqTy A B => do
    let l ← checkType ctx A
    let l' ← checkType ctx B
    unless l.equiv l' do throw (.other "type equality between different universes")
    pure (.sort 0, Usage.zeros ctx.lvl)
  | .refl A a => do
    let l ← checkType ctx A
    unless l.isNeverZero do throw (.other "refl is for terms of types in Type u")
    let _ ← check ctx a (ctx.eval A)
    let va := ctx.eval a
    pure (vEq ctx.globals (ctx.eval A) va va, Usage.zeros ctx.lvl)
  | .reflTy X => do
    let _ ← checkType ctx X
    let vX := ctx.eval X
    pure (vEqType ctx.globals vX vX, Usage.zeros ctx.lvl)
  | .cast A B e t => do
    let l ← checkType ctx A
    let l' ← checkType ctx B
    unless l.equiv l' do throw (.other "cast between different universes")
    let vA := ctx.eval A
    let vB := ctx.eval B
    let _ ← check { ctx with erased := true } e (vEqType ctx.globals vA vB)
    let u ← check ctx t vA
    pure (vB, u)
  | .transp A a P p b e => do
    -- a proof: everything in it is erased
    let ctx := { ctx with erased := true }
    let _ ← checkType ctx A
    let vA := ctx.eval A
    let _ ← check ctx a vA
    let va := ctx.eval a
    -- (b :0 A) → (_ :0 a = b) → Prop, with env [a, A]
    let motiveTy : Val R := .pi "b" .default (.qlit 0) vA
      (.mk [va, vA] (.pi "_" .default (.qlit 0) (.eq (.var 2) (.var 1) (.var 0)) (.sort 0) none)) none
    let _ ← check ctx P motiveTy
    let vP := ctx.eval P
    let g := ctx.globals
    let _ ← check ctx p (vApp g (vApp g vP va) (.neutral (.refl vA va) #[]))
    let _ ← check ctx b vA
    let vb := ctx.eval b
    let _ ← check ctx e (vEq g vA va vb)
    pure (vApp g (vApp g vP vb) (ctx.eval e), Usage.zeros ctx.lvl)
  | .qty => pure (.sort 1, Usage.zeros ctx.lvl)
  | .qlit _ => pure (.qty, Usage.zeros ctx.lvl)
  | .size => pure (.sort 1, Usage.zeros ctx.lvl)
  | .sizeLt s => do let _ ← check { ctx with erased := true } s .size; pure (.sort 1, Usage.zeros ctx.lvl)
  | .szInf => pure (.size, Usage.zeros ctx.lvl)
  | .szSuc s => do let _ ← check { ctx with erased := true } s .size; pure (.size, Usage.zeros ctx.lvl)
  | .enum _ => pure (.sort 1, Usage.zeros ctx.lvl)
  | .tag ls i => do
    unless i < ls.length do throw (.other s!"tag {i} out of range for {ls.length} labels")
    pure (.enum ls, Usage.zeros ctx.lvl)
  | .ecase z m s bs => do
    let (sty, us) ← infer ctx s
    let .enum ls := whnf sty | throw (.typeMismatch "an enumeration" (ctx.showVal sty))
    unless bs.length == ls.length do throw (.other s!"ecase needs {ls.length} branches, got {bs.length}")
    let _ ← checkType (ctx.bind z [] sty) m
    let mc : Closure R := .mk ctx.env m
    let mut ub : Option (Usage R) := none
    for b in bs, k in [0:bs.length] do
      let u ← check ctx b (Closure.inst ctx.globals mc (.tag ls k))
      match ub with
      | none => ub := some u
      | some u' =>
        let joined := (u.zip u').mapM fun (p, p') => QPoly.join? p p'
        let some j := joined | throw (.other "the branches of a case use variables incompatibly")
        ub := some j
    pure (Closure.inst ctx.globals mc (ctx.eval s), us + ub.getD (Usage.zeros ctx.lvl))
  | .desc l I => do
    let lI ← checkType ctx I
    unless lI.equiv (.succ l) do throw (.other "a description's index type must be in its universe")
    pure (.sort (.succ (.succ l)), Usage.zeros ctx.lvl)
  | .delim v P a b c h D => do
    let (dty, uD) ← infer ctx D
    let .desc l I := whnf dty | throw (.typeMismatch "a description" (ctx.showVal dty))
    let w := QuantitySyntax.explicitDefault
    let _ ← check ctx P (delimMotiveTy l v I w)
    let vP := ctx.eval P
    let (ta, tb, tc, th) := delimMethodTys ctx.globals l I vP w
    let ua ← check ctx a ta
    let ub ← check ctx b tb
    let uc ← check ctx c tc
    let uh ← check ctx h th
    pure (vApp ctx.globals vP (ctx.eval D), (← methodUsage ctx (ua + ub + uc + uh)) + uD)
  | .mu l I D i s _ | .nu l I D i s _ => do
    let _ ← check { ctx with erased := true } s .size
    let lI ← checkType ctx I
    unless lI.equiv (.succ l) do throw (.other "an index type must be in the data type's universe")
    let vI := ctx.eval I
    let _ ← check ctx D (.desc l vI)
    let _ ← check ctx i vI
    pure (.sort (.succ l), Usage.zeros ctx.lvl)
  | .ind l I D v P m i x => do
    let _ ← checkType ctx I
    let vI := ctx.eval I
    let _ ← check ctx D (.desc l vI)
    let vD := ctx.eval D
    let w := QuantitySyntax.explicitDefault
    let _ ← check ctx P (indMotiveTy ctx.globals l v vI vD w)
    let vP := ctx.eval P
    let um ← check ctx m (indMethodTy ctx.globals l v vI vD vP w)
    let _ ← check ctx i vI
    let vi := ctx.eval i
    let ux ← check ctx x (.mu l vI vD vi .szInf none)
    pure (vApp ctx.globals (vApp ctx.globals vP vi) (ctx.eval x), (← methodUsage ctx um) + ux)
  | .out x => do
    let (ty, u) ← infer ctx x
    let .nu l I D i s _ := whnf ty | throw (.typeMismatch "a coinductive type" (ctx.showVal ty))
    let some s' := sizePred? s
      | throw (.other s!"only a value of size ↑s or ∞ can be observed, not {ctx.showVal s}")
    pure (vInterp ctx.globals l I D (nuFamilyAt l I D s') i, u)
  | .sfix l I D v P f s i x => do
    let _ ← checkType ctx I
    let vI := ctx.eval I
    let _ ← check ctx D (.desc l vI)
    let vD := ctx.eval D
    let w := QuantitySyntax.explicitDefault
    let _ ← check ctx P (indMotiveTy ctx.globals l v vI vD w)
    let vP := ctx.eval P
    let uf ← check ctx f (sfixFunTy ctx.globals l vI vD vP w)
    let _ ← check { ctx with erased := true } s .size
    let _ ← check ctx i vI
    let ux ← check ctx x (.mu l vI vD (ctx.eval i) (ctx.eval s) none)
    pure (vApp ctx.globals (vApp ctx.globals vP (ctx.eval i)) (ctx.eval x), (← methodUsage ctx uf) + ux)
  | .scofix l I D A f s i a => do
    let _ ← checkType ctx I
    let vI := ctx.eval I
    let _ ← check ctx D (.desc l vI)
    let vD := ctx.eval D
    let w := QuantitySyntax.explicitDefault
    let _ ← check ctx A (coitStateTy l vI w)
    let vA := ctx.eval A
    let uf ← check ctx f (scofixFunTy ctx.globals l vI vD vA w)
    let _ ← check { ctx with erased := true } s .size
    let _ ← check ctx i vI
    let ua ← check ctx a (vApp ctx.globals vA (ctx.eval i))
    pure (.nu l vI vD (ctx.eval i) (ctx.eval s) none, (← methodUsage ctx uf) + ua)
  | .scase l I D v P m s i x => do
    let _ ← checkType ctx I
    let vI := ctx.eval I
    let _ ← check ctx D (.desc l vI)
    let vD := ctx.eval D
    let w := QuantitySyntax.explicitDefault
    let _ ← check ctx P (indMotiveTy ctx.globals l v vI vD w)
    let vP := ctx.eval P
    let _ ← check { ctx with erased := true } s .size
    let vs := ctx.eval s
    let um ← check ctx m (scaseMethodTy ctx.globals l vI vD vP vs w)
    let _ ← check ctx i vI
    let ux ← check ctx x (.mu l vI vD (ctx.eval i) vs none)
    pure (vApp ctx.globals (vApp ctx.globals vP (ctx.eval i)) (ctx.eval x), um + ux)
  | .cocon _ => throw (.cannotInfer (ctx.showTerm t))
  | .coit l I D S st i s => do
    let _ ← checkType ctx I
    let vI := ctx.eval I
    let _ ← check ctx D (.desc l vI)
    let vD := ctx.eval D
    let w := QuantitySyntax.explicitDefault
    let _ ← check ctx S (coitStateTy l vI w)
    let vS := ctx.eval S
    let ust ← check ctx st (coitStepTy ctx.globals l vI vD vS w)
    let _ ← check ctx i vI
    let vi := ctx.eval i
    let us ← check ctx s (vApp ctx.globals vS vi)
    pure (.nu l vI vD vi .szInf none, (← methodUsage ctx ust) + us)
  | .dret _ | .darg .. | .drec .. | .dhrec .. | .con _ => throw (.cannotInfer (ctx.showTerm t))
  --|ex
  --| | .app f a => sorry
  --| | .letE x q tty val body => sorry
  --| | .ann tm tty => sorry
  --| -- Exercise 4.7b
  --| | .sigma x q a b s => sorry
  --| | .fst t => sorry
  --| | .snd t => sorry
  --| | .split q s z m x y b => sorry
  --| | .unit l => sorry
  --| | .empty l => sorry
  --| | .absurd m t => sorry
  --| | .pair .. | .tt => throw (.cannotInfer (ctx.showTerm t))
  --| -- Exercise 4.14
  --| | .eq A a b => sorry
  --| | .eqTy A B => sorry
  --| | .refl A a => sorry
  --| | .reflTy X => sorry
  --| | .cast A B e t => sorry
  --| | .transp A a P p b e => sorry
  --| | .qty => pure (.sort 1, Usage.zeros ctx.lvl)
  --| | .qlit _ => pure (.qty, Usage.zeros ctx.lvl)
  --| | .size => pure (.sort 1, Usage.zeros ctx.lvl)
  --| | .sizeLt s => do let _ ← check { ctx with erased := true } s .size; pure (.sort 1, Usage.zeros ctx.lvl)
  --| | .szInf => pure (.size, Usage.zeros ctx.lvl)
  --| | .szSuc s => do let _ ← check { ctx with erased := true } s .size; pure (.size, Usage.zeros ctx.lvl)
  --| -- Exercise 4.20: the data rules (see the module docstring)
  --| | .enum _ => sorry
  --| | .tag ls i => sorry
  --| | .ecase z m s bs => sorry
  --| | .desc l I => sorry
  --| | .delim v P a b c h D => sorry
  --| | .mu l I D i _ _ | .nu l I D i _ _ => sorry
  --| | .ind l I D v P m i x => sorry
  --| | .out x => sorry
  --| | .coit l I D S st i s => sorry
  --| -- Exercise 4.23: the sized rules
  --| | .sfix l I D v P f s i x => sorry
  --| | .scofix l I D A f s i a => sorry
  --| | .scase l I D v P m s i x => sorry
  --| | .cocon _ => throw (.cannotInfer (ctx.showTerm t))
  --| | .dret _ | .darg .. | .drec .. | .dhrec .. | .con _ => throw (.cannotInfer (ctx.showTerm t))
  --sol>

/-- A binder's quantity annotation: a term of type `Qty` (its usage is discarded, as
for types), returned as a polynomial. -/
partial def checkQty (ctx : Ctx R) (q : Term R) : TCM (QPoly R) := do
  let _ ← check ctx q .qty
  qtyPoly ctx (ctx.eval q)

/-- `Γ ⊢ A type@i`: infer `A`, require it to be a `sort`, return the level.
The usage is discarded: type positions are erased. -/
partial def checkType (ctx : Ctx R) (a : Term R) : TCM Level := do
  let (ty, _) ← infer { ctx with erased := true } a
  match whnf ty with
  | .sort l => pure l
  | _ => throw (.notAType (ctx.showTerm a) (ctx.showVal ty))

end

/-- (D1 experiment, `predicativeProp`) Check a declaration's type, but not the
predicativity of its outer `Π`s: a theorem quantifying over types is fine in a predicative
`Prop` too (in a bigger `Prop` or in `Type`; the theorem itself is never used as a proof
of a proposition at level 0). -/
partial def declTypeSpine (ctx : Ctx R) : Term R → TCM Unit
  | .pi x _ q dom cod _ => do
    let q ← checkQty ctx q
    let _ ← checkType ctx dom
    declTypeSpine (ctx.bind x q (ctx.eval dom)) cod
  | t => do let _ ← checkType ctx t

/-- The checks every declaration's header gets: a new name, its level parameters, and
its type is a type. -/
def checkHeader (g : Globals R) (d : Decl R) : TCM Unit := do
  if g.contains d.name then throw (.duplicateDecl d.name)
  unless d.levelParams.eraseDups.length == d.levelParams.length do
    throw (.other s!"duplicate universe level parameter in {d.name}")
  let used := d.type.levelParamsUsed ++ (d.value.map Term.levelParamsUsed).getD [] ++
    (d.witness.map Term.levelParamsUsed).getD []
  if let some u := used.find? (!d.levelParams.contains ·) then
    throw (.other s!"unknown universe level parameter {u} in {d.name}")
  let ctx : Ctx R := { globals := g }
  if g.predicativeProp then declTypeSpine ctx d.type
  else discard <| checkType ctx d.type

/-- A definition's **implementation for the compiler** (`Decl.impl`): the term compiled
code runs instead of the value. It may call the definition itself (a structurally
recursive definition's equations with direct recursion), so it is checked against the
declared type in `g`, which already has the definition. The kernel never unfolds it, so it
proves nothing; it is checked because erasure reads it (its types, the sorts noted on its
`Π`s and `Σ`s, its quantities) as it reads a checked term. That it computes what the
value computes is *not* checked. -/
def checkImpl (g : Globals R) (d : Decl R) (impl : Term R) : TCM Unit := do
  if let some u := impl.levelParamsUsed.find? (!d.levelParams.contains ·) then
    throw (.other s!"unknown universe level parameter {u} in the implementation of {d.name}")
  let ctx : Ctx R := { globals := g }
  match check ctx impl (ctx.eval d.type) with
  | .ok _ => pure ()
  | .error e => throw (.other s!"the implementation of {d.name} (the term compiled code runs) does not check: {e}")

/-- Type check a declaration and add it to the global environment. Its implementation
for the compiler, if it has one, is checked too (`checkImpl`): no term reaches erasure
unchecked. -/
def addDecl (g : Globals R) (d : Decl R) : TCM (Globals R) := do
  if d.witness.isSome then throw (.other s!"{d.name}: only a partial definition has a witness")
  checkHeader g d
  let ctx : Ctx R := { globals := g }
  if let some v := d.value then
    -- usage is the empty vector: a closed term has no locals to misuse
    let _ ← check ctx v (ctx.eval d.type)
  let g' := g.insert d
  if let some impl := d.impl then checkImpl g' d impl
  pure g'

/-- Give the declaration `name` another implementation for the compiler
(`attribute [implemented_by g] f` sets the constant `g`), checked like a definition's own
(`checkImpl`): at `name`'s type. The kernel's view of `name` does not change. -/
def setImpl (g : Globals R) (name : Name) (impl : Term R) : TCM (Globals R) := do
  let some d := g.find? name | throw (.other s!"unknown declaration {name}")
  checkImpl g d impl
  pure (g.insert { d with impl := some impl })

/-- A partial definition's signature (stage 13): `f : T` is opaque to the kernel, like an
axiom, so the bodies of its group can call it. It must come with a **witness** `w : T`,
which the kernel checks here: then `f` proves nothing `w` doesn't, whatever the bodies do.
The witness is checked erased (quantity 0): it is only evidence that `T` is inhabited,
never run, so it may ignore a linear argument. -/
def addPartialDecl (g : Globals R) (d : Decl R) : TCM (Globals R) := do
  let some w := d.witness
    | throw (.other s!"partial definition {d.name} needs a witness, a term of its type")
  if d.value.isSome then throw (.other s!"partial definition {d.name} can't have a value")
  checkHeader g d
  let ctx : Ctx R := { globals := g, erased := true }
  let _ ← check ctx w (ctx.eval d.type)
  pure (g.insert d)

/-- A partial definition's implementation, which may call `f` and the other definitions
of its group: checked against the type and kept for the compiler. Only a partial
definition (one with a checked witness) takes one. -/
def addPartialImpl (g : Globals R) (name : Name) (impl : Term R) : TCM (Globals R) := do
  let some d := g.find? name | throw (.other s!"unknown declaration {name}")
  unless d.witness.isSome && d.value.isNone do
    throw (.other s!"{name} is not a partial definition")
  let ctx : Ctx R := { globals := g }
  let _ ← check ctx impl (ctx.eval d.type)
  pure (g.insert { d with impl := some impl })

/-- The axioms the declaration `n` depends on, through the constants in its type, its
value and (for a partial definition) its witness: the declarations without a value or a
witness (`axiom`s, foreign functions), and the `builtin` registrations made outside the
toolchain's library (`Globals.assumed`), shown as `builtin key := name`. A numeral
depends on the declarations registered as `nat`, `nat.zero` and `nat.succ`. A partial
definition's implementation is not looked at: it is only run, never unfolded in a proof.

Also listed, marked `native`: the **native implementations** the declaration's compiled
code runs, wherever they are registered (the library's too). `native f := g` is
`attribute [implemented_by g] f`, and `native T := mk/get` a native representation of the
type `T` (`attribute [implemented_by mk get] T.mk`, a `repr:` registration). The kernel
never runs them, so they prove nothing: they are trusted to agree with the definitions. -/
partial def Globals.axiomsOf (g : Globals R) (n : Name) : List String := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut todo := [n]
  let mut out : Array String := #[]
  let mut reprs : List Name := []
  let numeral := ["nat", "nat.zero", "nat.succ"].filterMap (List.lookup · g.builtins)
  while true do
    match todo with
    | [] => break
    | c :: rest =>
      todo := rest
      if seen.contains c then continue
      seen := seen.insert c
      let some d := g.find? c | continue
      if d.value.isNone && d.witness.isNone then out := out.push c
      for (k, m) in g.assumed.reverse do
        if m == c then out := out.push s!"builtin {k} := {c}"
      if let some i := d.nativeImpl? then out := out.push s!"native {c} := {i}"
      -- (a `repr:T:mk:get:…` registration is on `T`'s constructor: it concerns whatever
      -- mentions the type or the constructor)
      for (k, m) in g.builtins.reverse do
        if let "repr" :: T :: mkImpl :: getImpl :: _ := k.splitOn ":" then
          if (c == m || c == T) && !reprs.contains T then
            reprs := T :: reprs
            out := out.push s!"native {T} := {mkImpl}/{getImpl}"
      let (cs, lit) := ([d.type] ++ d.value.toList ++ d.witness.toList).foldl
        (fun (acc : List Name × Bool) t => (consts t acc.1, acc.2 || hasNatLit t)) ([], false)
      -- a registered operation or constructor makes numerals without a literal in the
      -- term (`Nat.zero` is `0`, `Nat.pow 0 0` is `1`), and numerals unfold through the
      -- registered `nat.zero` and `nat.succ`: it depends on them like a literal does
      let lit := lit || g.builtins.any fun (k, m) => m == c && k.startsWith "nat."
      todo := cs ++ (if lit then numeral else []) ++ todo
  return out.toList
where
  consts (t : Term R) (acc : List Name) : List Name :=
    match t with
    | .const c _ => c :: acc
    | t => (go t |>.run acc).2
  go (t : Term R) : StateM (List Name) Unit :=
    t.forChildren (fun _ => pure ()) fun _ c => match c with
      | .const n _ => modify (n :: ·)
      | c => go c
  hasNatLit (t : Term R) : Bool := match t with
    | .natLit _ => true
    | t => (litGo t |>.run false).2
  litGo (t : Term R) : StateM Bool Unit :=
    t.forChildren (fun _ => pure ()) fun _ c => match c with
      | .natLit _ => set true
      | c => litGo c

/-- Check a list of declarations in order. -/
def addDecls (g : Globals R) (ds : List (Decl R)) : TCM (Globals R) :=
  ds.foldlM addDecl g

end Wiz
