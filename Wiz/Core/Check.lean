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

    Γ ⊢ t ⇒ (q x : A) × B ⊣ U     le 1 q
    ──────────────────────────────── fst       (an erased field can't be projected)
    Γ ⊢ t.1 ⇒ A ⊣ U

    Γ ⊢ t ⇒ (q x : A) × B ⊣ U
    ──────────────────────────────── snd
    Γ ⊢ t.2 ⇒ B[t.1/x] ⊣ U

    Γ ⊢ s ⇒ (p x : A) × B ⊣ U₁     Γ, z : (p x : A) × B ⊢ M type
    Γ, x :(q·p) A, y :q B ⊢ b ⇐ M[(x, y)/z] ⊣ (u_y :: u_x :: U₂)
    le u_y q     le u_x (q·p)
    ──────────────────────────────── split
    Γ ⊢ let q (x, y) := s; b ⇒ M[s/z] ⊣ q·U₁ + U₂

    Γ ⊢ Unit_l ⇒ Sort l      Γ ⊢ () ⇐ Unit_l      Γ ⊢ Empty_l ⇒ Sort l

    Γ ⊢ M type     Γ ⊢ t ⇒ Empty_l ⊣ U
    ──────────────────────────────── absurd
    Γ ⊢ absurd M t ⇒ M ⊣ U

## Observational equality (stage 4c)

    Γ ⊢ A type@l   l ≠ 0 (A is not a proposition)   Γ ⊢ a, b ⇐ A
    ──────────────────────────────── eq            (a proposition)
    Γ ⊢ a = b ⇒ Prop ⊣ 0ₙ

    Γ ⊢ A type@l    Γ ⊢ B type@l
    ──────────────────────────────── eqTy
    Γ ⊢ A = B ⇒ Prop ⊣ 0ₙ

    Γ ⊢ refl a ⇒ (a = a) ⊣ 0ₙ          Γ ⊢ refl X ⇒ (X = X) ⊣ 0ₙ

    Γ ⊢ A, B type@l    Γ ⊢ e ⇐ (A = B)    Γ ⊢ t ⇐ A ⊣ U
    ──────────────────────────────── cast
    Γ ⊢ cast A B e t ⇒ B ⊣ U

    Γ ⊢ a, b ⇐ A    Γ ⊢ P ⇐ (b :0 A) → (_ :0 a = b) → Prop
    Γ ⊢ p ⇐ P a (refl a)    Γ ⊢ e ⇐ (a = b)
    ──────────────────────────────── transp
    Γ ⊢ transp A a P p b e ⇒ P b e ⊣ 0ₙ

Proofs carry no usage: they are erased, and conversion never looks at them.

`split` is how linear pairs are consumed: `fst p` and `snd p` each use `p`, so
using both on a linear pair uses it twice.

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
  qtys  : List R := []
  types : List (VTy R) := []
  /-- number of locals in scope = the next fresh de Bruijn level -/
  lvl   : Lvl := 0

namespace Ctx

variable [Zero R] [DecidableEq R]

/-- Go under a binder: the new variable is a fresh neutral. -/
def bind (ctx : Ctx R) (x : Name) (q : R) (ty : VTy R) : Ctx R :=
  { ctx with
    env := Val.var ctx.lvl :: ctx.env
    names := x :: ctx.names
    qtys := q :: ctx.qtys
    types := ty :: ctx.types
    lvl := ctx.lvl + 1 }

/-- Go under a `let`: the new variable has a known value. -/
def define (ctx : Ctx R) (x : Name) (q : R) (ty : VTy R) (val : Val R) : Ctx R :=
  { ctx with
    env := val :: ctx.env
    names := x :: ctx.names
    qtys := q :: ctx.qtys
    types := ty :: ctx.types
    lvl := ctx.lvl + 1 }

def eval (ctx : Ctx R) (t : Term R) : Val R := Wiz.eval ctx.globals ctx.env t

/-- The types of the locals indexed by level, as `conv` wants them. -/
def tys (ctx : Ctx R) : Array (VTy R) := ctx.types.reverse.toArray

variable [QuantitySyntax R] [DecidableEq R]

/-- Render a value for error messages. -/
def showVal (ctx : Ctx R) (v : Val R) : String :=
  (quote ctx.globals ctx.lvl v).pretty ctx.names

def showTerm (ctx : Ctx R) (t : Term R) : String := t.pretty ctx.names

end Ctx

variable [QRig R] [DecidableEq R] [ToString R] [QuantitySyntax R]

/-- **Exercise 1.5.** Leave the scope of a binder `x` declared at quantity `q`:
pop the binder's own usage off the head of the vector and check it is compatible
with `q` (using `QRig.le`), returning the rest. Throw `quantityMismatch` otherwise. -/
def popUsage (x : Name) (q : R) : Usage R → TCM (Usage R)
  --<sol
  | used :: rest =>
    if QRig.le used q then pure rest
    else throw (.quantityMismatch x (toString q) (toString used))
  | [] => throw (.other "internal error: usage vector underflow")
  --|ex
  --| | u => sorry
  --sol>

mutual

/-- **Exercise 1.6.** Check `t` against the type `ty`. Implement the `lam` and `letE`
rules here and fall back to `infer` + `convTy` for everything else.

**Exercise 4.7a** (stage 4b): the `pair` and `tt` rules. -/
partial def check (ctx : Ctx R) (t : Term R) (ty : VTy R) : TCM (Usage R) :=
  match t, ty with
  --<sol
  | .lam x body, .pi _ _ q dom cod => do
    let u ← check (ctx.bind x q dom) body (Closure.inst ctx.globals cod (Val.var ctx.lvl))
    popUsage x q u
  | .letE x q tty val body, _ => do
    let _ ← checkType ctx tty
    let vty := ctx.eval tty
    let uv ← check ctx val vty
    let ub ← check (ctx.define x q vty (ctx.eval val)) body ty
    let ub ← popUsage x q ub
    pure (q • uv + ub)
  | .pair a b, .sigma _ q A B => do
    let ua ← check ctx a A
    let ub ← check ctx b (Closure.inst ctx.globals B (ctx.eval a))
    pure (q • ua + ub)
  | .tt, .unit _ => pure (Usage.zeros ctx.lvl)
  | _, _ => do
    let (ty', u) ← infer ctx t
    unless convTy ctx.globals ctx.tys ty ty' do
      throw (.typeMismatch (ctx.showVal ty) (ctx.showVal ty'))
    pure u
  --|ex
  --| | .lam x body, .pi _ _ q dom cod => sorry
  --| | .letE x q tty val body, _ => sorry
  --| -- Exercise 4.7a
  --| | .pair a b, .sigma _ q A B => sorry
  --| | .tt, .unit _ => sorry
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
  --<sol
  | .var ix => pure (ctx.types[ix]!, Usage.single ctx.lvl ix)
  | .const n us => match ctx.globals.find? n with
    | some d => do
      unless d.levelParams.length == us.length do
        throw (TypeError.other s!"{n} expects {d.levelParams.length} universe levels, got {us.length}")
      pure (Wiz.eval ctx.globals [] (d.type.instLevels d.levelParams us), Usage.zeros ctx.lvl)
    | none => throw (.unboundGlobal n)
  | .sort l => pure (.sort (.succ l), Usage.zeros ctx.lvl)
  | .pi x _ q dom cod => do
    let i ← checkType ctx dom
    let j ← checkType (ctx.bind x q (ctx.eval dom)) cod
    pure (.sort (.imax i j), Usage.zeros ctx.lvl)
  --|ex
  --| | .var ix => sorry
  --| | .const n us => sorry
  --| | .sort l => sorry
  --| | .pi x _ q dom cod => sorry
  --sol>
  | .lam .. => throw (.cannotInfer (ctx.showTerm t))
  --<sol
  | .app f a => do
    let (fty, uf) ← infer ctx f
    match fty with
    | .pi _ _ q dom cod =>
      let ua ← check ctx a dom
      pure (Closure.inst ctx.globals cod (ctx.eval a), uf + q • ua)
    | _ => throw (.notAFunction (ctx.showTerm f) (ctx.showVal fty))
  | .letE x q tty val body => do
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
  | .sigma x q a b => do
    let i ← checkType ctx a
    let j ← checkType (ctx.bind x q (ctx.eval a)) b
    pure (.sort (.max i j), Usage.zeros ctx.lvl)
  | .fst t => do
    let (ty, u) ← infer ctx t
    match ty with
    | .sigma x q A _ =>
      unless QRig.le 1 q do
        throw (.other s!"cannot project the field {x}, which has quantity {q}; use let (x, y) := ... instead")
      pure (A, u)
    | _ => throw (.other s!"not a pair: {ctx.showTerm t}\n  has type: {ctx.showVal ty}")
  | .snd t => do
    let (ty, u) ← infer ctx t
    match ty with
    | .sigma _ _ _ B => pure (Closure.inst ctx.globals B (vFst (ctx.eval t)), u)
    | _ => throw (.other s!"not a pair: {ctx.showTerm t}\n  has type: {ctx.showVal ty}")
  | .split q s z m x y b => do
    let (sty, us) ← infer ctx s
    match sty with
    | .sigma _ p A B =>
      let _ ← checkType (ctx.bind z 0 sty) m
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
    let (ty, u) ← infer ctx t
    match ty with
    | .empty _ => pure (ctx.eval m, u)
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
    let _ ← check ctx e (vEqType ctx.globals vA vB)
    let u ← check ctx t vA
    pure (vB, u)
  | .transp A a P p b e => do
    let _ ← checkType ctx A
    let vA := ctx.eval A
    let _ ← check ctx a vA
    let va := ctx.eval a
    -- (b :0 A) → (_ :0 a = b) → Prop, with env [a, A]
    let motiveTy : Val R := .pi "b" .default 0 vA
      (.mk [va, vA] (.pi "_" .default 0 (.eq (.var 2) (.var 1) (.var 0)) (.sort 0)))
    let _ ← check ctx P motiveTy
    let vP := ctx.eval P
    let g := ctx.globals
    let _ ← check ctx p (vApp g (vApp g vP va) (.neutral (.refl vA va) #[]))
    let _ ← check ctx b vA
    let vb := ctx.eval b
    let _ ← check ctx e (vEq g vA va vb)
    pure (vApp g (vApp g vP vb) (ctx.eval e), Usage.zeros ctx.lvl)
  --|ex
  --| | .app f a => sorry
  --| | .letE x q tty val body => sorry
  --| | .ann tm tty => sorry
  --| -- Exercise 4.7b
  --| | .sigma x q a b => sorry
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
  --sol>

/-- `Γ ⊢ A type@i`: infer `A`, require it to be a `sort`, return the level.
The usage is discarded: type positions are erased. -/
partial def checkType (ctx : Ctx R) (a : Term R) : TCM Level := do
  let (ty, _) ← infer ctx a
  match ty with
  | .sort l => pure l
  | _ => throw (.notAType (ctx.showTerm a) (ctx.showVal ty))

end

/-- Type check a declaration and add it to the global environment. -/
def addDecl (g : Globals R) (d : Decl R) : TCM (Globals R) := do
  if g.contains d.name then throw (.duplicateDecl d.name)
  unless d.levelParams.eraseDups.length == d.levelParams.length do
    throw (.other s!"duplicate universe level parameter in {d.name}")
  let used := d.type.levelParamsUsed ++ (d.value.map Term.levelParamsUsed).getD []
  if let some u := used.find? (!d.levelParams.contains ·) then
    throw (.other s!"unknown universe level parameter {u} in {d.name}")
  let ctx : Ctx R := { globals := g }
  let _ ← checkType ctx d.type
  if let some v := d.value then
    -- usage is the empty vector: a closed term has no locals to misuse
    let _ ← check ctx v (ctx.eval d.type)
  pure (g.insert d)

/-- Check a list of declarations in order. -/
def addDecls (g : Globals R) (ds : List (Decl R)) : TCM (Globals R) :=
  ds.foldlM addDecl g

end Wiz
