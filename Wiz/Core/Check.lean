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
    Γ ⊢ coit S step i s ⇒ ν D i ⊣ ω·U_step + U_s

A method may run once per node, so its usage is scaled by ω (the rig's default
quantity). Branches of `ecase` are alternatives, so a case uses the *join* of its
branches' usages: with `{0, 1, ω}` a linear variable must be used the same way in
every branch, and an ω variable may be used differently.

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
  | u => sorry

mutual

/-- **Exercise 1.6.** Check `t` against the type `ty`. Implement the `lam` and `letE`
rules here and fall back to `infer` + `convTy` for everything else. (Stage 4f
replaces `convTy` with `subTy`, sized subtyping: the inferred type must be a subtype
of the expected one.)

**Exercise 4.7a** (stage 4b): the `pair` and `tt` rules. -/
partial def check (ctx : Ctx R) (t : Term R) (ty : VTy R) : TCM (Usage R) :=
  match t, whnf ty with
  | .lam x body, .pi _ _ q dom cod => sorry
  | .letE x q tty val body, _ => sorry
  -- Exercise 4.7a
  | .pair a b, .sigma _ q A B => sorry
  | .tt, .unit _ => sorry
  -- Exercise 4.20
  | .dret i, .desc _ I => sorry
  | .darg q S D, .desc l I => sorry
  | .drec q j D, .desc l I => sorry
  | .dhrec q H j D, .desc l I => sorry
  | .con x, .mu l I D i _ _ => sorry
  | _, _ => sorry

/-- **Exercise 1.7.** Infer the type of `t`. See the rules in the module docstring.
`checkType` (below) handles the "`A type@i`" premises.

**Exercise 4.14** (stage 4c): `eq`, `eqTy`, `refl`, `reflTy`, `cast`, `transp`.

**Exercise 4.7b** (stage 4b): `sigma`, `fst`, `snd`, `split`, `unit`, `empty`,
`absurd`. `pair` and `tt` can only be checked. -/
partial def infer (ctx : Ctx R) (t : Term R) : TCM (VTy R × Usage R) :=
  match t with
  | .mvar m => throw (.other s!"the kernel does not accept metavariables (?m{m})")
  | .natLit _ => match ctx.globals.builtins.lookup "nat" with
    | some N => pure (ctx.eval (.const N []), Usage.zeros ctx.lvl)
    | none => throw (.other "numerals need `builtin nat := …`")
  | .natOp .. => throw (.cannotInfer (ctx.showTerm t))
  | .var ix => sorry
  | .const n us => sorry
  | .sort l => sorry
  | .pi x _ q dom cod => sorry
  | .lam .. => throw (.cannotInfer (ctx.showTerm t))
  | .app f a => sorry
  | .letE x q tty val body => sorry
  | .ann tm tty => sorry
  -- Exercise 4.7b
  | .sigma x q a b => sorry
  | .fst t => sorry
  | .snd t => sorry
  | .split q s z m x y b => sorry
  | .unit l => sorry
  | .empty l => sorry
  | .absurd m t => sorry
  | .pair .. | .tt => throw (.cannotInfer (ctx.showTerm t))
  -- Exercise 4.14
  | .eq A a b => sorry
  | .eqTy A B => sorry
  | .refl A a => sorry
  | .reflTy X => sorry
  | .cast A B e t => sorry
  | .transp A a P p b e => sorry
  | .qty => pure (.sort 1, Usage.zeros ctx.lvl)
  | .qlit _ => pure (.qty, Usage.zeros ctx.lvl)
  | .size => pure (.sort 1, Usage.zeros ctx.lvl)
  | .sizeLt s => do let _ ← check { ctx with erased := true } s .size; pure (.sort 1, Usage.zeros ctx.lvl)
  | .szInf => pure (.size, Usage.zeros ctx.lvl)
  | .szSuc s => do let _ ← check { ctx with erased := true } s .size; pure (.size, Usage.zeros ctx.lvl)
  -- Exercise 4.20: the data rules (see the module docstring)
  | .enum _ => sorry
  | .tag ls i => sorry
  | .ecase z m s bs => sorry
  | .desc l I => sorry
  | .delim v P a b c h D => sorry
  | .mu l I D i _ _ | .nu l I D i _ _ => sorry
  | .ind l I D v P m i x => sorry
  | .out x => sorry
  | .coit l I D S st i s => sorry
  -- Exercise 4.23: the sized rules
  | .sfix l I D v P f s i x => sorry
  | .scofix l I D A f s i a => sorry
  | .scase l I D v P m s i x => sorry
  | .cocon _ => throw (.cannotInfer (ctx.showTerm t))
  | .dret _ | .darg .. | .drec .. | .dhrec .. | .con _ => throw (.cannotInfer (ctx.showTerm t))

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

/-- A partial definition (stage 13): `f` itself is opaque to the kernel, an axiom (so
its type must be inhabited, which the elaborator checks), and its implementation, which
may call `f` and the other definitions of its group, is checked against the type and
kept for the compiler. -/
def addPartialImpl (g : Globals R) (name : Name) (impl : Term R) : TCM (Globals R) := do
  let some d := g.find? name | throw (.other s!"unknown declaration {name}")
  let ctx : Ctx R := { globals := g }
  let _ ← check ctx impl (ctx.eval d.type)
  pure (g.insert { d with impl := some impl })

/-- Check a list of declarations in order. -/
def addDecls (g : Globals R) (ds : List (Decl R)) : TCM (Globals R) :=
  ds.foldlM addDecl g

end Wiz
