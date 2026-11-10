import Std.Data.HashMap
import Wiz.Core.Level

/-!
# Core terms

The kernel language. Variables are **de Bruijn indices**: `var 0` is the nearest
enclosing binder, `var 1` the next one out, and so on. This makes α-equivalence
syntactic equality and keeps substitution out of the kernel entirely (we never
substitute; see `Wiz.Core.Eval` for normalisation by evaluation).

Names on binders (`x`) are kept only for pretty-printing.

The quantity `q` on `pi` and `letE` is the QTT annotation. It is itself a term of
type `Qty`: a literal `qlit r` (`r : R`), or (stage 4d) a quantity variable. Lambdas carry no
quantity or domain: they are only ever *checked* against a `pi`, which supplies both.

`BinderInfo` on `pi` says whether the argument is explicit or implicit. The kernel
ignores it; the elaborator uses it to insert implicit arguments.

`mvar` is a metavariable, a hole the elaborator (stage 3) is still solving. The kernel
evaluates it to a stuck neutral and rejects it in the type checker. Elaborated terms
have all their metavariables replaced before they reach the kernel.

Universe levels are described in `Wiz.Core.Level`.

Stage 4 added Σ-types, observational equality, descriptions with μ/ν data, and sizes.
-/

namespace Wiz

abbrev Name := String

inductive BinderInfo where
  | default
  | implicit
  /-- `[x : C A]`: filled by type class resolution (the kernel treats it as implicit) -/
  | instImplicit
  deriving Repr, BEq, DecidableEq, Inhabited

inductive Term (R : Type) where
  /-- de Bruijn index -/
  | var (ix : Nat)
  /-- a global declaration, with its universe level parameters instantiated -/
  | const (name : Name) (levels : List Level)
  /-- `Sort l` (`Prop` is `Sort 0`, `Type u` is `Sort (u+1)`). Non-cumulative:
  `Sort l : Sort (l+1)` only. -/
  | sort (level : Level)
  /-- `(q x : dom) → cod` (or `{q x : dom} → cod`), where `cod` lives under one extra
  binder. `s`, when given, is the sort of the whole type (`imax` of the parts'): type
  equality compares propositions by logical equivalence, other types by their parts,
  and needs to know which is which (the kernel checks `s`) -/
  | pi (x : Name) (bi : BinderInfo) (q : Term R) (dom cod : Term R) (s : Option Level)
  /-- `λ x. body`, where `body` lives under one extra binder -/
  | lam (x : Name) (body : Term R)
  | app (fn arg : Term R)
  /-- `let x :q ty := val; body`, where `body` lives under one extra binder -/
  | letE (x : Name) (q : Term R) (ty val body : Term R)
  /-- `(tm : ty)`, used to switch from checking to inference -/
  | ann (tm ty : Term R)
  /-- metavariable number `id` (elaborator only) -/
  | mvar (id : Nat)
  -- Stage 4: structural types. `sigma` binder names double as field names.
  /-- `(q x : A) × B`: the first component may be used `q` times; `s` as for `pi` -/
  | sigma (x : Name) (q : Term R) (fst snd : Term R) (s : Option Level)
  | pair (a b : Term R)
  | fst (t : Term R)
  | snd (t : Term R)
  /-- `let q (x, y) := scrut; body` with motive `fun z => motive` for the result type.
  `motive` is under one binder (`z`), `body` under two (`x`, then `y`). -/
  | split (q : Term R) (scrut : Term R) (z : Name) (motive : Term R) (x y : Name) (body : Term R)
  /-- the unit type in `Sort l`: `True` at level 0, `Unit` at level 1 -/
  | unit (level : Level)
  | tt
  /-- the empty type in `Sort l`: `False` at level 0, `Empty` at level 1 -/
  | empty (level : Level)
  /-- `absurd t : motive`, given `t : empty l` -/
  | absurd (motive t : Term R)
  -- Stage 4c: observational equality.
  /-- `a = b` at type `A : Type u`. A proposition that *computes* by `A`. -/
  | eq (A a b : Term R)
  /-- `A = B` for types (what `eq (Sort l) A B` computes to); no level needed -/
  | eqTy (A B : Term R)
  /-- `refl a : a = a` (`A` is the type of `a`) -/
  | refl (A a : Term R)
  /-- `refl X : X = X` for a type `X` -/
  | reflTy (X : Term R)
  /-- `cast A B e t : B` given `e : A = B` and `t : A`. Computes by `A` and `B`. -/
  | cast (A B e t : Term R)
  /-- `transp A a P p b e : P b e` given `P : (b : A) → a = b → Prop`, `p : P a (refl a)`
  and `e : a = b`. Transport into propositions; with `cast` it gives `J`. -/
  | transp (A a P p b e : Term R)
  -- Stage 4d: quantity polymorphism. Binder quantities are terms of type `Qty`.
  /-- the type of quantities -/
  | qty
  /-- a quantity literal -/
  | qlit (r : R)
  -- Stage 4d: data. Labels are metadata; conversion ignores them.
  /-- a finite enumeration of tags, `Enum [a, b, c]` -/
  | enum (labels : List Name)
  /-- the `i`-th tag of an enumeration -/
  | tag (labels : List Name) (i : Nat)
  /-- `ecase t [b₀, …]` with motive `fun z => motive` -/
  | ecase (z : Name) (motive : Term R) (scrut : Term R) (branches : List (Term R))
  /-- descriptions of indexed inductive types, `Desc.{l} I` -/
  | desc (l : Level) (I : Term R)
  | dret (i : Term R)
  /-- a non-recursive field of quantity `q` and type `S`; `D : S → Desc I` -/
  | darg (q S D : Term R)
  /-- a recursive field of quantity `q` at index `j` -/
  | drec (q j D : Term R)
  /-- an infinitary recursive field `(h : H) → μ D (j h)` of quantity `q`, for
  `j : H → I` (a "higher" recursive field: one subtree per `h`) -/
  | dhrec (q H j D : Term R)
  /-- the eliminator of descriptions, into `P : Desc I → Sort v` -/
  | delim (v : Level) (P mret marg mrec mhrec D : Term R)
  /-- the least fixed point `μ D i`. `hint` is display metadata: the nominal form
  (`Vec A n`) to print instead; conversion ignores it. -/
  | mu (l : Level) (I D i : Term R) (sz : Term R) (hint : Option (Name × List Level × List (Term R)))
  | con (x : Term R)
  /-- induction: `ind P m i x : P i x` for `x : μ D i` -/
  | ind (l : Level) (I D : Term R) (v : Level) (P m i x : Term R)
  /-- the greatest fixed point `ν D i` -/
  | nu (l : Level) (I D i : Term R) (sz : Term R) (hint : Option (Name × List Level × List (Term R)))
  /-- observation: `out x : ⟦D⟧ (ν D) i` -/
  | out (x : Term R)
  -- Sized types: sizes are erased bounds on the depth of μ/ν values.
  /-- the type of sizes -/
  | size
  /-- the infinite size: `μ^∞` is the ordinary inductive type -/
  | szInf
  /-- the successor size `↑s` -/
  | szSuc (s : Term R)
  /-- `Size< s`: the sizes below `s` -/
  | sizeLt (s : Term R)
  /-- sized recursion: `sfix P f s i x : P i x` for `x : μ^s D i`, where
  `f : (s : Size) → ((j : Size< s) → (i : I) → (y : μ^j D i) → P i y) → (i : I) → (x : μ^s D i) → P i x`.
  It unfolds only on a constructor. -/
  | sfix (l : Level) (I D : Term R) (v : Level) (P f s i x : Term R)
  /-- sized case analysis: `scase P m s i x : P i x` for `x : μ^s D i`, where
  `m : (j : Size< s) → (i : I) → (xs : ⟦D⟧ (μ^j D) i) → P i (con xs)`: the fields have
  some size below `s` -/
  | scase (l : Level) (I D : Term R) (v : Level) (P m s i x : Term R)
  /-- a ν constructor: `cocon xs : ν^{↑s} D i` for `xs : ⟦D⟧ (ν^s D) i` -/
  | cocon (x : Term R)
  /-- sized corecursion: `scofix A f s i a : ν^s D i`, where
  `f : (s : Size) → ((i : I) → A i → ν^s D i) → (i : I) → A i → ν^{↑s} D i`.
  It unfolds only when observed with `out`. -/
  | scofix (l : Level) (I D A f s i a : Term R)
  /-- coiteration: unfold a state `s : S i` with `step` -/
  | coit (l : Level) (I D S step i s : Term R)
  /-- a numeral of the `builtin nat` type. It means `succ (… (succ zero))`, and
  unfolds one step at a time when something looks inside it. -/
  | natLit (n : Nat)
  /-- only made by `eval`, inside the closure for a registered operation such as
  `nat.add`: compute natively when the arguments (variables) are literals, else apply
  the definition -/
  | natOp (op : Name) (args : Array (Term R))
  -- Q4: lifting a type to a bigger universe
  /-- `ULift.{l} A : Sort l` for `A : Sort k` with `k ≤ l`: a copy of `A` one or more
  universes up. Description fields must live exactly in `Sort (l+1)`, so the elaborator
  wraps smaller ones (proof fields, and fields of a level-polymorphic type whose level
  is a `max`). A lifted proposition (`l ≠ 0`) is not a proposition: its inhabitants are
  boxed proofs, all equal by η. Erased at run time. -/
  | ulift (l : Level) (A : Term R)
  /-- `up a : ULift A` for `a : A` (checked only) -/
  | up (a : Term R)
  /-- `down t : A` for `t : ULift A`; `down (up a) ↦ a`, and `t ≡ up (down t)` (η) -/
  | down (t : Term R)
  deriving Repr, Inhabited, BEq

/-- A global declaration. `value = none` is an axiom/postulate. -/
structure Decl (R : Type) where
  name  : Name
  /-- universe level parameters, e.g. `[u]` for `def id.{u} ...` -/
  levelParams : List Name := []
  type  : Term R
  value : Option (Term R)
  /-- unfold eagerly instead of gluing (constructors, so values look like constructor
  applications) -/
  inline : Bool := false
  /-- an implementation for the compiler, not checked by the kernel: a structurally
  recursive definition, with direct recursion instead of the recursor -/
  impl : Option (Term R) := none
  deriving Repr, Inhabited

namespace Term

variable {R : Type}

/-- Rebuild a term with `fl` applied to its levels and `f k c` to each immediate
child `c`, where `k` is the number of binders the child is under. Generic traversals
(level instantiation, zonking, free-variable checks) are written with this so they
don't need a case per constructor. -/
@[specialize] def mapChildrenM {m : Type → Type} [Monad m] (fl : Level → m Level)
    (f : Nat → Term R → m (Term R)) : Term R → m (Term R)
  | .pi x bi q a b s => return .pi x bi (← f 0 q) (← f 0 a) (← f 1 b) (← s.mapM fl)
  | .lam x b => return .lam x (← f 1 b)
  | .app a b => return .app (← f 0 a) (← f 0 b)
  | .letE x q t v b => return .letE x (← f 0 q) (← f 0 t) (← f 0 v) (← f 1 b)
  | .ann a b => return .ann (← f 0 a) (← f 0 b)
  | .sort l => return .sort (← fl l)
  | .const n ls => return .const n (← ls.mapM fl)
  | .sigma x q a b s => return .sigma x (← f 0 q) (← f 0 a) (← f 1 b) (← s.mapM fl)
  | .pair a b => return .pair (← f 0 a) (← f 0 b)
  | .fst t => return .fst (← f 0 t)
  | .snd t => return .snd (← f 0 t)
  | .split q s z m x y b => return .split (← f 0 q) (← f 0 s) z (← f 1 m) x y (← f 2 b)
  | .unit l => return .unit (← fl l)
  | .empty l => return .empty (← fl l)
  | .absurd a b => return .absurd (← f 0 a) (← f 0 b)
  | .eq A a b => return .eq (← f 0 A) (← f 0 a) (← f 0 b)
  | .eqTy A B => return .eqTy (← f 0 A) (← f 0 B)
  | .refl A a => return .refl (← f 0 A) (← f 0 a)
  | .reflTy X => return .reflTy (← f 0 X)
  | .cast A B e t => return .cast (← f 0 A) (← f 0 B) (← f 0 e) (← f 0 t)
  | .transp A a P p b e => return .transp (← f 0 A) (← f 0 a) (← f 0 P) (← f 0 p) (← f 0 b) (← f 0 e)
  | .ecase z mo s bs => return .ecase z (← f 1 mo) (← f 0 s) (← bs.mapM (f 0))
  | .desc l I => return .desc (← fl l) (← f 0 I)
  | .dret i => return .dret (← f 0 i)
  | .darg q S D => return .darg (← f 0 q) (← f 0 S) (← f 0 D)
  | .drec q j D => return .drec (← f 0 q) (← f 0 j) (← f 0 D)
  | .dhrec q H j D => return .dhrec (← f 0 q) (← f 0 H) (← f 0 j) (← f 0 D)
  | .delim v P a b c h D => return .delim (← fl v) (← f 0 P) (← f 0 a) (← f 0 b) (← f 0 c) (← f 0 h) (← f 0 D)
  | .mu l I D i s h => return .mu (← fl l) (← f 0 I) (← f 0 D) (← f 0 i) (← f 0 s) (← h.mapM (hintM fl f))
  | .con x => return .con (← f 0 x)
  | .ind l I D v P mt i x =>
    return .ind (← fl l) (← f 0 I) (← f 0 D) (← fl v) (← f 0 P) (← f 0 mt) (← f 0 i) (← f 0 x)
  | .nu l I D i s h => return .nu (← fl l) (← f 0 I) (← f 0 D) (← f 0 i) (← f 0 s) (← h.mapM (hintM fl f))
  | .out x => return .out (← f 0 x)
  | .szSuc s => return .szSuc (← f 0 s)
  | .sizeLt s => return .sizeLt (← f 0 s)
  | .sfix l I D v P g s i x =>
    return .sfix (← fl l) (← f 0 I) (← f 0 D) (← fl v) (← f 0 P) (← f 0 g) (← f 0 s) (← f 0 i) (← f 0 x)
  | .cocon x => return .cocon (← f 0 x)
  | .scase l I D v P m s i x =>
    return .scase (← fl l) (← f 0 I) (← f 0 D) (← fl v) (← f 0 P) (← f 0 m) (← f 0 s) (← f 0 i) (← f 0 x)
  | .scofix l I D A g s i a =>
    return .scofix (← fl l) (← f 0 I) (← f 0 D) (← f 0 A) (← f 0 g) (← f 0 s) (← f 0 i) (← f 0 a)
  | .coit l I D S st i s =>
    return .coit (← fl l) (← f 0 I) (← f 0 D) (← f 0 S) (← f 0 st) (← f 0 i) (← f 0 s)
  | .ulift l A => return .ulift (← fl l) (← f 0 A)
  | .up a => return .up (← f 0 a)
  | .down t => return .down (← f 0 t)
  | t => pure t
where
  hintM (fl : Level → m Level) (f : Nat → Term R → m (Term R)) :
      Name × List Level × List (Term R) → m (Name × List Level × List (Term R))
    | (n, us, as) => return (n, ← us.mapM fl, ← as.mapM (f 0))

/-- Visit every immediate child (and level), ignoring the rebuilt term. -/
def forChildren {m : Type → Type} [Monad m] (fl : Level → m Unit) (f : Nat → Term R → m Unit)
    (t : Term R) : m Unit := do
  let _ ← t.mapChildrenM (fun l => do fl l; pure l) (fun k c => do f k c; pure c)

/-- Shift the free variables (indices `≥ cut`) up by `k`. -/
partial def lift (k : Nat) (cut : Nat := 0) : Term R → Term R
  | .var i => if i ≥ cut then .var (i + k) else .var i
  | t => Id.run <| t.mapChildrenM pure (fun d c => pure (lift k (cut + d) c))

/-- Abstract every occurrence of `target` (a term in the same context) as a new
variable `var 0`, shifting the other free variables up. This is how the elaborator
generalises a scrutinee in the expected type of a case (Lean's `kabstract`). -/
partial def abstract [BEq R] (t : Term R) (target : Term R) (depth : Nat := 0) : Term R :=
  if t == target.lift depth then .var depth else
  match t with
  | .var i => if i ≥ depth then .var (i + 1) else .var i
  | t => Id.run <| t.mapChildrenM pure (fun d c => pure (abstract c target (depth + d)))

/-- Remove variable `k`, which must not occur, lowering the variables above it. -/
partial def strengthen? (k : Nat) (t : Term R) (depth : Nat := 0) : Option (Term R) :=
  match t with
  | .var i =>
    if i < depth || i < k + depth then some (.var i)
    else if i == k + depth then none
    else some (.var (i - 1))
  | t => t.mapChildrenM (m := Option) some (fun d c => strengthen? k c (depth + d))

/-- Substitute `s` for variable `k`. `s` is a term in the context *without* `k`. -/
partial def instantiateAt (t : Term R) (k : Nat) (s : Term R) (depth : Nat := 0) : Term R :=
  match t with
  | .var i =>
    if i < depth || i < k + depth then .var i
    else if i == k + depth then s.lift depth
    else .var (i - 1)
  | t => Id.run <| t.mapChildrenM pure (fun d c => pure (instantiateAt c k s (depth + d)))

/-- The head and arguments of an application spine. -/
def spine : Term R → Term R × List (Term R)
  | .app f a => let (h, as) := spine f; (h, as ++ [a])
  | t => (t, [])

/-- Instantiate universe level parameters `ps` with `us`. -/
partial def instLevels (ps : List Name) (us : List Level) (t : Term R) : Term R :=
  Id.run <| t.mapChildrenM (fun l => pure (l.instParams ps us)) (fun _ c => pure (instLevels ps us c))

/-- All level parameter names mentioned in a term. -/
partial def levelParamsUsed (t : Term R) : List Name :=
  (go t |>.run []).2
where
  go (t : Term R) : StateM (List Name) Unit :=
    t.forChildren (fun l => modify (l.params ++ ·)) (fun _ c => go c)

end Term

/-- A description that starts with a choice of tag, `Desc.arg q (Enum ls) F`, or, in a
data type above `Type`, `Desc.arg q (ULift (Enum ls)) F` (Q4: the tag is lifted to the
type's universe). Returns the labels, whether the tag is lifted, and `F`. -/
def Term.descTag? {R : Type} : Term R → Option (List Name × Bool × Term R)
  | .darg _ (.enum ls) F => some (ls, false, F)
  | .darg _ (.ulift _ (.enum ls)) F => some (ls, true, F)
  | _ => none

/-- The binder name of a **phantom** argument (`Elab/Inductive.lean`): a type whose
parameters no field mentions ends in `(0 phantom✝ : D) → … → Unit` instead of `Unit`,
with `D` mentioning the parameter. Such a function type has one inhabitant up to η,
`fun _ => ()`, so it has no runtime content (`erasable`). The name is inaccessible,
so only the elaborator writes it. -/
def phantomName : Name := "phantom✝"

/-- The **structure marker** (stage 22i): a structure with at least one field ends in
`(0 phantom✝ : D) → … → (0 fields✝ : Enum [fields✝]) → Unit` (its phantom tail, 22e, then
the marker), so `structure S where val : A` is `(val : A) × ((0 fields✝ : Enum [fields✝]) → Unit)`.
Erasure recognises the marker and unboxes the Σ whose second component it ends (the
structure's last field): at run time that pair is just the field. The marker is in the
*type*, not only in a name, because the representation must be a function of the type up
to conversion: conversion ignores binder names but compares domains, and no user-written
type has the domain `Enum [fields✝]` (the label is inaccessible), so nothing convertible
to a structure lacks the marker, and nothing else has it. -/
def structTailName : Name := "fields✝"

/-- The marker's domain, `Enum [fields✝]`. -/
def structTailDom {R : Type} : Term R := .enum [structTailName]

/-- A binder name of a phantom tail (`phantomName` or `structTailName`). -/
def isPhantomName (x : Name) : Bool := x == phantomName || x == structTailName

/-- The value of a phantom tail type, `fun _ … _ => ()`. -/
partial def Term.phantomTailVal? {R : Type} : Term R → Option (Term R)
  | .pi x _ _ _ b _ => if isPhantomName x then (phantomTailVal? b).map (.lam x) else none
  | .unit _ => some .tt
  | _ => none

/-- Which casts `cast A A e t` reduce to `t` (regularity), for the D1 experiment
(`wiz-notes/d1-experiment.md`). Regularity, definitional proof irrelevance and an
impredicative `Prop` together break normalisation (Abel–Coquand, LMCS 2020;
`Tests/Elab.lean` "D1"). The default is `full`; the others are prototypes. -/
inductive Regularity where
  /-- whenever the two types are equal (today's rule) -/
  | full
  /-- (R1) only at types that are not propositions -/
  | nonProp
  /-- (R2) only along `refl`, `reflTy`, `()` or a `transp` of such proofs along such proofs -/
  | refl
  /-- never: a cast computes only by the shapes of its types -/
  | off
  deriving BEq, Repr, Inhabited

/-- The global environment. `order` records insertion order so anything that walks
the environment does so deterministically (never iterate the hash map directly). -/
structure Globals (R : Type) where
  decls : Std.HashMap Name (Decl R) := {}
  order : Array Name := #[]
  /-- `builtin key := name` registrations, such as `("nat", Nat)` and `("nat.add", Nat.add)` -/
  builtins : List (Name × Name) := []
  /-- unfold every definition eagerly (no gluing), for normal forms -/
  eager : Bool := false
  /-- which casts reduce by regularity (D1: `off`, so that checking terminates) -/
  regularity : Regularity := .off
  /-- D1 experiment (default off): reject impredicative `Π`s, those into `Prop` whose
  domain is a universe or ends in one (`Prop`, `A → Prop`, `Type`, …) -/
  predicativeProp : Bool := false
  /-- (13b) names private to a module (`private def …`, `private mk ::`), with the
  module: the elaborator rejects them elsewhere. The kernel ignores this. -/
  privates : Std.HashMap Name String := {}
  /-- (13b) structures with a private constructor, with their module: elsewhere the
  elaborator sees them as opaque (`Globals.elabView`). The kernel ignores this. -/
  opaques : Std.HashMap Name String := {}
  /-- the module being elaborated (`""`: the main file), for `privates` and `opaques` -/
  module : String := ""

namespace Globals

variable {R : Type}

def find? (g : Globals R) (n : Name) : Option (Decl R) := g.decls[n]?

def contains (g : Globals R) (n : Name) : Bool := g.decls.contains n

/-- The key `n` is registered under (`nat.add`, ...), if any. -/
def builtinKey? (g : Globals R) (n : Name) : Option Name :=
  (g.builtins.find? (·.2 == n)).map (·.1)

/-- Unchecked insertion. Use `Wiz.addDecl` to type check first. -/
def insert (g : Globals R) (d : Decl R) : Globals R :=
  { g with
    decls := g.decls.insert d.name d
    order := if g.decls.contains d.name then g.order else g.order.push d.name }

/-- (13b) The environment as the elaborator sees it in `g.module`: a structure whose
constructor is private to another module has no definition (it doesn't unfold), so
values of it can't be built from a tuple or a look-alike structure; its fields are read
through its projection functions. The kernel still checks against `g` itself. -/
def elabView (g : Globals R) : Globals R :=
  if g.opaques.isEmpty then g else
  g.opaques.fold (init := g) fun g' n m =>
    if m == g.module then g' else
    match g'.decls[n]? with
    | some d => { g' with decls := g'.decls.insert n { d with value := none } }
    | none => g'

/-- (13b) Is `T` opaque here (a structure, inductive or coinductive type with private
constructors, fields or observations, of another module)? Its module, if so. -/
def opaqueTo? (g : Globals R) (T : Name) : Option String :=
  match g.opaques[T]? with
  | some m => if m == g.module then none else some m
  | none => none

/-- (13b) The module `n` is private to, if that is not the one being elaborated. -/
def privateTo? (g : Globals R) (n : Name) : Option String :=
  match g.privates[n]? with
  | some m => if m == g.module then none else some m
  | none => none

end Globals

end Wiz
