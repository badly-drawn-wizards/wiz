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

Not in the core yet (see ROADMAP.md): μ/ν data and Σ-types (stage 4).
-/

namespace Wiz

abbrev Name := String

inductive BinderInfo where
  | default
  | implicit
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
  binder -/
  | pi (x : Name) (bi : BinderInfo) (q : Term R) (dom cod : Term R)
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
  /-- `(q x : A) × B`: the first component may be used `q` times -/
  | sigma (x : Name) (q : Term R) (fst snd : Term R)
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
  /-- the eliminator of descriptions, into `P : Desc I → Sort v` -/
  | delim (v : Level) (P mret marg mrec D : Term R)
  /-- the least fixed point `μ D i` -/
  | mu (l : Level) (I D i : Term R)
  | con (x : Term R)
  /-- induction: `ind P m i x : P i x` for `x : μ D i` -/
  | ind (l : Level) (I D : Term R) (v : Level) (P m i x : Term R)
  /-- the greatest fixed point `ν D i` -/
  | nu (l : Level) (I D i : Term R)
  /-- observation: `out x : ⟦D⟧ (ν D) i` -/
  | out (x : Term R)
  /-- coiteration: unfold a state `s : S i` with `step` -/
  | coit (l : Level) (I D S step i s : Term R)
  deriving Repr, Inhabited, BEq

/-- A global declaration. `value = none` is an axiom/postulate. -/
structure Decl (R : Type) where
  name  : Name
  /-- universe level parameters, e.g. `[u]` for `def id.{u} ...` -/
  levelParams : List Name := []
  type  : Term R
  value : Option (Term R)
  deriving Repr, Inhabited

namespace Term

variable {R : Type}

/-- Rebuild a term with `fl` applied to its levels and `f k c` to each immediate
child `c`, where `k` is the number of binders the child is under. Generic traversals
(level instantiation, zonking, free-variable checks) are written with this so they
don't need a case per constructor. -/
@[specialize] def mapChildrenM {m : Type → Type} [Monad m] (fl : Level → m Level)
    (f : Nat → Term R → m (Term R)) : Term R → m (Term R)
  | .pi x bi q a b => return .pi x bi (← f 0 q) (← f 0 a) (← f 1 b)
  | .lam x b => return .lam x (← f 1 b)
  | .app a b => return .app (← f 0 a) (← f 0 b)
  | .letE x q t v b => return .letE x (← f 0 q) (← f 0 t) (← f 0 v) (← f 1 b)
  | .ann a b => return .ann (← f 0 a) (← f 0 b)
  | .sort l => return .sort (← fl l)
  | .const n ls => return .const n (← ls.mapM fl)
  | .sigma x q a b => return .sigma x (← f 0 q) (← f 0 a) (← f 1 b)
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
  | .delim v P a b c D => return .delim (← fl v) (← f 0 P) (← f 0 a) (← f 0 b) (← f 0 c) (← f 0 D)
  | .mu l I D i => return .mu (← fl l) (← f 0 I) (← f 0 D) (← f 0 i)
  | .con x => return .con (← f 0 x)
  | .ind l I D v P mt i x =>
    return .ind (← fl l) (← f 0 I) (← f 0 D) (← fl v) (← f 0 P) (← f 0 mt) (← f 0 i) (← f 0 x)
  | .nu l I D i => return .nu (← fl l) (← f 0 I) (← f 0 D) (← f 0 i)
  | .out x => return .out (← f 0 x)
  | .coit l I D S st i s =>
    return .coit (← fl l) (← f 0 I) (← f 0 D) (← f 0 S) (← f 0 st) (← f 0 i) (← f 0 s)
  | t => pure t

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
partial def abstract [BEq R] (target : Term R) (t : Term R) (depth : Nat := 0) : Term R :=
  if t == target.lift depth then .var depth else
  match t with
  | .var i => if i ≥ depth then .var (i + 1) else .var i
  | t => Id.run <| t.mapChildrenM pure (fun d c => pure (abstract target c (depth + d)))

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

/-- The global environment. `order` records insertion order so anything that walks
the environment does so deterministically (never iterate the hash map directly). -/
structure Globals (R : Type) where
  decls : Std.HashMap Name (Decl R) := {}
  order : Array Name := #[]

namespace Globals

variable {R : Type}

def find? (g : Globals R) (n : Name) : Option (Decl R) := g.decls[n]?

def contains (g : Globals R) (n : Name) : Bool := g.decls.contains n

/-- Unchecked insertion. Use `Wiz.addDecl` to type check first. -/
def insert (g : Globals R) (d : Decl R) : Globals R :=
  { decls := g.decls.insert d.name d
    order := if g.decls.contains d.name then g.order else g.order.push d.name }

end Globals

end Wiz
