import WizMeta.Level

/-!
# Syntax of the spec

The spec has its own term type. It is not `Wiz.Term`: that type changes whenever the
kernel does, and the rules (and later the proofs) should not move with it.
`WizMeta/Translate.lean` maps `Wiz.Term` here and fails outside the fragment.

* de Bruijn indices; a binder's body lives under one more variable;
* quantities are **labels** `0, 1, ω` on binders and description fields: part of a type's
  identity, never computed with (no usage checking, no quantity variables);
* a `Π`/`Σ` carries its sort. The spec's rules type only `some s` (mandatory sorts,
  metatheory-plan N2); `none` exists so that today's kernel terms can be read, and the
  checker accepts it only when asked to (`Opts.sortsOptional`);
* the branches of `ecase` are a list built from `bnil`/`bcons` inside `Tm` (as in
  `Kernel.wiz`), so that `Tm` is a plain inductive type;
* no sizes: `μ` is `μ^∞`.
-/

namespace WizMeta

/-- Quantity labels. -/
inductive Q where
  | zero | one | many
  deriving Repr, Inhabited, BEq, DecidableEq

inductive Tm where
  | var (i : Nat)
  /-- a global constant at universe levels `us` -/
  | const (c : String) (us : List Lvl)
  | sort (l : Lvl)
  /-- `(q x : A) → B` in `Sort s` -/
  | pi (q : Q) (s : Option Lvl) (A B : Tm)
  | lam (b : Tm)
  | app (f a : Tm)
  /-- `let x :q A := v; b` -/
  | letE (q : Q) (A v b : Tm)
  | ann (t A : Tm)
  /-- `(q x : A) × B` in `Sort s` -/
  | sigma (q : Q) (s : Option Lvl) (A B : Tm)
  | pair (a b : Tm)
  | fst (p : Tm)
  | snd (p : Tm)
  | unit (l : Lvl)
  | tt
  | empty (l : Lvl)
  | absurd (M t : Tm)
  /-- an enumeration of `n` tags (labels are metadata in Wiz and absent here) -/
  | enum (n : Nat)
  | tag (n i : Nat)
  /-- `ecase s as z. M [bs]`; `M` is under one binder, `bs` is a `bnil`/`bcons` list -/
  | ecase (M s bs : Tm)
  | bnil
  | bcons (b bs : Tm)
  | eq (A a b : Tm)
  | eqTy (A B : Tm)
  | refl (A a : Tm)
  | reflTy (A : Tm)
  | cast (A B e t : Tm)
  | transp (A a P p b e : Tm)
  -- Tprog
  | ulift (l : Lvl) (A : Tm)
  | up (a : Tm)
  | down (t : Tm)
  /-- the type of quantities and its three elements: only as the argument that
  `Desc.elim`'s methods receive -/
  | qty
  | qlit (q : Q)
  | desc (l : Lvl) (I : Tm)
  | dret (i : Tm)
  /-- a field of a description. Its quantity is a *term* of type `Qty` (`Desc.elim`'s
  method is generic in it), unlike a binder's, which is a label -/
  | darg (q S D : Tm)
  | drec (q j D : Tm)
  | dhrec (q H j D : Tm)
  | delim (v : Lvl) (P mret marg mrec mhrec D : Tm)
  /-- `⟦D⟧ X i`, the type of a constructor's payload. A former of its own (in the kernel
  it is a closed `Desc.elim` term whose `Σ`s take the field's quantity as a variable,
  which a label cannot be) -/
  | interp (l : Lvl) (I D X i : Tm)
  /-- `All D X P i xs`: one `P`-proof per recursive field of the payload `xs : ⟦D⟧ X i`
  (the type of `ind`'s induction hypotheses), and `hyps D X P f i xs`, its element built
  by applying `f` to every recursive field. Formers of their own, like `interp` -/
  | dall (l v : Lvl) (I D X P i xs : Tm)
  | dhyps (l v : Lvl) (I D X P f i xs : Tm)
  | mu (l : Lvl) (I D i : Tm)
  | con (x : Tm)
  | ind (l : Lvl) (I D : Tm) (v : Lvl) (P m i x : Tm)
  deriving Repr, Inhabited, BEq

namespace Tm

def branches : List Tm → Tm
  | [] => bnil
  | b :: bs => bcons b (branches bs)

/-- The `k`-th branch of a branch list. -/
def branch? : Tm → Nat → Option Tm
  | bcons b _, 0 => some b
  | bcons _ bs, k + 1 => branch? bs k
  | _, _ => none

/-- The branches as a list, if the term is a well-formed branch list. -/
def branchList? : Tm → Option (List Tm)
  | bnil => some []
  | bcons b bs => (branchList? bs).map (b :: ·)
  | _ => none

/-! ## Renaming and substitution -/

def upRen (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ρ n + 1

def ren (ρ : Nat → Nat) : Tm → Tm
  | var i => var (ρ i)
  | const c us => const c us
  | sort l => sort l
  | pi q s A B => pi q s (ren ρ A) (ren (upRen ρ) B)
  | lam b => lam (ren (upRen ρ) b)
  | app f a => app (ren ρ f) (ren ρ a)
  | letE q A v b => letE q (ren ρ A) (ren ρ v) (ren (upRen ρ) b)
  | ann t A => ann (ren ρ t) (ren ρ A)
  | sigma q s A B => sigma q s (ren ρ A) (ren (upRen ρ) B)
  | pair a b => pair (ren ρ a) (ren ρ b)
  | fst p => fst (ren ρ p)
  | snd p => snd (ren ρ p)
  | unit l => unit l
  | tt => tt
  | empty l => empty l
  | absurd M t => absurd (ren ρ M) (ren ρ t)
  | enum n => enum n
  | tag n i => tag n i
  | ecase M s bs => ecase (ren (upRen ρ) M) (ren ρ s) (ren ρ bs)
  | bnil => bnil
  | bcons b bs => bcons (ren ρ b) (ren ρ bs)
  | eq A a b => eq (ren ρ A) (ren ρ a) (ren ρ b)
  | eqTy A B => eqTy (ren ρ A) (ren ρ B)
  | refl A a => refl (ren ρ A) (ren ρ a)
  | reflTy A => reflTy (ren ρ A)
  | cast A B e t => cast (ren ρ A) (ren ρ B) (ren ρ e) (ren ρ t)
  | transp A a P p b e => transp (ren ρ A) (ren ρ a) (ren ρ P) (ren ρ p) (ren ρ b) (ren ρ e)
  | ulift l A => ulift l (ren ρ A)
  | up a => up (ren ρ a)
  | down t => down (ren ρ t)
  | qty => qty
  | qlit q => qlit q
  | desc l I => desc l (ren ρ I)
  | dret i => dret (ren ρ i)
  | darg q S D => darg (ren ρ q) (ren ρ S) (ren ρ D)
  | drec q j D => drec (ren ρ q) (ren ρ j) (ren ρ D)
  | dhrec q H j D => dhrec (ren ρ q) (ren ρ H) (ren ρ j) (ren ρ D)
  | interp l I D X i => interp l (ren ρ I) (ren ρ D) (ren ρ X) (ren ρ i)
  | dall l v I D X P i xs => dall l v (ren ρ I) (ren ρ D) (ren ρ X) (ren ρ P) (ren ρ i) (ren ρ xs)
  | dhyps l v I D X P g i xs =>
    dhyps l v (ren ρ I) (ren ρ D) (ren ρ X) (ren ρ P) (ren ρ g) (ren ρ i) (ren ρ xs)
  | delim v P a b c h D => delim v (ren ρ P) (ren ρ a) (ren ρ b) (ren ρ c) (ren ρ h) (ren ρ D)
  | mu l I D i => mu l (ren ρ I) (ren ρ D) (ren ρ i)
  | con x => con (ren ρ x)
  | ind l I D v P m i x => ind l (ren ρ I) (ren ρ D) v (ren ρ P) (ren ρ m) (ren ρ i) (ren ρ x)

/-- Weakening by one variable. -/
def shift (t : Tm) : Tm := ren (· + 1) t
/-- Weakening by `n` variables. -/
def shiftN (n : Nat) (t : Tm) : Tm := ren (· + n) t

def upSub (σ : Nat → Tm) : Nat → Tm
  | 0 => var 0
  | n + 1 => shift (σ n)

def sub (σ : Nat → Tm) : Tm → Tm
  | var i => σ i
  | const c us => const c us
  | sort l => sort l
  | pi q s A B => pi q s (sub σ A) (sub (upSub σ) B)
  | lam b => lam (sub (upSub σ) b)
  | app f a => app (sub σ f) (sub σ a)
  | letE q A v b => letE q (sub σ A) (sub σ v) (sub (upSub σ) b)
  | ann t A => ann (sub σ t) (sub σ A)
  | sigma q s A B => sigma q s (sub σ A) (sub (upSub σ) B)
  | pair a b => pair (sub σ a) (sub σ b)
  | fst p => fst (sub σ p)
  | snd p => snd (sub σ p)
  | unit l => unit l
  | tt => tt
  | empty l => empty l
  | absurd M t => absurd (sub σ M) (sub σ t)
  | enum n => enum n
  | tag n i => tag n i
  | ecase M s bs => ecase (sub (upSub σ) M) (sub σ s) (sub σ bs)
  | bnil => bnil
  | bcons b bs => bcons (sub σ b) (sub σ bs)
  | eq A a b => eq (sub σ A) (sub σ a) (sub σ b)
  | eqTy A B => eqTy (sub σ A) (sub σ B)
  | refl A a => refl (sub σ A) (sub σ a)
  | reflTy A => reflTy (sub σ A)
  | cast A B e t => cast (sub σ A) (sub σ B) (sub σ e) (sub σ t)
  | transp A a P p b e => transp (sub σ A) (sub σ a) (sub σ P) (sub σ p) (sub σ b) (sub σ e)
  | ulift l A => ulift l (sub σ A)
  | up a => up (sub σ a)
  | down t => down (sub σ t)
  | qty => qty
  | qlit q => qlit q
  | desc l I => desc l (sub σ I)
  | dret i => dret (sub σ i)
  | darg q S D => darg (sub σ q) (sub σ S) (sub σ D)
  | drec q j D => drec (sub σ q) (sub σ j) (sub σ D)
  | dhrec q H j D => dhrec (sub σ q) (sub σ H) (sub σ j) (sub σ D)
  | interp l I D X i => interp l (sub σ I) (sub σ D) (sub σ X) (sub σ i)
  | dall l v I D X P i xs => dall l v (sub σ I) (sub σ D) (sub σ X) (sub σ P) (sub σ i) (sub σ xs)
  | dhyps l v I D X P g i xs =>
    dhyps l v (sub σ I) (sub σ D) (sub σ X) (sub σ P) (sub σ g) (sub σ i) (sub σ xs)
  | delim v P a b c h D => delim v (sub σ P) (sub σ a) (sub σ b) (sub σ c) (sub σ h) (sub σ D)
  | mu l I D i => mu l (sub σ I) (sub σ D) (sub σ i)
  | con x => con (sub σ x)
  | ind l I D v P m i x => ind l (sub σ I) (sub σ D) v (sub σ P) (sub σ m) (sub σ i) (sub σ x)

/-- The substitution `[a/0]`. -/
def one (a : Tm) : Nat → Tm
  | 0 => a
  | n + 1 => var n

/-- `b[a/x]` for the innermost variable of `b`. -/
def inst (b a : Tm) : Tm := sub (one a) b

/-- Substitute levels for the level parameters. -/
def instL (us : List Lvl) : Tm → Tm
  | var i => var i
  | const c vs => const c (vs.map (Lvl.inst us))
  | sort l => sort (l.inst us)
  | pi q s A B => pi q (s.map (Lvl.inst us)) (instL us A) (instL us B)
  | lam b => lam (instL us b)
  | app f a => app (instL us f) (instL us a)
  | letE q A v b => letE q (instL us A) (instL us v) (instL us b)
  | ann t A => ann (instL us t) (instL us A)
  | sigma q s A B => sigma q (s.map (Lvl.inst us)) (instL us A) (instL us B)
  | pair a b => pair (instL us a) (instL us b)
  | fst p => fst (instL us p)
  | snd p => snd (instL us p)
  | unit l => unit (l.inst us)
  | tt => tt
  | empty l => empty (l.inst us)
  | absurd M t => absurd (instL us M) (instL us t)
  | enum n => enum n
  | tag n i => tag n i
  | ecase M s bs => ecase (instL us M) (instL us s) (instL us bs)
  | bnil => bnil
  | bcons b bs => bcons (instL us b) (instL us bs)
  | eq A a b => eq (instL us A) (instL us a) (instL us b)
  | eqTy A B => eqTy (instL us A) (instL us B)
  | refl A a => refl (instL us A) (instL us a)
  | reflTy A => reflTy (instL us A)
  | cast A B e t => cast (instL us A) (instL us B) (instL us e) (instL us t)
  | transp A a P p b e =>
    transp (instL us A) (instL us a) (instL us P) (instL us p) (instL us b) (instL us e)
  | ulift l A => ulift (l.inst us) (instL us A)
  | up a => up (instL us a)
  | down t => down (instL us t)
  | qty => qty
  | qlit q => qlit q
  | desc l I => desc (l.inst us) (instL us I)
  | dret i => dret (instL us i)
  | darg q S D => darg (instL us q) (instL us S) (instL us D)
  | drec q j D => drec (instL us q) (instL us j) (instL us D)
  | dhrec q H j D => dhrec (instL us q) (instL us H) (instL us j) (instL us D)
  | interp l I D X i => interp (l.inst us) (instL us I) (instL us D) (instL us X) (instL us i)
  | dall l v I D X P i xs =>
    dall (l.inst us) (v.inst us) (instL us I) (instL us D) (instL us X) (instL us P) (instL us i) (instL us xs)
  | dhyps l v I D X P g i xs =>
    dhyps (l.inst us) (v.inst us) (instL us I) (instL us D) (instL us X) (instL us P) (instL us g) (instL us i)
      (instL us xs)
  | delim v P a b c h D =>
    delim (v.inst us) (instL us P) (instL us a) (instL us b) (instL us c) (instL us h) (instL us D)
  | mu l I D i => mu (l.inst us) (instL us I) (instL us D) (instL us i)
  | con x => con (instL us x)
  | ind l I D v P m i x =>
    ind (l.inst us) (instL us I) (instL us D) (v.inst us) (instL us P) (instL us m) (instL us i) (instL us x)

/-- Every level parameter in the term is below `n`. -/
def lvlBound : Tm → Nat
  | var _ | tt | enum _ | tag _ _ | bnil | qty | qlit _ => 0
  | const _ us => us.foldl (fun m u => Nat.max m u.bound) 0
  | sort l | unit l | empty l => l.bound
  | pi _ s A B | sigma _ s A B => Nat.max ((s.map Lvl.bound).getD 0) (Nat.max (lvlBound A) (lvlBound B))
  | lam b | fst b | snd b | reflTy b | up b | down b | dret b | con b => lvlBound b
  | app a b | ann a b | pair a b | absurd a b | bcons a b | eqTy a b | refl a b =>
    Nat.max (lvlBound a) (lvlBound b)
  | letE _ a b c | ecase a b c | eq a b c | darg a b c | drec a b c =>
    Nat.max (lvlBound a) (Nat.max (lvlBound b) (lvlBound c))
  | interp l a b c d =>
    Nat.max l.bound (Nat.max (Nat.max (lvlBound a) (lvlBound b)) (Nat.max (lvlBound c) (lvlBound d)))
  | cast a b c d | dhrec a b c d => Nat.max (Nat.max (lvlBound a) (lvlBound b)) (Nat.max (lvlBound c) (lvlBound d))
  | transp a b c d e f =>
    Nat.max (Nat.max (lvlBound a) (lvlBound b))
      (Nat.max (Nat.max (lvlBound c) (lvlBound d)) (Nat.max (lvlBound e) (lvlBound f)))
  | ulift l A | desc l A => Nat.max l.bound (lvlBound A)
  | delim v a b c d e f =>
    Nat.max v.bound (Nat.max (Nat.max (lvlBound a) (lvlBound b))
      (Nat.max (Nat.max (lvlBound c) (lvlBound d)) (Nat.max (lvlBound e) (lvlBound f))))
  | mu l a b c => Nat.max l.bound (Nat.max (lvlBound a) (Nat.max (lvlBound b) (lvlBound c)))
  | dall l v a b c d e f =>
    Nat.max (Nat.max l.bound v.bound) (Nat.max (Nat.max (lvlBound a) (lvlBound b))
      (Nat.max (Nat.max (lvlBound c) (lvlBound d)) (Nat.max (lvlBound e) (lvlBound f))))
  | dhyps l v a b c d e f g =>
    Nat.max (Nat.max l.bound v.bound) (Nat.max (Nat.max (lvlBound a) (Nat.max (lvlBound b) (lvlBound g)))
      (Nat.max (Nat.max (lvlBound c) (lvlBound d)) (Nat.max (lvlBound e) (lvlBound f))))
  | ind l a b v c d e f =>
    Nat.max (Nat.max l.bound v.bound) (Nat.max (Nat.max (lvlBound a) (lvlBound b))
      (Nat.max (Nat.max (lvlBound c) (lvlBound d)) (Nat.max (lvlBound e) (lvlBound f))))

end Tm

/-- A context: the types of the variables, innermost first. The type at position `i` lives
in the context of the entries after it, so the type of `var i` is `Γ[i]` weakened by
`i + 1`. -/
abbrev Ctx := List Tm

def Ctx.lookup (Γ : Ctx) (i : Nat) : Option Tm := (Γ[i]?).map (Tm.shiftN (i + 1))

/-- A global declaration: `nparams` level parameters, a type, and a value (`none` for an
axiom). Closed terms. -/
structure Decl where
  name : String
  nparams : Nat
  type : Tm
  value : Option Tm
  deriving Repr, Inhabited

/-- A signature, most recent declaration first. -/
abbrev Sig := List Decl

def Sig.find? (sg : Sig) (c : String) : Option Decl := List.find? (·.name == c) sg

end WizMeta
