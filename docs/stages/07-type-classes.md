# Stage 7: type classes

## 7a: glued evaluation ✅

Type classes need to see names: the class in `Add Nat`, the nominal head in
`Monad TacticM`. Evaluation used to unfold every definition eagerly, so those names
disappeared. Now a defined constant evaluates to a **glued** value
`Val.unfold n us sp t`: the head `n` applied to the spine `sp`, with its unfolding
`t` computed lazily (a `Thunk` remembers it), as in smalltt and Lean.

* `vApp` grows a glued spine (lazily), and `quote` keeps the name. So types print as
  `TacticM Nat`, and elaborated terms and meta solutions stay small.
* `whnf` unfolds glued heads. Everything that matches on a value's shape calls it
  first: the kernel's eliminators, `check`/`infer`, erasure, and the elaborator's
  `force`. The exercise code got given `whnf` lines (or a given first match arm) where
  needed.
* `conv`/`convTy` (`convGlued`) and `unify` (`unifyGlued`) first compare two glued
  values with the same head by their spines, and unfold only if that fails. A meta
  is solved with a glued value as is. Outside the pattern fragment, `unify` tries
  the **first-order approximation** (`?m a =?= f b` ↦ `?m =?= f`, `a =?= b`).
* `Decl.inline` (constructors) unfold eagerly, so values still print as `.succ n`.
  `nf` (`#reduce`) evaluates with `Globals.eager`.
* Exercise 3.1 is now `forceMeta` (metas only). `force` also unfolds glued heads.

The prelude now elaborates about 6× faster.

## 7b: classes, instances, tabled resolution ✅

```
class Inhabited (A : Type) where
  default : A
instance : Inhabited Nat := Inhabited.mk 0
instance {A : Type} [Inhabited A] : Inhabited (List A) where
  default := List.cons Inhabited.default List.nil
#eval (Inhabited.default : List Nat)       -- .cons 0 .nil
```

* `class` is `structure` plus a record of the class (its fields, and which
  parameters are `outParam`s). It generates methods `C.f : {Δ} → [self : C Δ] → F`.
  A structure's universe is now inferred from its fields when not given.
* `[x : C A]` / `[C A]` binders are `BinderInfo.instImplicit`. Applying a function
  creates a hole and an **instance problem**. It is solved when its non-output
  arguments are known, at the latest at the end of the command. Inside a definition,
  instance binders are local instances.
* `instance (priority := n)? binders : C T := v`, or `where f := …` with the fields
  by name. The instance is named after its type (`instInhabitedNat`). Instances
  overlap freely (Lean-style): local instances first, then higher priority, then
  later declarations.
* **Resolution** (`Elab/Class.lean`) is tabled, after Selsam, Ullrich & de Moura
  (2020), with generator and consumer nodes and an answer table per normalised goal.
  A subgoal already in the table waits for that goal's answers instead of being
  solved again, so cyclic instances fail instead of looping. Output parameters are
  fresh holes during resolution and are unified with the answer afterwards.
* `do` now works for any `Monad` (`class Monad (m : Type → Type)` in the prelude,
  with an instance for `TacticM`), thanks to glued evaluation and the first-order
  approximation: `?m ?A =?= TacticM Nat` gives `?m := TacticM`.

| #   | Where              | What                                             |
|-----|--------------------|--------------------------------------------------|
| 7.1 | `Elab/Class.lean`  | `applyInstance`: an instance's subgoals          |

Known limitations: no auto-bound implicits (write `{A : Type}`); instance problems
must have no holes left in their arguments by the end of the command; answers must be
complete terms; no default instances or coercions yet.

## 7c: command macros, reflection, `deriving` ✅

```
import Deriving
inductive Tree (A : Type) where
  | leaf
  | node (l : Tree A) (x : A) (r : Tree A)
  deriving Repr, BEq, Inhabited
#eval Repr.repr (Tree.node .leaf 1 .leaf)    -- "Tree.node Tree.leaf 1 Tree.leaf"
deriving instance Repr for Shape             -- after the fact
```

* **Command macros.** `attribute [macro command.k] f` with `f : CommandMacro :=
  Syntax → MacroM (List Syntax)` expands one command into any number of commands
  (`runCommandMacro`), built with `` `(command| …) `` quotations. A `Macro` still works
  for commands too.
* **Reflection** (`Elab/Reflect.lean`). `MacroM.getInductive T : MacroM (Option IndView)`
  describes an inductive type or structure: its parameters and indices
  (`ParamView`: name, binder kind, type), its constructors (`CtorView`: short name,
  fields, the indices of its result), each field (`FieldView`: name, kind, type,
  whether it is recursive, and whether it is a proof), and whether it is a structure. `MacroM.getType n` is the
  type of any declaration. Types are **syntax**, printed with binder names and parsed
  back, so a macro can splice them; the facts come from the kernel's declarations
  (`T.desc`, `T.c`), so they also hold for declarations replayed from the cache.
  The requests are two more `Tac` constructors.
* **Deriving.** `inductive … deriving C₁, C₂` (also `structure`) and
  `deriving instance C₁, C₂ for T₁, T₂` run C's **deriver**, a Wiz function
  `Deriver := String → MacroM (List Syntax)` registered with `attribute [deriver C] f`.
  `lib/Deriving.wiz` defines `Inhabited`, `BEq` and `Repr` (`reprPrec : A → Nat →
  String`), their derivers, and instances for `Nat`, `String`, `Bool`, `Option`, `List`.
  A derived instance has type `{A : Type} → [C A] → … → C (T A …)` (an instance argument
  for each `Type` parameter) and eliminates with `T.rec`, so recursion needs no
  termination check; a structure uses its projections.
* Splicing names: `$x` works wherever the grammar expects an identifier
  (`fun $x => …`, `{$x : $t} → …`, `def $x …`). A name that a quotation introduces
  gets the expansion's scope; names the deriver builds with `✝` in them (`f✝0`) can't
  capture the user's.

| #   | Where              | What                                             |
|-----|--------------------|--------------------------------------------------|
| 7.2 | `lib/Deriving.wiz` | `Derive.firstPlain`: the constructor `Inhabited` uses |

Limitations: `BEq` and `Inhabited` reject indexed families (`Repr` handles them, and
so mutual types); no `DecidableEq` (it needs no-confusion proofs); quotations can't
splice lists (`$xs*`), so derivers fold one-element quotations and use
`Syntax.mkApp`; the self-hosted frontend has no macros yet. `Repr String` doesn't
escape.

## 7d: deriving with proof fields and in any universe ✅

```
import Deriving
structure Pos where
  n : Nat
  h : Nat.lt 0 n = Bool.true
  deriving Repr, BEq
#eval Repr.repr (Pos.mk 3 (refl Bool.true))   -- "Pos.mk 3 _"
inductive Box.{u} (A : Type u) where          -- Box : Type u → Type u (inferred)
  | mk (x : A)
  deriving Repr, BEq, Inhabited
```

* **Proof fields.** `FieldView` says whether a field is a **proof** (its type is a
  proposition; `Elab/Reflect.lean` asks the kernel's `isProp`). `Repr` shows it as `_`,
  `BEq` doesn't compare it (proofs of a proposition are all equal), and `Inhabited`
  skips a constructor with one (there is no `default` proof).
* **Any universe.** `Inhabited`, `BEq` and `Repr` take `A : Type u`; a derived instance
  takes an instance argument for each `Type` or `Type u` parameter. An `instance` has
  the universe names in its binders and type as its universe parameters
  (`{A : Type u} → [Repr A] → Repr (Box A)`), so derivers need no `.{u}` syntax.
* **Inferred universes.** Without a signature, an `inductive` or `structure` lives in
  the smallest `Type l` that holds its fields: `Box.{u} (A : Type u)` is in `Type u`
  (before, it was put in `Type` and rejected).
* **Through `ULift`.** A field smaller than its type's universe is lifted in the
  description (CoreSpec §4.1, F5 in [Status.md](../Status.md)); the recursor a deriver eliminates
  with hands out `down` of it, whose type is the field's own, so instance resolution
  sees `Nat`, not `ULift Nat` (tested on a type in `Type 1` with a `Nat` field and a
  proof field).

## 7e: numeric classes ✅

```
class Add (A : Type) where
  add : A → A → A                      -- also Sub, Mul, Div, Mod, Neg
class OfNat (A : Type) (n : Nat) where
  ofNat : A
instance {ω w : Nat} : Add (UIntN w) := Add.mk UIntN.add
def mac {ω w : Nat} (a b c : UIntN w) : UIntN w := a * b + c
def x : U8 := 200                      -- OfNat (UIntN 8) 200
```

Decision HD9: `+ - * / %` and prefix `-` are the methods of the Prelude's classes `Add`,
`Sub`, `Mul`, `Div`, `Mod` and `Neg` (`infixl:65 " + " => Add.add`, `syntax:75 "-" term:75`),
with instances for `Nat` that are the natively computed functions (`Add.mk Nat.add`).

* **Numerals.** At the `builtin nat` type a numeral is still the kernel's literal. At
  another type `T` it is `@OfNat.ofNat T n ?i`, with an instance problem `OfNat T n`: the
  literal is an index of the class, as in Lean, so an instance can look at it (Z3 below
  reduces it mod 3; a `Fin n` instance could check the bound). At an unsolved type the
  numeral is a `Nat`, as before: that default is a rule of the numeral elaborator, not a
  default instance, so ordinary arithmetic involves no search beyond `Add Nat`.
* **Conversion.** `a + b` at `Nat` is `Add.add Nat instAddNat a b`, a glued application
  that unfolds to `Nat.add a b`: `2 + 3` computes natively, `rfl : 2 + 3 = 5` and
  `0 + n = n` hold by evaluation, and lemmas stated with `+` (`Nat.add_comm` in
  lib/Vec.wiz) are unchanged.
* **Elaboration order.** An application of a class method with a numeral argument
  (`1 + x`, `Add.add x 1`, `-3`) is elaborated expected type first (in infer mode against
  a fresh type), and a numeral whose type is still a hole waits for the other arguments:
  `1 + x` with `x : U8`, `0 + a` with `a : Int`, `(-3 : Int)` and `def x : U8 := 1 + 2`
  put the numerals at the right type, with no search (a small Lean `binop%`).
* **Signed and unsigned words.** `UIntN w` and `IntN w` have one shape but are sealed
  (22k, docs/stages/22-numbers.md), so they are different types and ordinary resolution
  tells their instances apart: `/` at `I32` is signed and at `U32` unsigned. (An
  interim nominal rule in `Class.lean` did this before the seal; it is gone, so ordinary
  look-alike types still share instances, as they share everything else.)
* **Declared types.** A definition by equations, a copattern definition, an inductive
  type's signature and constructor types solve their instance problems before their
  types are zonked (they used to be zonked at once: `(n : Nat) → n + 0 = n` would have
  left the instance a hole).
* **Compiled code.** A one-method class is unboxed (22i), so `Add.add` erases to
  `λ A self. self` and `instAddNat` to `Nat.add`. The Lean compiler substitutes such
  trivial definitions wherever they are applied (`ETerm.trivialBody`: a variable, a
  projection, a global, `◾`, or a forwarder `f x y`) and projects a method out of an
  instance with several (`ETerm.objBody`, `projOf`): `a * b + a` at `Nat` compiles to
  `prim nat.mul`/`prim nat.add`, as before, with no dictionary; at `U32` it is
  `wiz_word_mul`/`wiz_word_add` (numerals `wiz_word_of_nat`), as `UIntN.add` was. Inlined
  arguments float out of `let`s, and a partial application used once is substituted, so
  the inlined call meets its arguments.
* **Instances** (docs/libraries.md, "Numbers"): `Int` (lib/Int.wiz, printed `-10` through
  `builtin int`), `UIntN w`/`IntN w` and their aliases (lib/Word.wiz), `UInt64`,
  `Float64` (lib/IO.wiz).
* **Literals that don't fit.** A numeral at `UIntN w` above `2^w - 1`, or at `IntN w`
  above `2^(w-1)` (so `-128 : I8` is fine), still wraps around (`OfNat (UIntN w) n` is
  `UIntN.ofNat`), but with a warning: "the numeral 300 does not fit in UIntN 8 (at most
  255): it wraps around to 44" (the elaborator knows these two families by name; an
  `Info.warning` carries it to the command's messages).
* **Errors.** `"a" + 1`: "failed to synthesize an instance of Add String"; `(1 : Bool)`:
  "failed to synthesize an instance of OfNat Bool 1"; `-1 : Nat`: "… Neg Nat".
* **The self-hosted toolchain** has no type classes: its own prelude
  (`selfhost/Frontend.wiz`, `preludeText`) keeps `infixl " + " => Nat.add`, and its
  sources use `+` only at `Nat`, which both frontends accept.

Heterogeneous `HAdd A B C` (Lean's) is not here: it needs default instances, which the
class mechanism lacks; see /workspace/wiz-notes/num-classes.md for the design.
Types are structural (two declarations of the same shape are one type), so an instance
for a look-alike type applies too; numerals as patterns: see 13q (`docs/stages/13-language.md`).
