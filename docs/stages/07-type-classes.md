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
  fields, the indices of its result), each field (`FieldView`: name, kind, type, and
  whether it is recursive), and whether it is a structure. `MacroM.getType n` is the
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
