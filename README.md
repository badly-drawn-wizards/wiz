# wiz

A dependently typed language with quantitative types, built in Lean 4 as a learning
project. The implementation is staged; each stage leaves `sorry`s for you to fill in,
and a test suite tells you when you've got them right.

See [ROADMAP.md](ROADMAP.md) for the stages and the design decisions behind them.

```sh
lake build          # the library and the `wiz` executable
lake test           # all exercise tests; every case runs in its own process
lake test -- conv   # only the groups whose name starts with "conv"
```

An unimplemented exercise shows up as `✗ ... not implemented yet (hit a sorry)`.

The design decisions taken so far are listed at the top of [ROADMAP.md](ROADMAP.md).

## Stage 1: the core kernel

```
Wiz/
  Rig.lean               Rig / QRig classes: the algebra of quantities
  Rig/Instances.lean     Unit (plain MLTT), Nat (exact counts), ZeroOneMany (Idris 2)
  Core/Term.lean         core syntax (de Bruijn indices), Decl, Globals
  Core/Value.lean        semantic domain: neutrals + closures (de Bruijn levels)
  Core/Eval.lean         eval, vApp, Closure.inst, quote, nf
  Core/Conv.lean         definitional equality with η
  Core/Usage.lean        usage vectors
  Core/Check.lean        bidirectional QTT checker, addDecl
  Core/Pretty.lean       pretty printer
  Core/Raw.lean          named terms + a tiny DSL, until stage 2 adds a parser
Tests/                   the exercise tests
```

### Conventions to keep straight

* **Terms** use de Bruijn **indices**: `var 0` is the nearest binder.
* **Values** use de Bruijn **levels**: `Val.var 0` is the *outermost* binder.
  Converting in a context of size `l`: `index = l - level - 1`.
* Environments, contexts and usage vectors are lists with the **innermost** binder at
  the head, so `env[ix]` is the value of `var ix`.

## Exercises

Work through them in order, because later tests depend on earlier code.

| #   | Where                        | What                                                        |
|-----|------------------------------|-------------------------------------------------------------|
| 0.1 | `Rig/Instances.lean`         | `ZeroOneMany.add`, `mul`, `le` tables                        |
| 0.2 | `Rig/Instances.lean`         | prove the `QRig ZeroOneMany` laws                           |
| 1.1 | `Core/Eval.lean`             | `eval`                                                      |
| 1.2 | `Core/Eval.lean`             | `vApp`, `Closure.inst`                                      |
| 1.3 | `Core/Eval.lean`             | `quote`                                                     |
| 1.4 | `Core/Conv.lean`             | `conv`, including η for functions                           |
| 1.5 | `Core/Check.lean`            | `popUsage`: the heart of QTT                                |
| 1.6 | `Core/Check.lean`            | `check`: the `lam`, `let` and mode-switch rules              |
| 1.7 | `Core/Check.lean`            | `infer`                                                     |

The typing rules are written out in the docstring of `Core/Check.lean`.

### Optional extensions to stage 1

These have no tests. Write your own tests in `Tests/` as you go.

* **0.3** Atkey's erasure theorem needs extra conditions on the rig: *zero-sum-free*
  (`a + b = 0 → a = 0 ∧ b = 0`) and *zero-divisor-free* (`a * b = 0 → a = 0 ∨ b = 0`).
  Add them as a class and prove them for `ZeroOneMany` and `Nat`. Then find a rig
  where they fail and work out what goes wrong.
* **0.4** Add an affine rig `{0, ≤1, ω}`, where linear variables may be dropped, and
  a test showing a program it accepts that `ZeroOneMany` rejects.
* **0.5** Prove `Usage.add` commutative and `Usage.scale` distributive, using the
  `Rig` laws.
* **1.8** Implement Atkey's σ ∈ {0, 1} modes properly (see "Simplification vs. Atkey" in
  `Core/Check.lean`), so the checker stops verifying linearity inside type positions.
  (Stage 4d adds a light version, `Ctx.erased`, which only relaxes projections.)
* **1.9** Σ-types with a QTT-friendly eliminator, `let (x, y) := p; b`, which uses
  `p` once and binds both components at its quantity.
* **1.10** Glued evaluation: stop unfolding globals eagerly, keeping both the stuck
  and the unfolded form, so error messages print `Nat` and not its Church encoding.
* **1.11** Universe cumulativity (`Type i ≤ Type j`) and/or universe polymorphism.

## Stage 2: the extensible parser

```
Wiz/
  Syntax/Basic.lean      untyped Syntax trees (atom / ident / node), SourceInfo
  Parser/Descr.lean      ParserDescr (grammars as data), categories, parser tables
  Parser/Token.lean      scannerless tokens: whitespace, identifiers, strings, symbols
  Parser/Monad.lean      the parser monad: backtracking, farthest error, memo table
  Parser/Interp.lean     the ParserDescr interpreter and the Pratt loop
  Parser/Builtin.lean    the built-in grammar (terms, commands, the grammar of `syntax`)
  Parser/SyntaxCmd.lean  `syntax` declarations → ParserDescr
  Frontend/Parse.lean    command-at-a-time file parsing with error recovery
examples/syntax.wiz      try `lake exe wiz parse examples/syntax.wiz`
```

The surface syntax is Lean-like, with Idris 2 quantities: `def id {0 A : Type} (1 x : A) : A := x`.
`Builtin.lean` documents every node kind and its children. Those shapes are the
contract with the elaborator in stage 3.

| #   | Where                   | What                                                        |
|-----|-------------------------|-------------------------------------------------------------|
| 2.1 | `Parser/Token.lean`     | `skipWs`: whitespace, line comments, nested block comments  |
| 2.2 | `Parser/Token.lean`     | `readIdent` (dotted names), `readStr` (escapes)             |
| 2.3 | `Parser/Token.lean`     | `longestToken`                                              |
| 2.4 | `Parser/Interp.lean`    | `runDescr`: `many`, `many1`, `optional`, `sepBy`, `sepBy1`  |
| 2.5 | `Parser/Interp.lean`    | `Candidate.best` and the Pratt loop `categoryLoop`          |
| 2.6 | `Parser/SyntaxCmd.lean` | `stxToDescr` and `addSyntax`: user-declared syntax          |

Hints:
* 2.4: you'll want helper functions for the loops. Put them inside the `mutual` block,
  since they call `runDescr`.
* 2.5: the trailing loop is easiest as a separate recursive function in the `mutual`
  block that takes the current left-hand side and its precedence.

### Optional extensions to stage 2

* **2.7** Replace the token list with a trie.
* **2.8** Index leading parsers by their first token, so the Pratt loop only tries
  parsers that can start with the next token. This is how Lean keeps longest match
  cheap.
* **2.9** A syntax *formatter* (`Syntax → String`) that round-trips: parsing the output
  gives back the same tree. You'll need it for macro error messages and the LSP.
* **2.10** Ambiguity detection: when two equal-priority parsers tie on length, report
  an ambiguity instead of silently picking the later one, or keep both as a *choice
  node* (as Lean does) and let the elaborator decide.

## Stage 3: the elaborator

```
Wiz/
  Elab/Basic.lean        ElabM, metavariables, the local context
  Elab/Unify.lean        force, partial renamings, pattern unification
  Elab/Zonk.lean         replacing solved metavariables before the kernel sees a term
  Elab/Term.lean         bidirectional elaboration of term syntax, implicit arguments
  Elab/Command.lean      def / axiom / #check / #reduce / syntax
  Frontend/Frontend.lean parse a command, elaborate it, repeat
examples/church.wiz      try `lake exe wiz check examples/church.wiz`
```

The elaborator produces *candidate* core terms and the stage 1 kernel re-checks every
declaration. Metavariables are therefore untyped, and quantity errors come from the
kernel. This follows Kovács' elaboration-zoo (`03-holes`, `04-implicit-args`).

Stage 3 changed stage 1 in three small ways (and stage 4 added universe levels): Π types carry a `BinderInfo`
(explicit/implicit), there is a `Term.mvar` / `Head.mvar` the kernel rejects, and the
pretty printer prints surface syntax.

| #   | Where                | What                                                     |
|-----|----------------------|----------------------------------------------------------|
| 3.1 | `Elab/Unify.lean`    | `force`: unfold solved metas                             |
| 3.2 | `Elab/Unify.lean`    | `invert`: spine → partial renaming                       |
| 3.3 | `Elab/Unify.lean`    | `rename`: with scope and occurs checks                   |
| 3.4 | `Elab/Unify.lean`    | `solve`                                                  |
| 3.5 | `Elab/Unify.lean`    | `unify`                                                  |
| 3.6 | `Elab/Zonk.lean`     | `zonk`                                                   |
| 3.7 | `Elab/Term.lean`     | `insertImplicits`                                        |
| 3.8 | `Elab/Term.lean`     | `check`: implicit lambdas, holes, and the mode switch    |
| 3.9 | `Elab/Term.lean`     | `inferApp`: application, `@f`, and functions of unknown type |

### Optional extensions to stage 3

* **3.10** *Pruning*: solve `?m x y =?= ?n x` by pruning `y` from `?n`. See
  elaboration-zoo `05-pruning`.
* **3.11** Typed metavariables and contextual "could not infer `?A : Type`" messages.
* **3.12** Named arguments `f (A := Nat)`.
* **3.13** Postponement: when a check is stuck on an unsolved meta, such as a lambda
  checked against `?m`, postpone it and retry at the end of the declaration.
* **3.14** Universe level metavariables, so `checkType` always knows the level.

## Stage 4: data

Stage 4 has several steps, each committed separately:

1. **Universe polymorphism** ✅ (below)
2. **Type-directed conversion, Σ / ⊤ / ⊥ with η** ✅ (below)
3. **Observational equality** ✅ (below)
4. **Quantity polymorphism** ✅ and **indexed descriptions, μ / ν** ✅ (below)
5. Surface `inductive` / `structure` ✅ (below); dependent `match`, structural and
   well-founded recursion, and copatterns are next

### 4a: universe polymorphism

`Wiz/Core/Level.lean` has Lean-style levels: `Sort 0` is `Prop` (impredicative),
`Type u` is `Sort (u+1)`, and Π lives in `Sort (imax u v)`. Declarations take level
parameters, `def id.{u} {A : Sort u} (x : A) : A := x`, and uses get fresh level
metavariables (`id`) or explicit levels (`id.{1}`). The level normaliser is
provided. Exercise 1.7's `pi` and `sort` cases now produce `imax` and `succ`.

Metavariables are untyped, so the elaborator records "this hole has type `Sort l`"
for implicit type arguments and type holes. After elaboration it asks the kernel for
each solution's type to solve `l` (`solveSortConstraints`).

| #   | Where              | What                                   |
|-----|--------------------|----------------------------------------|
| 4.1 | `Elab/Unify.lean`  | `unifyLevel`                           |
| 4.2 | `Elab/Term.lean`   | `elabLevel`: level syntax → `Level`    |

Optional:
* **4.3** Write your own level normaliser and compare it with `Level.normalize`.
  Can you make `imax` complete?
* **4.4** Postpone level constraints such as `max ?u ?v =?= 1` instead of failing.
* **4.5** Hide inserted implicit arguments when pretty printing (`id Type`, not
  `id (Type 1) Type`). This needs the binder info of the head's type.

### 4b: Σ, Unit, Empty, and type-directed conversion

Structs are Σ types ending in `Unit`, and the Σ binder names are the field names:
`(x : Unit) × (y : Unit) × Unit` supports `p.y`. Pairs have η (`p ≡ (p.1, p.2)`),
and so does `Unit` (`u ≡ ()`).

η for `Unit` can't be decided without types, so **conversion is now type-directed**
(`conv tys A a b`, `convTy`, and `convNe` for neutrals), and neutral spines hold
general eliminations (`Elim`: application, `.1`, `.2`, `let (x, y) := …`, `absurd`).
These changes landed in stage 1's files. Stage 1's exercises keep their numbers, and
the new constructor cases inside them are labelled 4.3–4.8.

Quantities: `(1 x : A) × B` is a pair whose first field is linear. `p.1` and `p.2`
each use `p`, so a linear pair is consumed with `let 1 (x, y) := p; …`. An erased
field (`(0 n : A) × B`) can't be projected at all.

| #   | Where              | What                                                       |
|-----|--------------------|------------------------------------------------------------|
| 4.3 | `Core/Eval.lean`   | `eval` cases for Σ / pairs / Unit / Empty                  |
| 4.4 | `Core/Eval.lean`   | `vSplit`, `vFst`, `vSnd`                                   |
| 4.5 | `Core/Eval.lean`   | `quote` for the new values and eliminations                |
| 4.6 | `Core/Conv.lean`   | η for pairs and Unit; `convTy` and `convNe` cases          |
| 4.7 | `Core/Check.lean`  | typing rules (in the module docstring)                     |
| 4.8 | `Elab/Unify.lean`  | unification cases                                          |
| 4.9 | `Elab/Term.lean`   | `elabFields`: field access by name                         |

`examples/pairs.wiz` shows it all.

### 4c: observational equality

`a = b` is not an inductive type. It is a proposition that **computes** by the type
of `a` and `b` (Pujet & Tabareau, *Observational Equality: Now for Good*):

| at type          | `a = b` computes to                                  | consequence |
|------------------|------------------------------------------------------|-------------|
| `(x : A) → B`    | `(x : A) → a x = b x`                                | funext      |
| `(x : A) × B`    | `(e : a.1 = b.1) × cast … a.2 = b.2`                  |             |
| `Unit`, `Empty`  | `True`                                               |             |
| `Prop`           | `(a → b) × (b → a)`                                  | propext     |
| `Type u`         | structural equality of types; `False` for different formers | no-confusion |
| a type variable  | stuck                                                 |             |

`cast e t : B` (for `e : A = B`, `t : A`) also computes by the two types.
`transp P p e` transports into propositions, and together they give `J`
(`examples/equality.wiz` derives `subst` and `sym`). Proofs are **definitionally
irrelevant**, so conversion at a proposition always succeeds. **Regularity**,
`cast A A e t ≡ t`, is a conversion rule (not an evaluation rule), which makes `J`
compute on `refl`.

Stuck equations, casts and proofs are new neutral heads (`Head.eq`, `Head.cast`,
`Head.refl`, …). Some results of the computation rules need new binders. Values can't
contain Lean functions, so those are closures over small term templates (see
`vEq` in `Core/Eval.lean`).

| #    | Where              | What                                                     |
|------|--------------------|----------------------------------------------------------|
| 4.10 | `Core/Eval.lean`   | `eval` cases                                             |
| 4.11 | `Core/Eval.lean`   | `vEq`, `vEqType`, `vCast`: the computation rules         |
| 4.12 | `Core/Eval.lean`   | `quote` for the new heads                                |
| 4.13 | `Core/Conv.lean`   | proof irrelevance, regularity, comparing the new heads   |
| 4.14 | `Core/Check.lean`  | typing rules                                             |

Optional:
* **4.15** Quotient types: `A / R` with `Eq (A / R) [a] [b] ↦ R a b`. This is where
  OTT shines.
* **4.16** Make `rfl` work when the expected equation has already computed (for
  example at function types), by recording the original `a = b` alongside its
  computed form.

### 4d (part 1): quantity polymorphism

Quantities are now **terms** of a primitive type `Qty`. A binder annotation is any
quantity term: a literal (`1`, `ω`), or a variable written `%q`.

```
def app {A B : Type} {q : Qty} (f : (%q x : A) → B) (%q a : A) : B := f a
```

Usage vectors hold **polynomials** over the rig in the quantity variables
(`Core/QPoly.lean`), so `a` above is used `q · 1 = q` times. `used ≤ declared` must
hold for *every* value of the variables. For finite rigs that is decided by trying
all assignments (`QRig.elements?`); for infinite rigs only syntactically equal
polynomials are accepted.

So `def keep {q : Qty} (%q x : A) : A := x` is **rejected**: `q` could be `0`, and an
erased variable can't be returned. (Linear Haskell avoids this by having no `0`
multiplicity.) Bounded quantity variables are an optional exercise.

This is what lets descriptions (next) carry field quantities and still have a
`Desc` eliminator: the eliminator abstracts over a field's quantity like any other
argument.

| #    | Where              | What                                                     |
|------|--------------------|----------------------------------------------------------|
| 4.15 | `Core/QPoly.lean`  | `leSymbolic`: `p ≤ q` for every assignment               |

Stage 1 changed shape slightly: binder quantities are `Term`s / `Val`s, `Usage` holds
`QPoly`s, and `Rig` gained `mul_comm`. The constant case of `QPoly.le` is provided,
so stage 1 still only needs `QRig.le`.

Optional:
* **4.16** Bounded quantity variables: `{q : Qty} [1 ≤ q]`, so that `keep` above is
  accepted, with the constraint checked at use sites.

### 4d (part 2): data as descriptions

Inductive and coinductive types are **anonymous**: `μ D i` and `ν D i` for a
*description* `D : Desc I`. Constructors are tags of a finite `Enum`:

```
def NatD : Desc Unit :=
  Desc.arg 1 (Enum [zero, succ]) (fun t => ecase t [Desc.ret (), Desc.rec 1 () (Desc.ret ())])
def Nat : Type := μ NatD ()
def succ (n : Nat) : Nat := con ('succ, n, (), ())
```

| primitive | meaning |
|---|---|
| `Enum [a, b]`, `'a`, `ecase t [b₀, b₁]` | tags (labels are metadata), case on a tag |
| `Desc I`, `Desc.ret i`, `Desc.arg q S D`, `Desc.rec q j D` | descriptions; fields carry quantities |
| `Desc.elim P mret marg mrec D` | the eliminator of descriptions (generic programming) |
| `μ D i`, `con xs`, `ind P m x` | least fixed point, constructor, induction |
| `ν D i`, `coit S step s`, `out x` | greatest fixed point, unfold, observe |
| `Desc.interp D X i`, `Desc.All D X P i xs` | `⟦D⟧ X i` and the induction hypotheses |

`⟦D⟧`, `All`, the hypotheses and `map` are **not kernel primitives**. They are closed
terms built with `Desc.elim` (`Core/Templates.lean`), so on a neutral description
they get stuck as an ordinary `Desc.elim`. The field quantities are what made the
eliminator need quantity polymorphism: `marg` abstracts over the field's `q : Qty`.

Observational equality extends to data: `con a = con b ↦ a = b`, tags compare by
index, and `Enum`s by size. Equality at ν is stuck (a design decision).

A case uses the **join** of its branches' usages (`0 ⊔ 1 = ω`), so a linear variable
must be used identically in every branch. `ind`'s method is scaled by ω, since it runs
once per node. Erased fields can be projected in erased positions (`Ctx.erased`).

`examples/data.wiz` defines `Bool`, `Nat`, addition by `ind` (with a hand-written
"convoy" to branch on the tag, which `match` will generate in stage 4e), and streams.

| #    | Where                  | What                                                     |
|------|------------------------|----------------------------------------------------------|
| 4.17 | `Core/Templates.lean`  | `allTm` (optional: the others are written for you)       |
| 4.18 | `Core/Eval.lean`       | `eval` cases                                             |
| 4.19 | `Core/Eval.lean`       | `vEcase`, `vDelim`, `vInd`, `vOut`: the computation rules |
| 4.20 | `Core/Check.lean`      | typing rules                                             |

### 4e (part 1): `inductive` and `structure`

```
inductive Vec (A : Type) : Nat → Type where
  | nil : Vec A .zero
  | cons {0 n : Nat} (x : A) (xs : Vec A n) : Vec A (.succ n)

structure Point where
  x : Nat
  y : Nat
```

An `inductive` elaborates to `Vec.desc` (its description), `Vec` (a nominal wrapper
around `μ`, with a *display hint* so it prints as `Vec A n`), and constructors
`Vec.nil`, `Vec.cons`, all checked by the kernel. Constructor fields are elaborated
with `Vec` bound as a local variable: a field of type `Vec A j` becomes `Desc.rec`, the
result type becomes `Desc.ret`. Positivity therefore holds by construction, and any
other occurrence is an error. A `structure` is a Σ ending in `Unit` with constructor
`S.mk`.

Every `inductive` also gets Lean-style eliminators `T.rec` (with induction
hypotheses) and `T.casesOn` (`Elab/Recursor.lean`). They are built on `ind`: a
"convoy" `ecase` on the tag, then a `cast` along the constructor's index equation.
In evaluation, `cast A B e t` reduces to `t` whenever `A` and `B` quote to the same
term (cheap regularity), so normal forms stay readable.

`.c` (with or without arguments) is a constructor of the expected type. Applications
containing such arguments are elaborated *expected type first* (`checkApp`), so
`.cons .zero .nil : Vec Nat (.succ .zero)` resolves every constructor. Values print
with their constructor names (`.cons .zero .zero .nil`, including erased fields).

| #    | Where                  | What                                        |
|------|------------------------|---------------------------------------------|
| 4.21 | `Elab/Inductive.lean`  | `ctorDesc`: a constructor's description      |

### 4e (part 2): pattern matching and structural recursion

```
def add : Nat → Nat → Nat
  | .zero, n => n
  | .succ m, n => .succ (add m n)

def head {A : Type} {n : Nat} : Vec A (.succ n) → A
  | .cons x _ => x                      -- the `nil` case is impossible, so it's omitted
```

`match` and equation-style definitions compile to case trees over `T.casesOn`
(`compileMatch` in `Elab/Term.lean`). Later match variables are reverted into the
motive. Index *variables* are generalised by the motive, which is Cockx's solution
rule without an equation. Other indices get an equation `idx_c = ξ`, which
observational equality computes. When it contains `False`, the case is closed
automatically with `absurd`. Recursive calls on a recursive field of the first
argument compile through `T.rec`, and the other arguments may change between calls.

The solution rule *with* an equation is supported too (`tail`, `zip`). When the
computed equation contains `y = t` for a constructor field `y`, the later fields are
re-bound with `y := t`, and the branch is transported back along the equation with
`cast`/`transp`.

Coinductive types and **copatterns**:

```
coinductive Stream (A : Type) where
  head : A
  tail : Stream A

def nats (n : Nat) : Stream Nat
  | .head => n
  | .tail => nats (.succ n)
```

A coinductive type is `ν` of a one-constructor description whose fields are the
observations. Each observation `T.f` is a projection of `out`. A copattern definition
compiles to `coit`: the state is the tuple of the definition's explicit arguments
(implicit ones stay fixed), and each recursive observation must be a corecursive call,
whose arguments are the next state. This is the guardedness check.
`(nats .zero).tail.head` uses generalised field notation (`x.f` is `T.f x` for a
nominal type `T`), which also works on inductives.

Not yet: course-of-values recursion, and well-founded recursion (`termination_by`).

### 4f: sized types

Well-founded recursion and general corecursion are justified by **sizes** (Abel-style),
your choice over `Acc`/`termination_by` and guarded recursion. `μ` and `ν` carry a size:
`Nat^i` is the naturals below depth `i`, and `Nat` is `Nat^∞`.

* Sizes: `Size`, `∞`, `↑s`, and `Size< s` (sizes below `s`). Comparison uses the
  bounds in the context.
* **Subtyping**: `μ^s ≤ μ^t` when `s ≤ t` (and the reverse for `ν`), applied through Π
  and Σ. The kernel's mode switch checks `inferred ≤ expected` (`subTy`).
* `con xs : μ^{↑s}` for a payload at `μ^s`; `out : ν^{↑s} → ⟦D⟧ (ν^s)`; `cocon` builds ν
  values.
* `sfix P f s i x` is recursion where the recursive call takes any `j : Size< s`. It
  unfolds only on constructors.
* `scase P m s i x` is case analysis on `x : μ^s` whose fields live at some `j : Size< s`.
* `scofix` is sized corecursion that unfolds only under `out`.
* Every inductive also gets `T.scasesOn`.

| #    | Where              | What                                                |
|------|--------------------|-----------------------------------------------------|
| 4.22 | `Core/Eval.lean`   | `vSfix`, `vScase` (and the eval cases)              |
| 4.23 | `Core/Check.lean`  | typing rules for `sfix`, `scofix`, `cocon`, `scase` |

Definitions with a sized signature use all of this automatically:

```
def fib {i : Size} : Nat^i → Nat
  | .zero => .succ .zero
  | .succ .zero => .succ .zero
  | .succ (.succ n) => add (fib n) (fib (.succ n))
```

compiles to `sfix`. Inside, `fib` is a local function that only accepts arguments of
a size below the current one, so the termination check is ordinary type checking.
Matching on a sized value uses `T.scasesOn` (fields at a smaller size). A constructor
checked against a sized type gets size `↑m`, where `m` is the size of its recursive
arguments, so `fib (.succ n)` is accepted because `n` is two levels down. Unconstrained
size metavariables default to `∞`.

Limitations: non-indexed types only, recursion on the first argument, and no
as-patterns (size-preserving functions like `minus` want `x@.zero`).

## Stage 5: erasure and the interpreter

```
#eval fib (.succ (.succ (.succ (.succ (.succ .zero)))))   -- .succ (… 8 …)
#erase Vec.cons                                          -- the erased code
```

* **Erasure** (`Compiler/Erase.lean`) is type-directed and bidirectional, like the
  kernel. Types, proofs, sizes, quantities, and everything of quantity `0` become `◾`.
  QTT guarantees the erased parts are never needed. Binders are kept, and an erased
  argument is passed as `◾`.
* **Data at runtime**: a value of `μ D i` is its payload (nested pairs with a tag), and
  descriptions are runtime values. `ind`, `Desc.elim` and the `map` behind
  coiteration are runtime primitives that walk the description.
* **The interpreter** (`Compiler/Run.lean`) is strict, with lazy codata (`coit`,
  `scofix`) that unfolds under `out`. `#eval` reads results back with their type, so
  they print with constructor names.

| #   | Where                   | What                                              |
|-----|-------------------------|---------------------------------------------------|
| 5.1 | `Compiler/Erase.lean`   | `eraseCheck`, `eraseInfer`                         |
| 5.2 | `Compiler/Run.lean`     | `run`                                             |
| 5.3 | `Compiler/Run.lean`     | `ind` (hypotheses) and `out` (coiteration's `map`) |

Next: an ANF intermediate representation with join points and explicit closures,
specialising the primitives for known descriptions (flat constructor objects), and
then macros (stage 6), which run in this interpreter.

## Stage 6: macros

### 6a: macros by example ✅

```
infixl:65 " + " => add
notation "two" => Nat.succ (Nat.succ Nat.zero)
syntax "if" term "then" term "else" term : term
macro_rules
  | `(term| if $c then $t else $e) => `(term| match $c with | .true => $t | .false => $e)
```

* Every syntax category has **antiquotations** `$x`, and every category `c` has a
  **quotation** `` `(c| …) `` as a term (`Builtin.addMetaParsers`, also run for
  `declare_syntax_cat`).
* `macro_rules` match syntax structurally and instantiate templates
  (`Elab/Macro.lean`). `notation` and `infixl`/`infixr`/`infix` register a syntax rule
  and a macro rule together. User command syntax expands too.
* **Hygiene** via macro scopes: identifiers a template introduces become `x✝n`. Locals
  must match exactly, and globals are found with the scope stripped.

| #   | Where              | What                                      |
|-----|--------------------|-------------------------------------------|
| 6.1 | `Elab/Macro.lean`  | `matchPattern`, `instantiate` (hygiene)   |

### 6b: the prelude, literals and procedural macros ✅

```
import Prelude
#eval 100 * 100 * 100 - 1          -- 999999, computed natively
def t : 2 + 2 = 4 := refl 4         -- the kernel computes on literals too

syntax (name := twice) "twice!" term : term
def twiceMacro : Macro := fun stx => do
  e ← MacroM.pure (Syntax.getArg stx 1);
  MacroM.pure `(term| let y := $e; Nat.add y y)
attribute [macro term.twice] twiceMacro
#eval twice! 21                     -- 42
```

* `import M` loads `lib/M.wiz` (and `$WIZ_PATH`). `lib/Prelude.wiz` defines `Bool`,
  `Nat`, `List`, `Option`, `Char`, `String`, `Except`, `Syntax`, `MacroM`, and `do`
  notation (written as macros).
* `builtin key := name` registers prelude definitions with the kernel and the runtime
  (as Agda's `BUILTIN`): `nat` and its constructors and operations, and `string`.
* **Literals.** A numeral of the registered `Nat` is a kernel literal `natLit n`. It
  unfolds one step at a time (`0 ↦ zero`, `n+1 ↦ succ (natLit n)`, `vNatView`) when an
  eliminator, `conv`, `unify` or `vEq` looks inside it. Registered operations compute
  natively on literals (`vBuiltin?`, `vNatOp`), and otherwise fall back to their
  definitions. The runtime uses native numbers that look like their unary payloads
  when inspected (`RVal.nat`, `natView`). Strings are `String.mk [Char.mk n, …]`, and
  `#eval` prints numbers and strings as literals.
* **Quotations in terms** build `Syntax` values (`elabQuote`): identifiers are marked
  `x✝`, and `$x` refers to a local `x : Syntax`.
* **Procedural macros** are Wiz functions `Syntax → MacroM Syntax`, where
  `MacroM A := Nat → Except String (A × Nat)` (a supply of fresh scopes, plus failure).
  `attribute [macro k] f` registers `f` for node kind `k`. Expanding a node compiles
  the environment, encodes the node as a runtime value, runs `f` in the interpreter,
  and decodes the result (`Elab/ProcMacro.lean`). The `x✝` marks then get this
  expansion's scope.
* Antiquotations win ties within their category; `$x:term` picks the other reading.
  `match` alternatives must line up (`colGe`), so a nested `match` ends where the
  outer one's next alternative starts.

| #   | Where                  | What                                              |
|-----|------------------------|---------------------------------------------------|
| 6.2 | `Elab/Term.lean`       | `elabQuote`: a quotation as a term building `Syntax` |
| 6.3 | `Elab/ProcMacro.lean`  | `decodeSyntax`: a runtime value back to `Syntax`  |

### 6c: tactics in Wiz ✅

**Infinitary inductives.** Descriptions gain `Desc.hrec q H j D`, a field
`(h : H) → μ D (j h)`: one subtree per `h`, as in W-types. `Desc.elim` takes a fifth
method, `interp`/`All`/`hyps`/`map` have the obvious extra case, and `All` now lives in
`Sort (max (l+1) v)`. `inductive` accepts fields like `(k : Nat → Tree)`, the recursor's
hypothesis for them is `(x : Nat) → motive (k x)`, and structural recursion accepts
`f (k n)`. `Level.equiv` now decides `imax` by splitting on parameters. The tactic monad
needs all of this: it is a free monad, whose continuations are infinitary fields.

If you have already done exercises 4.17–4.21 (the templates, `vDelim`, description
checking and `ctorDesc`), add the `hrec` cases.

**Tactics** (`examples/tactics.wiz`):

```
def ap : (A B : Type) → (A → B) → A → B := by
  intro A; intro B; intro f; intro a
  apply f
  assumption
```

* `by tac₁; tac₂ …` (or one tactic per line) makes a hole of the expected type and runs
  the tactics on it. Leftover goals are reported with their hypotheses.
* A tactic is a **Wiz function** `Syntax → TacticM Unit`, registered for a `tactic`
  syntax kind with `attribute [tactic k] f`. Tactic syntax can also be macros
  (`rfl` is `exact rfl`).
* `TacticM A := (A → Tac) → Tac`, where `Tac` is an inductive type of **requests** to
  the elaborator, each with a continuation (an infinitary field). The elaborator
  interprets them (`runTac`): goals (`getGoals`, `setGoals`, `goalType`, `goalHyps`),
  `intro`, `exact`, `elabInfer`, `assign`, `newGoal`, `isDefEq`, `normalize`,
  `instantiate`, `inferType`, `evalTactic`, and `catch` (which backtracks the elaborator
  state). Tactic code itself stays pure and deterministic. Macros use the same monad
  (`MacroM := TacticM`, requesting only `fresh` and `fail`), so `do` notation serves both.
* Terms are reflected as `Expr` (de Bruijn variables, constants, closed sorts, Π, λ,
  application, numerals). Every other kernel form is an **opaque handle** that
  remembers its depth, and nominal types are shown by name (`Vec A n`).
* The prelude's tactics: `intro`, `exact`, `rfl`, `assumption`, `apply`, `try`,
  `first | t | u`, `( t; u )`, `repeat`, `trace`.
* Macro and tactic code is erased once, on first use, and only what is reachable
  from them (`compileReachable`; `#eval` does the same).

Also fixed along the way: `elabMatch` zonks the expected type, and `checkApp` keeps the
written arguments (not the placeholders' normal forms) and solves placeholders
without quoting.

| #   | Where                 | What                                               |
|-----|-----------------------|----------------------------------------------------|
| 6.4 | `Elab/Tactic.lean`    | `reflect` and `reify`: terms ↔ `Expr` with handles |
| 6.5 | `Elab/Term.lean`      | `runTac`: the request loop                         |
| 6.6 | `lib/Prelude.wiz`     | `TacticM.findHyp`, for `assumption` (in Wiz!)      |

Next: typeclasses with tabled resolution (stage 7), which also make `do` generic.

## Stage 7: type classes

### 7a: glued evaluation ✅

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

### 7b: classes, instances, tabled resolution ✅

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

## Stage 8: the backend

### 8a: IR and Perceus reference counting ✅

```
#ir twice          -- def twice x0 x1 :=  dup x0;  let x2 := ap x0 x1;  let x3 := ap x0 x2;  ret x3
#run fact 10       -- 3628800, through the IR, on a heap that checks reference counts
```

* **IR** (`Compiler/IR.lean`): A-normal form, first order: objects (`ctor`), fields
  (`proj`), direct calls (`fap`), closures (`pap`/`ap`), native operations (`prim`),
  `case` on tags, join points. Constructors without fields and numbers are unboxed
  scalars.
* **Lowering** (`Compiler/Lower.lean`): lambda lifting, closure conversion, arities,
  join points for non-tail `case`s (closed over their variables). The generic
  eliminators are written in the erased language (`Compiler/PrimCode.lean`) and
  compiled like user code. The output is sorted by name, so it's deterministic.
* **Perceus** (`Compiler/RC.lean`): every variable is owned; `dup` an argument that
  is still needed, and `drop` a variable as soon as it's dead (garbage free).
* **Checked heap** (`Compiler/IRRun.lean`): `#run` runs the IR with explicit reference
  counts and fails on use after free, double free, or leaks. All the examples give the
  same results under `#run` as under `#eval`.

| #   | Where             | What                                     |
|-----|-------------------|------------------------------------------|
| 8.1 | `Compiler/RC.lean`| `insertRC`: Perceus `dup`/`drop`        |

### 8b: C ✅

```
$ wiz run fact.wiz        # def main : Nat := fact 30
265252859812191058636308480000000
```

* `wiz build FILE -o OUT` compiles the definition `main` to C and then to an
  executable; `wiz run FILE` also runs it and reads the printed result back with
  `main`'s type. The C compiler is `$WIZ_CC` (default `cc`), with `$WIZ_CFLAGS` and
  `$WIZ_LDFLAGS` for GMP. The C tests skip themselves if GMP isn't found.
* **Runtime** (`runtime/wiz.c`, embedded in the compiler): a value is a word; scalars
  have the low bit set; objects have a header (reference count, tag, size). Closures
  point to a boxed entry and share or move their captured arguments when applied.
  Numbers that don't fit in 62 bits are GMP integers. Projecting a number gives its
  unary view. The program checks at exit that every object was freed.
* **Codegen** (`Compiler/C.lean`): one C function per IR function (plus a boxed
  version for closures); `case` is a `switch`, join points are labels, `dup`/`drop`
  call the runtime.

| #   | Where              | What                                   |
|-----|--------------------|----------------------------------------|
| 8.2 | `Compiler/C.lean`  | `body`: C statements for an IR body    |

### 8c: reuse ✅

`Compiler/Reuse.lean` pairs each `drop x` with a later allocation in the same block:
`let w := reset x; …; let y := reuse w in ctor t args`. At runtime, if `x` was unique,
its fields are dropped and the new object is written into its cell (if the sizes
match), so updating data you own happens in place. Constructor functions are inlined
when fully applied, so user code takes part. The generic eliminators already reuse
their payload pairs.

| #   | Where                 | What                                          |
|-----|-----------------------|-----------------------------------------------|
| 8.3 | `Compiler/Reuse.lean` | `insertReuse`: pair drops with allocations    |

### 8d: LLVM ✅

`wiz build FILE -o OUT --llvm` and `wiz run FILE --llvm` go through textual LLVM IR
(`Compiler/LLVM.lean`) and `llc` (`$WIZ_LLC`). The runtime is the same C file,
compiled separately with `-DWIZ_API=` so that its functions are exported. In SSA form,
join point parameters live in stack slots, and a variable bound in several branches
gets one name per branch. The LLVM tests are the C tests, through LLVM.

Still to do in the backend: specialise the eliminators for known descriptions (flat
constructor objects instead of nested pairs, direct recursion instead of walking the
description), borrowed parameters, and drop specialisation.

## Stage 9: the C FFI

### 9a: IO, machine types, foreign functions ✅

```
import IO
extern "strlen" (header := "string.h") strlen : String → Nat
def main : IO Unit := do
  IO.println "hello from Wiz";
  IO.println (Nat.toString (strlen "hello"))
```

* `lib/IO.wiz`: `IO A := (1 w : World) → A × World`. The world is a **linear token**:
  QTT's usage checking makes sure every action takes it and gives it back exactly
  once, so effects are ordered and nothing else is impure. (`let 1 (a, w') := …`
  splits linearly; `match` can't, because `ind` uses its methods ω times.) `Monad IO`
  makes `do` work.
* `extern "cname" (header := "h.h")? name : T` declares an axiom implemented by a C
  function. Marshalling follows `T`: `Nat` and `UInt64` ↔ `uint64_t`, `Float64` ↔
  `double`, `String` ↔ UTF-8 `char*`, `Bool` ↔ `int`, `Unit` ↔ `void`; a result in `IO`
  takes and returns the world. The backends emit a C wrapper per foreign function.
  Without a header, a prototype is generated from the Wiz type.
* `UInt64` and `Float64` are axioms whose operations are runtime functions, bound
  with `extern` (boxed raw words at runtime). The kernel doesn't compute with them.
* `wiz run` on `main : IO A` runs it. Foreign functions only run in compiled code
  (`#eval`/`#run` report them).

### 9b: importing C headers ✅

```
import IO
import_c "string.h"            -- C.strlen : String → IO Nat, …
import_c "math.h" (pure)       -- C.pow : Float64 → Float64 → Float64, …
```

`import_c "h"` binds every function of a header whose types can be marshalled, as
`C.name`, in `IO` unless the import is marked `pure`. The command line tool (and the
tests) run the header through `cc -E -P` first, since the frontend is pure. A parser
for a small C subset (`FFI/CParse.lean`) reads the prototypes and the typedefs they
use, and skips struct bodies, inline function bodies and GNU extensions. Variadic
functions and functions taking pointers other than `char*` (or function pointers,
or structs by value) are skipped. On glibc, `string.h` gives 66 prototypes and
`math.h` gives 620.

| #   | Where              | What                                              |
|-----|--------------------|---------------------------------------------------|
| 9.1 | `FFI/CParse.lean`  | `declarator`: pointers, names, parameter lists    |

### 9c: checked C glue ✅

```
import_c "string.h"
glue sumTo (n : Nat) : Nat := "uint64_t s = 0; for (uint64_t i = 0; i < n; i++) s += i; return s;"
glue twiceLen (s : String) : Nat := "return strlen(s) * 2;"
```

A `glue` function's body is C, in a **checked subset** (`FFI/CGlue.lean`): scalar
locals, assignments, `if`/`while`/`for`/`return`, arithmetic and logic on integers and
doubles, strings passed around, and calls to functions from imported headers (with
their types checked). Pointer dereference, address-of, casts, indexing, member access,
`goto`, `asm` and `sizeof` are rejected, so glue can't corrupt memory by itself. The
checked code is emitted into the program, with its headers, and bound like an
`extern`.

| #   | Where              | What                                     |
|-----|--------------------|------------------------------------------|
| 9.2 | `FFI/CGlue.lean`   | `expr`: types of glue expressions        |

### 9d: foreign pointers, finalizers, buffers ✅

```
foreign_type FILE (finalizer := "fclose")
extern "fopen" (header := "stdio.h") fopen : String → String → IO FILE
extern "fputs" (header := "stdio.h") fputs : String → FILE → IO Nat
```

* `foreign_type T (finalizer := "f")` declares an opaque type of C pointers. A pointer
  returned by a foreign function is wrapped in a reference-counted object, and `f` runs
  when the last reference goes. An argument is borrowed during the call and released
  after it. Glue code can pass foreign pointers on but not look inside them.
* `Bytes` (in `lib/IO.wiz`) is a byte buffer whose `push` updates in place when the
  buffer is unique (the same idea as Perceus reuse). It has `IO.readFile` for input.
  Runtime helpers like these take Wiz values as they are (the `w` marshalling kind).

The FFI is complete for now. Not done yet: callbacks (C calling Wiz closures), structs
by value, and mapping more of a header's pointer types onto foreign types automatically.

## Stage 10: effects

### 10a: effects as a library, commutation as proofs ✅

```
import Eff
def prog : Eff (Row.cons (State Nat) (Row.cons (Exn String) (Row.cons Console Row.nil))) Nat := do
  n ← get;
  println "starting";
  put (n + 1);
  Monad.pure n
def main : IO Unit := do
  r ← runConsole (runExn (runState prog 4))
  …
```

* `lib/Eff.wiz`: an `Effect` is a type of operations with an answer type for each, a
  `Row` lists effects, and `Eff r A` is a free monad over the row's operations (its
  continuations are infinitary fields). `Member e r` (two instances, found by
  resolution) injects an effect's operations into a row; `send` performs one.
* Handlers peel the first effect off a row: `runState`, `runReader`, `runExn`, and
  `runConsole` into `IO` at the bottom.
* **Lowering to a monad**: a `Handler e m` for every effect of a row gives
  `interpret : Eff r A → m A`. **Commutation is a proof obligation**:
  `Commute e₁ e₂ m` asks for a proof (kernel-checked, with the OTT equality) that
  swapping two operations doesn't change the result in `m`; `reorder` needs it. Two
  readers commute (the proof is `rfl`); the kernel rejects the same claim for state.
* This needed more of the elaborator: dependent matching now carries induction
  hypotheses through nested patterns; unification got lazy delta (unfold the later
  definition one step), first-order approximation against variables, projections of
  holes, and non-linear spines; description fields may live in smaller universes;
  `Type` takes a universe argument only right of the enclosing position; types get
  their trailing instance arguments.

### 10b: fusion ✅

Effectful code can be written against classes (`MonadState S m`, `MonadReader E m`,
`MonadConsole m`) and run two ways: as a tree of operations (`Eff r`, whose instances
`send` operations to handlers, so resumptions are general), or **fused**, directly in
a monad (`StateT S IO`, `ReaderT E IO`, `IO`), where every operation is a plain call
and no tree is built. In a 200,000-step state loop the fused version is about 4.5×
faster.

```
def prog {m : Type → Type} [Monad m] [MonadState Nat m] [MonadConsole m] : m Nat := …
runConsole (runState (prog : Eff (Row.cons (State Nat) (Row.cons Console Row.nil)) Nat) 0)   -- tree
(prog : StateT Nat IO Nat) 0                                                                 -- fused
```

## Stage 12: towards self-hosting

### 12a (part 1): compiled recursion ✅

* **Direct recursion.** For a structurally recursive definition, the elaborator also
  produces the compiler's version (`Decl.impl`, not checked by the kernel): the same
  equations, with case analysis and the definition calling itself. Only the recursive
  calls the program makes are computed, instead of every induction hypothesis.
* **Case analysis.** `T.casesOn`'s method no longer threads the hypotheses through, and
  erasure applies such a method directly instead of computing them.
* **Stack.** Compiled programs run on a thread with a 1 GB stack (`$WIZ_STACK_MB`), so
  deep non-tail recursion (`sumTo 100000`) works.

Next: the standard library for self-hosting (arrays and hash maps updated in place when
unique, string operations, file IO), flat constructor objects, then porting the lexer
and the parser.

## Stage 11: tooling

### 11a–b: queries and a language server ✅

* **Queries** (`Wiz/Query.lean`): elaboration is a pure function of the text, so each
  command's result is memoised under a **content hash chained through every command
  before it**. After an edit, only the commands from the edit on are elaborated again;
  the same text gives the same result (deterministic builds). The elaborator records
  identifiers with their types and ranges, and each global's declaration site, for
  `hoverAt`, `definitionAt` and `completionsAt`.
* **`wiz lsp`** (`Wiz/LSP.lean`): the Language Server Protocol over stdio, with
  diagnostics as you type, hover types, go to definition (also into `lib/`), and
  completion of global names. Each open document has its own query engine.

### 11c: a shared, content-addressed cache ✅

`wiz check`/`build`/`run` keep each command's **effect** (declarations, messages,
registrations, hovers) in `$WIZ_CACHE` (default `.wiz-cache`; `WIZ_CACHE=off` turns it
off), under the command's chained content hash. A shared directory is a shared cache,
since equal keys mean equal results. Imported modules are cached command by command
too. Commands that change the grammar or the macros rerun (they are cheap).
`Wiz/Cache.lean` serialises terms as S-expressions (quantities through the rig's
literal syntax). Every example gives the same output from the cache as without it.

Next: finer dependencies (re-elaborate only what an edit affects, not everything
after it), and hovers for declarations that fail.
