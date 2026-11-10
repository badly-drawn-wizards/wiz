# wiz

A dependently typed language with quantitative types, built in Lean 4 as a learning
project. The implementation is staged; each stage leaves `sorry`s for you to fill in,
and a test suite tells you when you've got them right.

See [ROADMAP.md](ROADMAP.md) for the stages and the design decisions behind them.

```sh
lake build          # the library and the `wiz` executable
lake test           # all exercise tests; every case runs in its own process
lake test -- conv   # only the groups whose name starts with "conv"
lake test -- =c     # only the group named exactly "c"
lake test -- --list # the group names
```

An unimplemented exercise shows up as `✗ ... not implemented yet (hit a sorry)`.

The design decisions taken so far are listed at the top of [ROADMAP.md](ROADMAP.md).

**Reviewing the core?** [docs/CoreSpec.md](docs/CoreSpec.md) states the kernel's calculus
as inference rules, with the file and line that implements each rule.
[docs/Status.md](docs/Status.md) says what is proved, what is conjectured, and which
soundness issues are known, open and fixed.

## Continuous integration

`nix develop` gives the toolchain the tests need besides Lean (see `flake.nix`): GMP and
LLVM's `llc` for the C and LLVM backends, Boehm GC for the self-hosted backend, a C
compiler, and elan, which installs the Lean in `lean-toolchain`. Entered at the
repository root, it writes this machine's paths to the uncommitted `grail.local.wiz`,
which grail and the test driver read (`Tests/Main.lean`; flags to `lake test -- …` win);
`wiz` takes flags. Nothing reads environment variables.

GitHub Actions (`.github/workflows/ci.yml`) runs on pushes and pull requests to
`solutions` and `master`. Every job runs in that dev shell (with the Cachix cache, when
one is configured); the elan toolchain and `.lake` (including Lake's artifact cache) are
cached between runs.

* **The solution tree** (`solutions`; recognised by its `--<sol` markers) runs the full
  suite in parallel shards, one job per entry of `.github/test-shards.json` (each entry
  is a list of `lake test` selectors). The build job checks that every group of
  `Tests/Main.lean` is in exactly one shard (`scripts/ci.py check-shards`), so **a new
  test group must be added to `.github/test-shards.json`**. Each shard prints a pass/fail
  table in its job summary, and the `CI result` job sums them up for the whole suite.
* **The exercise tree** (`master`) checks that everything builds and that the test driver
  runs to its summary line; the failures are the exercises.
* **The bootstrap fixpoint** (`scripts/fixpoint.sh`: the stage-1 C of the toolchain
  equals its stage-2 C) runs weekly on `solutions`, or from "Run workflow" with
  `fixpoint` ticked. It takes a long time; run it locally with `nix develop -c
  scripts/fixpoint.sh`.
* **The Nix package** (the `nix package` job): `nix build .#wiz` builds `wiz` and
  `grail` with Lake and nixpkgs' Lean (the flake checks that it is the version in
  `lean-toolchain`), and wraps them with the toolchain as flags (`--cc`, `--cflags`,
  `--ldflags`, `--llc`, `--gc-cflags`, `--gc-ldflags`; flags you pass come later and
  win) and, for `wiz`, the packaged standard library as a module root after `./lib`. CI
  pushes it to the public Cachix cache `badlydrawnwizards` on pushes and on pull
  requests from this repository (which have the token). The tests still use Lake, whose
  artifact cache rebuilds only what changed.
* **The Wiz build caches.** Each test shard keeps what the suite builds from Wiz
  programs between runs: the elaboration cache (`lake test -- --cache ~/.cache/wiz …`),
  `.grail`, and the self-hosted checker and compiler that the tests compile
  (`/tmp/wiz-selfhost-*`). The cache key starts with a hash of everything the compiler
  is made of (the `.lean` files, Lean, `flake.lock`), and partial hits only come from the
  same compiler (the elaboration cache's own keys include the wiz binary's hash, but the
  test driver's grail runs use a fixed binary id and the `/tmp` programs a timestamp).

To run Wiz without a checkout or a Lean toolchain, with the binaries from Cachix:

```
nix run --option extra-substituters https://badlydrawnwizards.cachix.org \
  --option extra-trusted-public-keys badlydrawnwizards.cachix.org-1:TxG+RHY8RMC/AXc0LJbYtYm9LW/XRjfQwgz+EEaAjBI= \
  github:badly-drawn-wizards/wiz/solutions#wiz -- check hello.wiz
```

or `cachix use badlydrawnwizards` once and then `nix run
github:badly-drawn-wizards/wiz/solutions#wiz -- …` (`#grail` for grail; `wiz build FILE
-o OUT` works out of the box). Name the `solutions` branch: the default branch, `master`,
is the exercise tree, whose `wiz` is mostly stubs. The `--option`s count only for a
trusted Nix user (or with the cache in `nix.conf`); otherwise Nix builds wiz from source,
which takes a few minutes.

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
each use `p`, so a linear pair is consumed with `let 1 (x, y) := p; …`. `p.2` drops the
first field, so if that field is linear it counts `p` as used ω times (only an
unrestricted pair may drop a linear field); `p.1` drops the second component, which the
projection rule doesn't track. An erased field
(`(0 n : A) × B`) can't be projected at all. Both projections are allowed in erased
positions (`Ctx.erased`).

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
| `(x : A) → B`    | `(0 x : A) → a x = b x`                              | funext      |
| `(x : A) × B`    | `(e : a.1 = b.1) × cast … a.2 = b.2`                  |             |
| `Unit`, `Empty`  | `True`                                               |             |
| `Prop`           | `(a → b) × (b → a)`                                  | propext     |
| `Type u`         | structural equality of types (propositions inside by equivalence; `μ`, `ν`, `Desc` stuck); `False` for different formers | no-confusion |
| a type variable  | stuck                                                 |             |

`cast e t : B` (for `e : A = B`, `t : A`) also computes by the two types.
`transp P p e` transports into propositions, and together they give `J`
(`examples/equality.wiz` derives `subst` and `sym`). Proofs are **definitionally
irrelevant**, so conversion at a proposition always succeeds.

**No regularity (D1).** Regularity, `cast A A e t ≡ t` for *any* proof `e`, would make
`J` compute on `refl` everywhere, but together with an impredicative `Prop` and
irrelevant proofs it makes type checking loop (Abel–Coquand; `Tests/Elab.lean` "D1"). So
it is off (`wiz check --regularity full` turns it back on, for experiments). Instead
`cast` computes on data, constructor by constructor: `μ D i = μ D i'` is `i = i'`, and
`cast (μ D i) (μ D i') e (con x)` casts each field of `x` along it (so a proof field is
cast between propositions, which applies the equivalence: that is what stops the loop).
At **inert** types (first-order data: `Nat`, `Bool`, `List Nat`, … — no `Prop` fields,
functions or type variables) regularity is kept: there a cast between equal types is the
identity. A cast at a type variable (`cast e a` for `e : A = A`) stays stuck, as in
TTobs: `J` computes on `refl` at data types, not at a variable family (docs/CoreSpec.md §8.4).
What regularity said definitionally is available as a proof: the Prelude's axiom
`castRefl : (cast e a : A) = a` (for `e : A = A`). It doesn't compute, it is consistent
(the setoid model), and `#print axioms` shows where it is used.

**Propositions inside types.** Two propositions are equal when equivalent, whatever
their shapes: `True = (True → True)` holds. So equality of types can't compare a
proposition by its shape either, even as the domain of a function type in `Type`:
comparing `(True → Unit) = ((True → True) → Unit)` domain by domain once proved `False`
(`transp` carries the first equation to the second). Type equality first asks each side
whether it is a proposition (`propSort?`): two propositions compare by equivalence, a
proposition and another type are different, and only other types compare by shape. A
`Π` or `Σ` can't tell by itself (`(x : A) → B` is a proposition when `B` is), so it
carries its sort (the elaborator writes it, the kernel checks it); without one, type
equality waits. Surface `Π`/`Σ` get theirs from the levels `checkType` computes; the
ones the elaborator builds itself (a definition's telescope, constructor, recursor and
projection types, a structure's or an index's `Σ`, match motives) get theirs from the
kernel's `typeSort?` in the context they live in (`Sorts` in `Elab/Basic.lean`, applied to
every declaration before the kernel sees it). Only a `Π`/`Σ` under a `fun` whose
variable's type isn't written down, or one that still mentions a metavariable, goes
without. A cast between propositions applies the equivalence.

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
once per node (and so are the methods of `Desc.elim`, `sfix`, `scofix` and `coit`). ω
is the rig's unrestricted quantity (`QRig.many?`); a rig without one, like exact
counting (`Nat`), only lets a method use local variables in erased positions. Erased fields can be projected in erased positions (`Ctx.erased`).

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
"convoy" `ecase` on the tag, then a `cast` along the constructor's index equation
(none for a type without indices). Indexed families also get `T.recN` and `T.casesOnN`,
whose motive is a plain type: they need no cast, and `match` uses them when its result
type depends on neither the indices nor the scrutinee. Without regularity (D1) the cast
in `T.rec` computes on a constructor only through the motive's type: at an inert type
(`Vec.length`) it vanishes, at a type variable (`Vec.map : … → Vec B n`) the fields stay
cast (`cons (cast B B _ (f x)) …`).

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

A copattern definition with **no corecursive observation** is not recursive at all:
it compiles to `cocon`, one cell in front of the values given, and `f` may not occur
on its right-hand sides. That is how a delay is written:

```
def register {A : Type} (init : A) (s : Stream A) : Stream A
  | .head => init
  | .tail => s
```

The same cell as a term is the **coconstructor** `Stream.mk init s` (or `.mk init s`
against a coinductive expected type); `cocon` itself is a data primitive like `con`.
With a sized result type `(Stream Nat)^(↑i)`, the tail is checked at `(Stream Nat)^i`:
`register` is the size bump that guarded feedback needs.
Copatterns keep one syntax for every codata definition (Agda's, and the clause form
Wiz already uses for `match`), so there is no separate `where head := …` notation.
A mix (one recursive observation a corecursive call, another an existing stream) is
still rejected: that needs a state that can be either.

At runtime codata is a lazy cell (`coit`, `scofix`), and the compiled backends
**memoise** observation: `out` on a shared cell overwrites it in place with its payload
(`wiz_lazy_set`, like a forced `memo` thunk), so observing `s.tail` twice computes it
once. A unique cell is about to die, so it is just unfolded; a hoisted constant is not
overwritten. The payload's corecursive fields are always *new* cells built from the
state, never the cell itself, so no cycle forms and reference counting stays exact;
the price is that a stream keeps its observed prefix alive while its root is referenced
(walk it with `s := s.tail` to let the prefix go). A knot is not tied: feedback through
`scofix` (`Signal.fix`) unfolds a new cell per step and stays quadratic. The runtime has
one mutator, as for `memo`; with threads, only shared cells would need a blackhole.
The interpreter (`#eval`) still recomputes. A Mealy machine (`mealy f st i`, state =
its arguments) costs O(1) per step either way.

| #    | Where               | What                                                |
|------|---------------------|-----------------------------------------------------|
| 4.24 | `Elab/Command.lean` | `elabCopatternsCocon`: copatterns without corecursion |

Not yet: course-of-values recursion, and well-founded recursion (`termination_by`).

### 4f: sized types

Well-founded recursion and general corecursion are justified by **sizes** (Abel-style),
your choice over `Acc`/`termination_by` and guarded recursion. `μ` and `ν` carry a size:
`Nat^i` is the naturals below depth `i`, and `Nat` is `Nat^∞`.

* Sizes: `Size`, `∞`, `↑s`, and `Size< s` (sizes below `s`). Comparison uses the
  bounds in the context.
* `∞` is the top size and `↑∞ = ∞`, but `∞` is not below itself. Since every `↑s ≤ ∞`,
  that comparison can't decide `s < ∞` (Agda's `∞ < ∞`, issue #3026, gave `False`). So
  `Size< ∞` holds only sizes built from a bounded variable, `↑ᵏ x` for `x : Size< u`;
  not `∞`, and not a variable of type `Size` (it may stand for `∞`). Running a sized
  function at `∞` is fine: `sfix` takes any `s`, and its recursive calls take sizes below it.
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

* `import M` loads `lib/M.wiz` (and the `-I DIR` roots; `import A.B` is `A/B.wiz`). `lib/Prelude.wiz` defines `Bool`,
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

### 7c: command macros, reflection, `deriving` ✅

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

### 7d: deriving with proof fields and in any universe ✅

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
  description (CoreSpec §4.1, F5 in docs/Status.md); the recursor a deriver eliminates with hands out `down`
  of it, whose type is the field's own, so instance resolution sees `Nat`, not
  `ULift Nat` (tested on a type in `Type 1` with a `Nat` field and a proof field).

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
  `main`'s type. The C compiler is `--cc X` (default `cc`), with `--cflags "…"` and
  `--ldflags "…"` for GMP (stage 23a: flags, not environment variables). The C tests
  skip themselves if GMP isn't found.
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

A cell is often taken apart in one block and rebuilt in another: a tree node is
projected and dropped at once, but the new node is built two `case`s later, after
comparing keys. So `reuseAcross` runs first and follows a dropped cell into the
branches (as Perceus and Lean 4 do): the `reset` stays where the drop was, each branch
that builds an object reuses the token, and the others free it at once
(`reuse w in ctor 0`, which needs no cell). The IR has no types, and a `Bool` returned
by a function has no cell to give, so only variables known to be objects (projected
from, or built) go across, outermost first; the local pass pairs what is left. A
zipper's insertion loop then allocates nothing per level.

| #   | Where                 | What                                          |
|-----|-----------------------|-----------------------------------------------|
| 8.3 | `Compiler/Reuse.lean` | `insertReuse`: pair drops with allocations    |

### 8d: LLVM ✅

`wiz build FILE -o OUT --llvm` and `wiz run FILE --llvm` go through textual LLVM IR
(`Compiler/LLVM.lean`) and `llc` (`--llc X`). The runtime is the same C file,
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

### 12a (part 2): a standard library for systems code ✅

`lib/Std.wiz`: `Array A`, native text `Str` (UTF-8, with slicing and comparison), and
`StrMap V` (hash maps from text), all functional but **updated in place when unique**
(as Perceus reuse does for constructors). Plus `IO.writeFile`, and `do let x := e; …`.
Foreign functions can now take erased arguments (`{A : Type}`) and pass Wiz values as
they are.

### 12b: the lexer in Wiz ✅

`selfhost/Lex.wiz` reads tokens at an offset of the input (an array of code points),
like `Wiz/Parser/Token.lean`: whitespace and nested comments, dotted identifiers,
numbers, string literals with escapes, and the longest symbol of the token table. The
test lexes a program with the full built-in token table and compares with the Lean lexer.

| #    | Where              | What                                          |
|------|--------------------|-----------------------------------------------|
| 12.1 | `selfhost/Lex.wiz` | `longest`: the longest token at an offset     |

### 12c: flat constructor objects ✅

A data value is one object `⟨tag f₁ … fₙ⟩` at runtime instead of a tag and a chain of
pairs (lists stay linked lists; `Array` stays a vector). Erasure builds constructors
directly and resolves case analysis to field reads (**views**); generic code (`ind`
with hypotheses) converts with `pack`/`unpack`, which walk the description. Numbers stay
native. Redexes become `let`s, and scalars get no reference counting.

### 12d: the parser in Wiz ✅

`selfhost/Parse.wiz` interprets the grammar descriptors (`ParserDescr`) like
`Wiz/Parser/Interp.lean`: Pratt parsing of syntax categories, the longest alternative
wins, and category parses are memoised (packrat) in a `StrMap`. The test turns
`Builtin.tables` into Wiz data and compares the trees (and errors) with the Lean parser.

| #    | Where                | What                                                   |
|------|----------------------|--------------------------------------------------------|
| 12.2 | `selfhost/Parse.wiz` | `runDescr`: `many`, `many1`, `optional`, `sepBy(1)`    |
| 12.3 | `selfhost/Parse.wiz` | `trailingLoop`, `manyLoop`, `sepLoop`                  |

Along the way: induction on a big numeral is lazy in the kernel (`Val.lazyInd`, glued,
so fuel arguments like `100000000` cost nothing), constructor fields no longer shadow
variables in `match` alternatives, and reuse only recycles constructor cells.
`WIZ_LEAKS=1` lists the objects a compiled program leaks (`WIZ_WATCH=<address>` traces
one).

## Stage 13: the language, for programs this size

Writing the lexer and parser in Wiz showed what the language lacked:

* **Recursion on any argument.** The structural argument is the first one the first
  clause matches; parameters before the colon may be passed unchanged or left out.
* **`partial def` and `mutual … end`.** General recursion: the kernel treats the
  definition as an axiom (its type must be visibly inhabited, so no `False`), and its
  implementation (checked against the type) is what `#eval` and compiled code run. The
  parser's core is a mutual block, with no fuel.
* **Mutual inductive types.** `mutual inductive A … inductive B … end` becomes one
  family indexed by a tag type, `A_B : A_B.Tag → Type`, with `def A := A_B .A`.
  Recursion over a family at a concrete index (`SyntaxF .false`) works.
* **`match` without an expected type**, **tuple patterns** `(a, b, c)`, and `x |> f`.
* Keywords of tactic syntax (`first`, `exact` …) are no longer reserved words.
* The prelude has `Nat.lt` (native at runtime), `Nat.le`, `Nat.max`, `Bool.and/or/not`.

## Stage 14: the kernel in Wiz

### 14a: a type checker ✅

`selfhost/Kernel.wiz`: normalisation by evaluation for a core calculus (variables,
universes, Π, λ, application, `let`, ascription), with values and environments mutually
inductive (closures), and bidirectional checking.

| #    | Where                 | What                                    |
|------|-----------------------|-----------------------------------------|
| 14.1 | `selfhost/Kernel.wiz` | `eval`, `vapp`                          |
| 14.2 | `selfhost/Kernel.wiz` | `quote`                                 |
| 14.3 | `selfhost/Kernel.wiz` | `infer`, `check`                        |

### 14b–c: from text to checked definitions ✅

`selfhost/Frontend.wiz` scope-checks Wiz syntax (identifiers, `Type n`, Π and arrows,
`fun`, application, `let`, ascription) into the kernel's terms, and processes a file of
`def`, `#check` and `#reduce` commands, the globals being the kernel's constants (each
command is checked in the empty context). Lexer, parser, scope checker and type checker all run as compiled Wiz.

| #    | Where                   | What                                     |
|------|-------------------------|------------------------------------------|
| 14.4 | `selfhost/Frontend.wiz` | `elab`: names to de Bruijn indices       |
| 14.5 | `selfhost/Frontend.wiz` | `command`: one command                   |

### 14d: differential testing ✅

Conversion in the Wiz kernel compares values, with η for functions, like `Conv.lean`.
A test generates 300 pseudo-random closed terms, checks each with both kernels (the
Lean kernel through the same terms, quantities `ω`), and requires the same verdict and
the same inferred type.

| #    | Where                 | What                                    |
|------|-----------------------|-----------------------------------------|
| 14.6 | `selfhost/Kernel.wiz` | `conv`: values, with η                  |

### 14e: Σ types ✅

Pairs, projections and Σ types in the Wiz kernel, with η for pairs (`p` and `(p.1, p.2)`
are convertible); neutral values carry a spine of eliminations (`Val`, `Env` and
`Spine` are mutually inductive). The differential generator mixes in well-typed pairs,
so its 400 terms exercise them. Exercises 14.1–14.3 and 14.6 now include Σ.

### 14f: finite types ✅

`Unit n`, `Empty n` (with `exfalso`), and enumerations of `k` tags with case analysis
(a motive under a binder; a stuck case is an elimination in the spine). Terms are now a
mutual inductive (`Tm` and its lists `Tms`). The generator adds them, often
well-typed (cases returning tags), and both kernels agree on all 400 terms.

### 14g: `Prop`, and conversion at a type ✅

`Prop` (`Sort 0`) with impredicative Π (`imax`), `True` and `False`, and conversion
**at a type** like `Conv.lean`: all proofs of a proposition are equal, functions and
pairs are compared by η, types structurally, neutrals by their eliminations at their
types (computed from the variable's type, `typeOfNe`). Exercise 14.6 is now typed.
(Also fixed: the index-equation binder of a match could shadow a variable `e`.)

### 14h: observational equality ✅

`a = b` and `A = B` compute by type, as in `Eval.lean` (with the same closure templates):
pointwise for functions, componentwise (with a cast of the second component) for pairs,
`True`/`False` for tags, logical equivalence for propositions. `cast` computes by the
two types, and `refl`, `reflTy`, `transp` are proofs. A neutral now has a **head**: a
variable, or a stuck equality, cast or proof. (In the Wiz source the constructors are
`eqRefl`, `tyRefl`, `coe` and `subst`: `refl`, `cast` and `transp` are keywords.) The
differential generator adds equalities and their proofs, often well-typed.

(Checking the Wiz kernel had become slow, 24 seconds. A profile showed the cause: the
inhabitedness check for partial definitions evaluated the type of every global, for
each definition. It now looks only at constants whose type visibly ends in the right
type: 3 seconds.)

### 14i: descriptions and data ✅

Descriptions (`descr l I` for `Desc.{l} I`, with `ret`, `arg`, `rec`, `hrec`),
`Desc.elim`, `μ D i` and constructors, as in the Lean kernel: `⟦D⟧ X i` is the same
`interpTm` template, written with `Desc.elim`, and `con x = con y` is equality of the
payloads. This kernel has no quantities: where the templates take one, it passes `tt`
(and the method types bind it at `Unit`). The differential test now always checks a
list of samples first (the natural numbers, constructors, `Desc.elim` into `Unit`,
ill-typed payloads), then the random terms.

### 14j: induction ✅

`ind` on `μ D i`, with the motive and method types of the Lean kernel and the `All`
and hypotheses templates (`allTm`, `hypsTm`, the same `Desc.elim` terms): on a
constructor, the method gets the payload and the induction hypotheses; on a variable
it is stuck. The samples check that it computes (`tt : ind … 1 = #1` checks, and
`= #0` doesn't) and agree with the Lean kernel.

The Wiz kernel now covers the Lean kernel's dependent types, equality and data, apart
from quantities, sizes, coinduction, globals and universe polymorphism.

### 14k: global constants ✅

A global definition is a term `const name value type` that carries its (closed) value
and type, shared rather than looked up in a table; an axiom is `axiomC name type`.
Definitions are **glued** as in the Lean kernel: a constant applied to arguments keeps
its name and spine together with its unfolding, quotation keeps the name, conversion
compares two applications of the same constant by their arguments before unfolding
(lazy delta), and `whnf` looks through them before matching on a value's shape. The
differential test builds the same globals in the Lean kernel (with `addDecl`) and
uses them in samples and random terms.

### 14l: universe polymorphism ✅

Levels in terms are expressions over level parameters (`Lvl`: numerals, parameters,
successor, `max`, `imax`), and `Sort l` takes any of them. A universe-polymorphic
constant carries its parameters and the levels it is used at; using it substitutes the
levels into its definition (`tmSubst`) before evaluating. Every term the kernel
evaluates is closed, so values only ever see numeric levels. (Checking a polymorphic
definition itself, with symbolic level equivalence, comes with checking declarations.)
The differential test adds polymorphic globals (`idP.{u}`, `constP.{u v}`) used at
various levels.

### 14m: quantities ✅

Binders carry a quantity (`0`, `1`, `ω`: `piq`, `sigmaq`, `letq`; the plain forms are
`ω`), and every judgement returns a **usage vector**, as in `Check.lean`: a variable
counts once, an application adds its argument's usage scaled by the binder's
quantity, leaving a binder checks its variable's usage against the quantity, case
branches join, and types and proofs count nothing (erased positions, where an erased
field may also be projected). The kernel's own templates use the Lean kernel's
quantities (equations and indices are erased), and printing shows `:0` and `:1`.
The differential test adds linear and erased binders, in samples and at random.

### 14n: sizes and subtyping ✅

`Size`, `∞`, `↑s`, `Size< s`, and `μ D i` at a size (`∞` by default); a constructor
builds a value of size `↑s` from fields at `s`. Checking falls back to **subtyping**
(`subTy`, exercise 14.7) as in the Lean kernel: data types are covariant in their size
(`sizeLe`, which uses a variable's `Size< u` bound), functions contravariant in their
domain (and may differ in quantity when they are propositions), pairs covariant.

### 14o: sized recursion ✅

`sfix` (recursion whose function takes a smaller size `Size< s`) and `scase` (case
analysis giving the fields at the predecessor size), with the method types computed
from the description as in the Lean kernel (`sfixFunTy`, `scaseMethodTy`). Both reduce
on a constructor; the recursive function is used ω times. The differential test checks
that they compute, and that the index can't be returned (it is erased).

### 14p: coinduction ✅

`ν^s D i`, `out`, `cocon`, coiteration (`coit`) and sized corecursion (`scofix`), as
in the Lean kernel: unfoldings compute only when observed (`out` re-wraps the recursive
fields with the `map` template), only a value of size `↑s` or `∞` can be observed, and
`ν` is contravariant in its size. Unfoldings are compared structurally (there is no
bisimulation). The differential test observes streams built both ways.

The parser got a per-offset token cache (each alternative used to re-lex, scanning the
whole token table) and no longer shares its memo table with candidate states (each
store copied the table): `Kernel.wiz` now checks in a third of the time.

Compiling the kernel (which the self-hosting tests do) had grown to 8 minutes. A
catch-all row of a multi-column `match` is copied into every leaf of the split, so
`checkW`'s now calls a helper (`checkByInfer`); and erasure no longer asks the kernel's
full `infer` for the type of each subterm (which re-checked every subterm once per
enclosing node) but follows the elimination spine (`Erase.quickType`). Now 37 seconds.

### 14q: declarations at symbolic levels ✅

Values carry symbolic levels (`vsort (l : Lvl)`), compared as in `Level.lean`: normal
forms are sorted lists of `atom + k` (exercise 14.8, `lvlNorm`), and when an `imax`
keeps them apart, `lvlEquiv` splits on the parameter it depends on (`p = 0` or
`p = p + 1`). `checkDecl` checks a declaration with its parameters symbolic, so at
every level at once. A differential test checks declarations, and 200 random level
puzzles (`Sort a : Sort b`, Π's of sorts; the true ones made by rewriting with
identities), against the Lean kernel's `addDecl`. (The Lean kernel also rejects unknown
or duplicate level parameter names; this one doesn't look.)

The Wiz kernel now covers the Lean kernel's calculus.

The `match` compiler now shares a large catch-all last row of a multi-column match: it
is elaborated once, as a local function `dflt✝` of the scrutinees, and the row calls it
(falling back to copying when the right-hand side doesn't check without what the other
rows learnt).

## Stage 15: performance for self-hosting

### 15a: lazy unfolding ✅

`memo : (Unit → A) → Unit → A` (Prelude, `builtin memo`) is a memoised suspension. To
the kernel and the interpreters it is the identity; compiled code makes it a thunk
object (`WIZ_TAG_THUNK`) that `wiz_apply` runs at most once, keeping the result. The
Wiz kernel's glued values now hold their unfolding as `Unit → Val` built with `memo`, as
the Lean kernel's `Val.unfold` holds a `Thunk`: a global is unfolded only when `whnf`
looks through it, and once. Checking a term that mentions a large global 300 times
(without needing its value) went from 206 s to 1 s.

(`whnf` recurses into the forced unfolding: structural recursion through a function
field. For a mutual family, that field's induction hypothesis wants the index equation
after the field's argument; the recursive call now supplies it, as `fun h => ih h
proof`.)

### 15b: the self-hosted pipeline, measured ✅

A benchmark checks a file of 300 definitions (and one of 3000) with the self-hosted
pipeline compiled to C, against the Lean-hosted `wiz check`. At first the self-hosted
one took 1.5 s (and 32 s, so quadratic) against 0.08 s (0.68 s). Profiling the compiled
program with `gprof` (`WIZ_CFLAGS=-pg`):

* the parser spent nearly all its time reading tokens, each read trying every token of
  the table: the context now keeps the table by first character (`tokenBuckets`), and
  a candidate no longer shares the memo table with the live state;
* globals were variables of the typing context, so every command rebuilt it, and every
  usage vector and name lookup grew with the number of globals: they are now the
  kernel's constants (checked in the empty context, unfolded lazily since 15a), found
  by name in a `StrMap` (`Scope`), and kept in an `Array`.

Now 0.25 s (2.4 s): linear, within 3–4× of the Lean-hosted checker. The profile is flat;
the largest share left is reference counting (about 1.4 billion `inc`/`dec` for the
3000 definitions). Two things tried and left out:

* *borrow inference* as a pass around `insertRC` (parameters never consumed are
  borrowed; calls and boxed wrappers fixed up afterwards) removed only 4% of the
  `inc`s, and cost 12% more allocations, since a borrowed cell can't be reused. The
  gain needs borrowed *projections* and reuse-aware inference inside `insertRC`
  itself;
* `ap` of a known partial application: closures are applied only about a million
  times here.

Next: fewer index equations for mutual families (elaboration time and code size).

## Stage 16: data in the self-hosted frontend

### 16a: inductive types ✅

`selfhost/Frontend.wiz` reads `inductive T where | c (x : A) (y : T) …` (no parameters
or indices yet, in `Type`): `T` becomes the constant `μ D tt` for the description

    D := darg (Enum k) (fun t => ecase t [D₁, …, Dₖ])

with one `Dᵢ` per constructor (exercise 16.1, `ctorDesc`: a field `(x : A)` is
`darg A (fun x => …)`, a field of type `T` is `drec tt …`, the end is `dret tt`), and
each constructor `T.c` the constant `fun fields => con (tag, fields…, tt, tt)`. The
Wiz kernel checks all of them.

| #    | Where                   | What                                     |
|------|-------------------------|------------------------------------------|
| 16.1 | `selfhost/Frontend.wiz` | `ctorDesc`: a constructor's description  |

### 16b: pattern matching and structural recursion ✅

`def f (ps) : R := match x with | .c a b => rhs …`, for a parameter `x` of an inductive
type (and `R` not mentioning `x`), becomes induction with the motive `fun i y => R` and
the method

    fun i xs ih => (ecase (fst xs) [b₁, …, bₖ] : convoy) (snd xs) ih

where each branch `bᵢ := fun rest ih => let fields := …; let hyps := …; rhs` (exercise
16.2, `branchTm`) names the payload's fields and the recursive fields' induction
hypotheses; a recursive call `f … y …` on a recursive field `y`, the other arguments
unchanged, is `y`'s hypothesis. A catch-all `x =>` stands for the missing
constructors. The convoy's types apply the `interp` and `All` templates, which the
frontend normalises first (`nfAt`: the kernel can't infer the type of an applied λ).

| #    | Where                   | What                                     |
|------|-------------------------|------------------------------------------|
| 16.2 | `selfhost/Frontend.wiz` | `branchTm` (16e: `specialize`)           |

### 16c: parameters ✅

`inductive List (A : Type) where | nil | cons (head : A) (tail : List A)`: the
description lives under the parameters (`List` is `fun A => μ D[A] tt`), a field of type
`List A` (the type applied to its own parameters) is recursive, and the constructors take
the parameters first (the self-hosted frontend has no implicit arguments yet:
`List.cons Nat x xs`). A match on `l : List A` instantiates the description and the
field types with the scrutinee type's arguments, again by normalising
(`(fun ps => D) args`) rather than substituting.

### 16d: equations ✅

`def f (ps) : A → R | p => rhs …` (one pattern per alternative) is read as
`def f (ps) (x✝ : A) : R := match x✝ with | p => rhs …` (`eqnsToMatch`, on the syntax
tree; `(x : A) → R` names the parameter).

### 16e: several scrutinees and nested patterns ✅

The match compiler now works column by column, as `compileMatch` in `Term.lean`: split on
the first column where the first clause has a constructor pattern (an `ind` with the
constant motive), replacing that column by the constructor's fields in each branch
(exercise 16.2, `specialize`: the clauses that remain, with their sub-patterns); a leaf
binds its variables with `let`s. The first split is on the structural column (the
leftmost one any clause matches): its method runs for the induction hypotheses too, so
the parameters after it are generalised in its motive (and bound again in each branch:
a recursive call may change them), and a variable for the column is the value at hand
(`cur✝ := con (tag, rest)`). Equations take several columns. The Wiz kernel got the
Lean kernel's check rule for `let`.

That last point was also wrong in the Lean elaborator since the scrutinee change above:
a catch-all variable of a recursive definition stood for the original argument in the
kernel's term (only `#eval`, which runs the `casesOn` implementation, was right). Now it
is the constructor at the recursor's split.

| #    | Where                   | What                                     |
|------|-------------------------|------------------------------------------|
| 16.2 | `selfhost/Frontend.wiz` | `specialize`: the clauses for a constructor |

Next: indices, implicit arguments (which need metavariables in the self-hosted
frontend).

## Stage 17: elaboration in the self-hosted frontend

### 17a–b: implicit arguments ✅

The self-hosted frontend now elaborates with types (`inferT`/`checkT` in
`Frontend.wiz`), so `{A : Type}` binders work: `List.cons x xs`, `id Nat.zero`,
`map f l`. A metavariable `?mN` is the kernel's opaque constant (`axiomC`) of type
`Π Γ. A`, applied to the variables of the context `Γ` it was made in, so the kernel needs
nothing new; unification (`unify`) solves `?mN Γ =?= t` when `t` lives in `Γ`
(`lowerTm`, with an occurs check), compares Π types and spines structurally, and leaves
the rest to the kernel's conversion. Before the kernel checks a definition, the
solutions are put in (`zonk`). A global records which of its parameters are implicit:
`{…}` binders, and an inductive type's parameters in its constructors.

The match compiler elaborates its right-hand sides with types too: it keeps the typing
context of its binders (the method's `i`, `xs`, `ih`, the payload, the fields, the
hypotheses, `cur✝`, the generalised parameters) alongside their names, and the expected
type as a value (at the structural split, the generalised motive's body, peeled as the
later parameters are bound again). Recursive calls leave out the implicit parameters.
Typed elaboration produces constants, so for `#reduce` the definitions are inlined
afterwards (`inlineTm`) instead of being compiled twice.

### 17c: `.c` and `@f` ✅

A constructor can be written `.c` (or `.c a b`) where the expected type is `T …`: it is
`T.c`. An argument written so whose type is still an unsolved metavariable (the `.zero`
in `.cons .zero xs`, before `xs` fixes the list's type) is postponed: a metavariable
stands for it until the other arguments are elaborated, then it is checked and unified
with that metavariable. `@f` inserts no implicit arguments.

### 17d: `partial` and `mutual` ✅

`partial def` and `mutual … end` blocks of definitions: each function is first an axiom
of its type (`addAxioms`), so that the bodies may call any of them, as the Lean kernel
sees partial definitions; then each body is checked as usual and replaces the axiom.

## Stage 18: more data in the self-hosted frontend

### 18a: indexed families ✅

`inductive Vec (A : Type) : Nat → Type where | nil : Vec A Nat.zero | cons (n : Nat)
(a : A) (v : Vec A n) : Vec A (Nat.succ n)` (one index): the description's index type
is `Nat`, a recursive field `Vec A j` is `drec j`, a constructor ends in `dret i` for
its result's index `i` (exercise 16.1 now takes the index), and its payload ends in the
proof `refl I i`. `Vec` is `fun A i => μ D i`. A match on `v : Vec A n` runs induction at
`v`'s index, with the index type in the method's binders, the convoy's templates and
`cur✝` (whose index is the method's). The motive is still constant, so a match needs a
case (or a catch-all) for every constructor, even one the index rules out.

Elaboration got two things this needed: an application checked against a type unifies
its result type with it before the postponed `.c` arguments are done, and an argument
whose type is still unknown at the end of its application waits in the elaboration state
until the whole definition is elaborated (`drain`).

### 18b: index equations ✅

When the scrutinee's index is closed (`Vec A (Nat.succ Nat.zero)`, or a tag), the motive
also takes the equation `e :0 i = idx` (and the `ind` gets `refl`). A constructor no
clause covers is then ruled out if the index makes it impossible: its payload proves
`i_c = i`, carried along `e` (`subst`) that is `i_c = idx`, which OTT computes to
`False` (or to `False × …`, projected) when the two differ, so the branch is `exfalso`.
A hypothesis for a recursive field with that same index is applied to `refl` already.
The parameter and result types of a match are now elaborated with types too.

### 18c: mutual inductive types ✅

`mutual inductive Tm … inductive Tms … end` (no parameters or indices yet) is one
family `Tm_Tms : Enum 2 → Type` over every member's constructors: a field whose type is
a member is recursive at that member's tag, and a member's constructors end at its tag.
Each member is the constant `Tm := Tm_Tms (tag 0)`, and its constructors `Tm.c` build
the family's values. A match on a `Tm` runs at a closed index, so 18b rules out the
other members' constructors: a match lists only its own type's.

### 18d–e: parameters for mutual types; structures ✅

The members of a mutual block share their parameters (the first member's): the family
is `fun ps i => μ D i`, a member `A := fun ps => A_B ps (tag j)`, a field `A ps` is
recursive, and constructors take the parameters implicitly (`Tree`/`Forest A`).

`structure T (ps) where f : A …` is read, on the syntax tree, as the inductive type
`T (ps) where | mk (f : A) …` and one projection `T.f {ps} (s : T ps) : A` per field,
defined by `match`. `x.f` (and `(e).f`) is `T.f x` for `x : T …`. (A field's type may
not mention an earlier field yet.)

### 18f–g: numerals; `match` as a term ✅

A numeral `n` is `Nat.succ` applied `n` times to `Nat.zero` (the kernel has no number
literals), and in a pattern `0` is `.zero` and `n + 1` is `.succ n`. `match` can now
appear anywhere a term is checked: its scrutinees are `let`-bound and its clauses
compiled against the expected type, by the same compiler (so the elaborator and the
match compiler are now one mutual block). Only a definition's own match recurses, and
a recursive call may change only the parameters after the structural one: `lt m' n'`
inside a nested `match m` under `match n` is rejected, `| succ m, succ n => lt m n`
is fine.

### 19a: a Prelude, `if`, strings ✅

`import Prelude` checks a small Prelude (written in the subset itself, kept as a string
in `Frontend.wiz`) before the file: `Nat`, `Bool`, `List`, `Option`, `Prod`, `Char`
(a structure over its code) and `String` (a structure over a `List Char`), with
arithmetic, comparisons, the Boolean connectives and a few list functions. `if c then a
else b` is a `match c` with `.true`/`.false` clauses; a string literal is `String.mk`
of a list of `Char.mk` numerals. A definition whose `match` scrutinises something other
than its parameters (`match s.data with …`) is compiled as a `match` term.

Only the structural split of a match needs induction; the other splits are now case
analysis (the kernel's `scase` at `∞`, whose method sees the payload at `μ^j D i` for a
size `j`). Computing induction hypotheses nobody uses made nested matches exponential:
`Nat.beq 14 14` took 0.7 s, `Nat.beq 65 65` now takes 0.17 s.

### 19b: infix operators ✅

`infixl:65 " + " => Nat.add` (and `infixr`, `infix`) extends the self-hosted parser
while it runs: a trailing `term` parser `a + b` at the declared precedence, and the
token `+`. Each later command is expanded before it is elaborated, `a + b` standing for
`Nat.add a b`, like the Lean side's macro rule. The Prelude declares `+ - *` and `++`;
in a pattern, `n + 2` is `.succ (.succ n)`. **Exercise 19.1** is `infixCmd`, the new
parser entry and notation.

### 19c: axioms, `IO`, `do` — the frontend checks `Lex.wiz` ✅

`axiom f (bs) : T` and `extern "c_name" f : T` (a foreign function is an axiom to the
checker) declare constants. `Unit` and `()` are built in. The Prelude declares `Array`
and its operations as axioms, and `IO A := World → Prod A World` with `IO.pure`,
`IO.bind` and the axioms `IO.println`, `IO.readFile`. `import Prelude` also adds the
`do` grammar to the parser's tables (there are no type classes, so `do` is for `IO`
only): `x ← e; rest`, `e; rest` and `let x := v; rest` expand to `IO.bind`. A `let`
may now leave out its type (the value's inferred type is used).

With these, the self-hosted frontend checks the first file of its own source,
`selfhost/Lex.wiz` (every declaration, no errors; about 18 s).

### 19d: `Syntax`, `StrMap` — the frontend checks `Parse.wiz` ✅

The Prelude adds the syntax trees (`SyntaxF : Bool → Type` and `Syntax := SyntaxF
.true`, with `getArg`), `Nat.toString`, and `Str`/`StrMap` as axioms. Three gaps
closed on the way:

* a type that is a definition (`Syntax`) is unfolded where an inductive type is
  needed: for `.c` (`dotName`), for a match (`unfoldTy`), and in unification, which
  unfolds one definition at a time before comparing whole values (`SyntaxF ?b =?=
  Syntax` solves `?b := .true`);
* in an indexed family, the index `.c` of a constructor's result type is `I.c` (the
  constructors are scope-checked, not typed);
* a metavariable's solution may contain projections and pairs (`lowerTm`): the fields
  of a pattern are projections of its payload, so `.some (.mk n l)` inside a branch
  needs them.

The self-hosted frontend now checks `Lex.wiz` and `Parse.wiz` together (96
declarations, about 20 s).

### 19e: towards `Kernel.wiz` ✅

* A field `(v : Unit → Val)` of a mutual type is higher-order recursive: `dhrec H (fun _
  => tag j) D` in the description.
* Induction only where it is needed: a definition's match uses `ind` only when the
  definition calls itself and isn't partial (a partial definition calls its axiom);
  every other split is case analysis. This also avoids building hypotheses for
  function fields.
* A catch-all at the structural split of a mutual member (a closed index, 18b) used to
  bind the variable to `con (tag, rest)` at the method's index; it is now moved to the
  scrutinee's index with `coe` along `F i = F idx` (obtained by `subst` from `tyRefl`),
  so `| t => t` has the right type.
* `Unit` in constructor fields, `fun _ => …`, and `Nat.max` in the Prelude.

### 19f: the frontend checks `Kernel.wiz` ✅

* **Big numerals**: a numeral is `Nat.succ` applied `n` times, so `quote 100000 A` in
  the kernel was a term 100000 deep. With `Nat.mul` around, a numeral of 16 or more is
  built in binary (`2 * (n / 2)`, plus `succ` when odd).
* **Recursion through a function field**: `whnf (v ())` with `v : Unit → Val`. The
  hypothesis for such a field is a function, `(h : H) → P (j h) (v h)` (pre-applied to
  `refl` in mode B), and a recursive call on `v a` becomes `ih a`.
* **The structural parameter first**: when a recursive call changes a parameter before
  the structural one (`tApps (.app f a) rest`), `f` is defined through `f✝s`, with the
  structural parameter moved to the front, so the others are generalised in the motive.
* **A shared catch-all**: a big last clause of variables in a match that only does
  case analysis is checked once as a definition `f✝d`, and the leaves call it, instead
  of copying it into every leaf.
* `memo` in the Prelude.

The self-hosted frontend now checks `Lex.wiz`, `Parse.wiz` and `Kernel.wiz` (272
declarations, about two minutes). Next: `Frontend.wiz` itself.

### 20a: towards `Frontend.wiz` ✅

* A `match` or `fun` argument whose expected type is still a metavariable waits, like
  a `.c` one (`.cons (match s with …) rest`), and a postponed argument's metavariable
  takes any term at its own depth (a `match` elaborates to `let`s and `scase`).
* A `match` or `if` without an expected type (`let x := match …`) is checked against a
  new metavariable; `fun (x : A) => b` with typed binders infers `(x : A) → B`.
* `zonk` reaches every form the elaborator makes (`ecase`, `scase`, `delim`, `piq`,
  …): a solved metavariable inside a match's motive used to reach the kernel.
* Pruning: a solution at depth `k` that mentions a deeper metavariable whose type
  doesn't depend on the deeper variables (`?m := List ?n`, `?n` made under more
  `let`s) solves that one by a new metavariable at depth `k`.
* The structural parameter can be moved first past grouped binders (`(Tc TcI : Tm)`).

### 20b: the frontend checks `Frontend.wiz` ✅

The rest was performance, found by profiling the checker (flat `perf` profiles, and
stacks sampled by interrupting it under `gdb`):

* **A `let`'s variable is glued to its value** in the elaborator's context: it quotes
  back as the variable. Every metavariable is applied to the whole context, and each
  application used to carry the values of all the `let`s before it (`splitCol` ran out
  of memory).
* **The binders' types are quoted once**, lazily, for the Π type of every new
  metavariable, instead of once per metavariable.
* **A catch-all in case analysis is elaborated once**: the last clause of variables
  becomes `let dflt✝ := …` before the split, and the branches refer to it (a match on
  a `Val` with `| t => …` copied the body into some 70 branches).
* String literals' character codes are binary numerals too.

On a prefix where `Lex.wiz`, `Parse.wiz` and `Kernel.wiz` keep their types and their
functions become axioms, the self-hosted frontend checks all 650 declarations of
`Frontend.wiz` without an error, in about a quarter of an hour. So every file of the
self-hosted frontend is accepted by the self-hosted frontend.

### 20c: the self-check in the test suite ✅

Two more quadratic costs, both found by sampling stacks: the kernel's rule for an
application evaluated the argument to instantiate the codomain even when the codomain
doesn't mention it (`List.cons c rest` nested 2000 deep evaluated the rest at every
level: `usesVar`), and string literals' codes were unary. The whole self-hosted
frontend (`Lex`, `Parse`, `Kernel` and `Frontend.wiz`, 651 declarations) now checks
itself, unstubbed, in about 40 s; the test suite runs it.

### 20d: a faster kernel ✅

Profiling the self-check by call counts (`gprof`; the work runs on a second thread, so
its timings are useless but its counts are exact) pointed at universe levels: every
unfolding of a constant substituted its level parameters even when it had none
(`substIfAny`), and `conv` computed the full sort of a type at every step to test for
proof irrelevance. `isProp` now looks only at what decides it (a Π type is a
proposition when its codomain is), and `conv` doesn't ask at Π and Σ types (the
comparison of the bodies or components asks again). The self-check went from 40 s to
20 s. What remains is mostly allocation: comparing stuck `ecase`s (the payload types of
big data types) branch by branch.

### 20e: dead code in the backend ✅

The generated C showed allocations nobody used: `whnf` built a pair of erased values on
every call, and branches read fields their pattern variables never mentioned (an
increment and a decrement each). The backend now drops pure values nobody uses
(`erased`, numbers, constructors, projections, partial applications) before reference
counting (`elimDead` in `Reuse.lean`). In the kernel, two stuck `ecase`s with the same
branches over structurally equal environments (checked within a budget of nodes, without
allocating: `valSame`) are equal without comparing the branches. The self-check: 20 s to
13 s.

### 20f: sparse usages, shared constants ✅

* The kernel's usage lists (how often each variable is used, for quantities) may stop
  early, the variables after the end unused: no usage is the empty list, instead of a
  list as long as the context for every term (a third of the kernel's allocations).
* **Constants are hoisted** (`hoistConsts` in `Reuse.lean`): a string literal is a list
  of characters, and was built again at every use (`strEq (kindOf s) "term.ident"`:
  about twenty allocations). A closed constant used as a value becomes a function
  `wiz.const.k` without parameters, which the C backend runs once, marking the result
  immortal (never freed, not counted as a leak); the other backends just call it.
  Constants are interned in a table: each constructor node caches its hash, computed
  from its children's by the smart constructor `Const.mkCtor`, so interning is linear in
  their size, and only the constants used as values (not every suffix of a string) get
  a function.

The self-check: 13 s to 11 s. Since the start of stage 20 it went from about 17
minutes (on a stubbed prefix) to 11 s.

## Stage 21: bootstrap

### 21a–c: a self-hosted backend ✅

`selfhost/Backend.wiz` compiles what the self-hosted frontend checked to C, and
`selfhost/rt.c` is its runtime. A minimal first version:

* **Erasure** (`eraseCheck`, **exercise 21.1**; `eraseInfer`), type directed through the
  self-hosted kernel (`quickType` follows elimination spines, else `infer`): types,
  proofs, sizes and quantity-`0` arguments become `◾`. A value of `μ D i` stays its
  payload, nested pairs, except for a type shaped like the natural numbers, whose
  values are native numbers (unpacked for a match). Descriptions become objects, which
  the runtime's `ind` walks to build the induction hypotheses, **lazily**: a hypothesis
  is computed when the method first reads it (eagerly, every structural function walked
  its whole argument).
* **Lazy `let`s**: the match compiler's `let`s (a shared catch-all, the hypotheses) are
  substituted when cheap (variables, projections) and else suspended with `memo`;
  evaluated eagerly they made the self-compiled compiler thousands of times slower.
* **C** (`cgE`, **exercise 21.2**): each term one C expression (GNU statement
  expressions for `let` and `case`), `λ`s lifted to C functions over their captured
  variables; a global defined by `k` `λ`s is a C function of `k` arguments, called
  directly when applied to as many (else through a curried closure); other globals are
  values built on first use. Natives by name: `Nat` arithmetic, `IO`, `Str`, arrays
  (persistent: Baker's trick), `StrMap` (a persistent treap), `memo`.
* **Runtime**: tagged words, objects collected by the Boehm garbage collector (no
  reference counts yet); the program re-executes itself once with a large stack.

**Bootstrap**: the self-hosted compiler (frontend and backend, about 6500 lines of Wiz),
compiled by the Lean toolchain, compiles itself to C (about 90 000 lines); that program
(stage 2) produces the same C as stage 1 on the inputs tried. The test suite compiles
and runs a program with the self-hosted compiler (when `$WIZ_GC_CFLAGS`/`$WIZ_GC_LDFLAGS`
point at the garbage collector).

### 21d: faster self-compilation ✅

Measured, not guessed (`perf`, per-global timestamps from a streaming driver):

* Compiling the toolchain took 5 min 43 s, almost all of it in one global: the Prelude's
  text, a string literal 2600 characters long, i.e. 2600 nested `List.cons`. Two
  quadratic costs: erasure evaluated each argument to instantiate the next parameter's
  type even when the codomain doesn't mention it (`usesVar`, as in the kernel), and the
  C text was built by appending `String`s, lists of characters (now a rope, `Doc`,
  printed piece by piece). Also `quickType` follows `scase`, `let`, `coe` and the like
  instead of inferring the whole match again at every nested split. Now 18 s.
* String literals become their code points in the C code, built once; numerals made of
  `Nat.succ`/`Nat.mul` are folded. The C went from 19 MB to 9.4 MB.
* **Multi-argument closures**: a chain of `λ`s is one C function over its captured
  variables and arguments (`mkfun`), and an application to several arguments calls it
  at once (`apn`), without the closures of the partial applications. 88 000 lifted
  functions became 35 000, the C 5.1 MB, and compiling it takes 31 s instead of 3 min.
  Stage 2 runs about twice as fast.

A note on debugging: under `gdb`, the Boehm collector's stopping of the world hangs,
because `gdb` intercepts its suspend signals; pass them through (`handle SIGPWR nostop
noprint pass`, and the same for `SIGXCPU`).

**Fixpoint.** Stage 2 (the self-hosted compiler compiled by itself) compiles the whole
toolchain to exactly the same C as stage 1 does. It took 15 minutes against stage 1's
18 s, about 70% of it the collector marking: payloads as nested pairs were about four
objects per constructor. A chain of pairs `(e₀, (e₁, … t))` is now one object, its tails
the same pointer with an offset in its low bits (taking one allocates nothing): 8½
minutes. A `match` was a method applied to the payload, a closure built and called each
time; a lambda applied to arguments is now a `let`: 6 minutes. Reference counting comes
next.

### 21g: reference counting in the self-hosted backend (first stage)

A second mode of `Backend.wiz` (`genProgramRC`), chosen by a first line `-- wiz: rc` in
the program (a stand-in for a command-line flag: self-hosted programs can't read their
arguments yet). The garbage-collected mode is unchanged, byte for byte.

* **Perceus on the erased terms** (`rcE`): the C is in A-normal form, one local per
  intermediate value, statements in evaluation order (C leaves the order of arguments
  unspecified, and with reference counts the order of a use and an `inc` matters).
  Liveness is one backward pass: a term is compiled knowing the variables used after it
  (by de Bruijn level), and returns those used from its start; arguments are compiled
  right to left. The last use of a variable moves it, earlier uses `inc` it, and a
  variable that dies unused is `dec`ed where it dies (after its `let`, at a function's
  start, at the start of each `case` branch that doesn't use it). A projection path from
  a variable reads in place and `inc`s only the field; a `case` on a variable's field
  reads the tag in place.
* **Runtime** (`rt.c` with `WIZ_RC`): a count in every object's header; functions own
  their arguments; function closures pass their collected arguments on (moved out when
  unique); freeing is a worklist (a list a million long frees without recursion);
  `memo` and the lazy hypotheses of `ind` release their suspension once forced; arrays
  are updated in place when unique, else copied (Baker's versions would make cycles);
  map nodes hold their keys. Constants (globals, string literals) are roots, released at
  exit, after which the program checks that every object was freed.

* **Borrowed parameters** (as in Lean): a parameter of a global function that its body
  only reads (projections, a `case`'s tag, borrowed arguments of direct calls) is
  borrowed, found as a greatest fixed point over all functions. A caller lends a
  variable to it (and releases it after the call if that was its last use); the function
  neither `inc`s it nor releases it.

**Bootstrap in this mode**: stage 1 compiles the toolchain (with the `-- wiz: rc` line)
to C, and that program (stage 2, reference counted) compiles it again to the same C,
freeing every object by the end.

Next: reuse and drop specialisation (as in stages 8c), a faster allocator, keeping tail
calls when a borrowed argument is lent; then reference counting by default.

## Stage 22: numbers for hardware and systems code

Prerequisites shared by the HDL and the Rust-style DSL (decisions RD9, RD10/HD3).

### 22a: division, powers and bits ✅

The Prelude defines `Nat.div`, `Nat.mod`, `Nat.pow`, `Nat.land`, `Nat.lor`, `Nat.xor`,
`Nat.shiftLeft`, `Nat.shiftRight`, `Nat.log2` (and `Nat.testBit`, `a / b`) by structural
recursion on a fuel argument that bounds the number of steps, so the kernel can unfold
them. Each is registered with `builtin nat.<op>`: on numerals the kernel computes
natively (`def t : Nat.mod 300 256 = 44 := refl 44`), as do `#eval`, `#run`, C/LLVM
(`runtime/wiz.c`: machine words, GMP when big) and the self-hosted backend
(`selfhost/rt.c`; its Prelude has the same definitions). As in Lean, `n / 0 = 0`,
`Nat.mod n 0 = n` and `Nat.log2 0 = 0`. One table (`natNative?`, `Wiz/Core/Eval.lean`)
serves the kernel and both interpreters.

### 22b: `implemented_by` ✅

`attribute [implemented_by g] f` gives a definition `f` a different implementation in
compiled code: erasure (`compileReachable`) takes `g`'s code for `f`, while the kernel,
and so every proof, keeps `f`'s definition. `g` is a Wiz definition or an `extern`, and
must have `f`'s type up to conversion (checked at the attribute; `g` can't implement
`f` otherwise). The implementation is **trusted**, as in Lean: nothing proves it agrees
with the model, so tests compare them. `#eval` and `#run` follow the attribute, except
to an `extern` (the interpreters can't call C): there they run the model, which gives a
differential test for free. `#erase f` shows `f := g`. Foreign functions may now take
and return Wiz data types, passed as they are (marshalling kind `w`).

Not yet: a *type* with a native representation (`Vec A` as an array, R0b), and the
attribute in the self-hosted backend.

### 22c: machine integers ✅

`import Word` (`lib/Word.wiz`): `UIntN w`, a w-bit unsigned integer, and `IntN w`, w-bit
two's complement, both a number of bits below `2^w` (normalised by construction, so
arithmetic wraps around), with `ofNat`/`toNat`, wrapping `add`/`sub`/`mul`/`neg`,
`div`/`mod` (signed: `div` truncates towards zero and `rem` takes the dividend's sign,
as Rust; `x / 0 = 0` and `x % 0 = x` as Lean, where Rust panics), comparisons, bitwise
operations, shifts (`shiftLeft` by `k ≥ w` gives `0`; `IntN.shiftRight` is
arithmetic), `resize` (zero- or sign-extending, or truncating) and `toIntN`/`toUIntN`.

* **One width-indexed type** serves both clients: the HDL's `Unsigned n` needs any
  width (1, 5, 65, …) and Rust's `u32` is `U32 := UIntN 32` (also `U8 … U64`, `USize`,
  `I8 … I64`, with `U32.ofNat`, `I32.ofNeg`, …). Operations are named functions
  (`UIntN.add a b`, or `a.add b`) until the numeric classes (HD9) arrive.
* **The width is a phantom parameter** (`inductive UIntN (w : Nat) where | mk (toNat :
  Nat)`, since 22e/22h): no field mentions it, yet `UIntN 8` and `UIntN 16` are different
  types and `w` is inferred. (Before 22e it had to be an index, `mk {0 w : Nat} …`,
  leaving an erased slot in the object.)
* **Natives.** The kernel computes with the definitions, quickly on numerals (22a), and
  so do `#eval`/`#run`. Compiled code calls natives (`runtime/wiz.c`, `wiz_word_*`) by
  `implemented_by`: in a `uint64_t` up to 64 bits, GMP beyond, one function per
  operation for every width. A table of operations at widths 8 to 100 gives the same
  values in the kernel (`refl`), both interpreters, C and LLVM (`examples/words.wiz`:
  an FNV-1a hash, and facts proved by `refl` about named values; an equation whose
  sides still contain an unsolved implicit width when it is computed gets stuck, so
  state facts about definitions). A word is still an
  object holding a number (above `2^62`, a GMP number); unboxed words need the type-level
  `implemented_by` (22d).

### 22d: native representations: unboxed words ✅

`attribute [implemented_by mk get] T.mk` gives a type a **native representation** in
compiled code. `T.mk` is a constructor with one runtime field (the others erased);
`mk` has the constructor's type and `get` reads the field back. Erasure then never
builds the model's object: a constructor becomes `mk`, and `match` (and the generic
eliminators, which get the model's object back from `get`) reads the field with `get`.
The kernel and every proof keep the model. As with function-level `implemented_by`,
the natives are trusted, and the interpreters (`#eval`, `#run`) keep the model's
objects when `mk` or `get` is foreign, so the tables below compare the two.

`lib/Word.wiz` uses it for `UIntN w` and `IntN w` (and `NatObj`, a `Nat` passed to C
as the runtime number itself, possibly big). **A word is its bits**:

| bits b | representation | allocation |
|---|---|---|
| `b < 2^63` | a tagged scalar | none |
| `2^63 ≤ b < 2^64` | a raw 64-bit box (`WIZ_TAG_RAW`) | one cell |
| `b ≥ 2^64` (widths above 64) | a GMP number | as `Nat` |

* **Width-independent.** The representation depends only on b, so generic code over
  `UIntN w` (unknown `w`, any width: `BitVec n`, the HDL's `Unsigned n`) needs no width
  to build or read a word, and each value has exactly one representation (equality is
  a comparison of bits). `ofBits`/`toBits` convert from and to `Nat` (free below
  `2^62`).
* **Operations** are natives on that representation (`wiz_word_*` in `runtime/wiz.c`):
  `ofNat`/`ofNeg`, `+ - *`, `div`/`mod`/`rem`, comparisons, `land`/`lor`/`xor`/`not`,
  shifts and `testBit` (a shift or index of `2^64` or more counts as infinite),
  `resize` (zero- or sign-extending), `toIntN`/`toUIntN` (free). Up to 64 bits each is
  a few instructions on a `uint64_t`; the C backend pastes the runtime into the program,
  so `cc -O2` inlines them.
* **What is not unboxed.** A 64-bit value with the top bit set still takes a cell (the
  uniform representation has 63 bits of payload). Unboxing those too needs per-variable
  representations in the IR (raw `uint64_t` locals and parameters, boxed at polymorphic
  boundaries, as Lean's `UInt64`): the next step, once a measurement says it pays.
* **Self-hosted backend:** not yet (it runs the model; see the wishful note).

### 22e: phantom parameters ✅

```
inductive UIntN (w : Nat) where
  | mk (toNat : Nat)                     -- no field mentions `w`
def f (x : UIntN 8) : UIntN 16 := x      -- type mismatch
def width {ω w : Nat} (a : UIntN w) : Nat := w
#eval width (UIntN.mk 3 : UIntN 8)       -- 8: `w` is inferred
```

Types are structural, so a parameter that no field mentions used to be forgotten:
`UIntN 8` and `UIntN 16` were one type, `w` couldn't be inferred, and an HDL `Signal d A`
didn't keep clock domains apart. Now, for each such parameter `p : P`, the elaborator
(`phantomTail`, `Elab/Inductive.lean`) ends the type with `(0 phantom✝ : D) → Unit`
instead of `Unit`. That `Unit` is the end of the index type of an `inductive` or
`coinductive`, or of a structure's Σ. Here `D := p` if `p` is a type, and
`D := (0 x : P) × (x = p)` otherwise.

* `D` mentions `p` and is a type, not a proposition. Propositions compare by equivalence
  (4c), so `p = p` would have forgotten `p` again. Conversion now compares `p`, and
  unification solves it.
* The tail's only inhabitant is `fun _ => ()` (up to η). So it is still a singleton:
  constructors fill it in, patterns never see it, structure η and copattern index
  equations hold by `refl`, and `()` fills a structure's tail in a tuple.
* Erasure drops it (`erasable` knows the inaccessible binder name), so data, `#ir` and the
  C/LLVM code are those of the type without the parameter. Constructors, projections,
  `deriving` and `implemented_by` don't change. Nothing in the kernel changes either: it
  checks the encoding like any other declaration.
* Proof parameters get no phantom, and neither do sizes or quantities. A parameter whose
  `D` lives in a higher universe than the type also gets none, since the tail would
  raise the type's universe; it stays forgotten.
* For structures, `S 8 = S 16` computes through the Σ to `(x = 8) ↔ (x = 16)` under
  a binder `x`, so it is refutable (`Tests/Elab.lean`, group `phantom`). Equality of two
  `μ` types computes to the index equation only when their descriptions agree (so
  `UIntN 8 = UIntN 8` does), and the phantom is part of the description. So for an
  `inductive`, `UIntN 8 = UIntN 16` stays stuck: it is neither provable nor refutable,
  and a `cast` between such types gets stuck too.
* A `def` alias (`def Mut (ρ : Region) (A : Type) : Type := A`) unfolds, so its
  parameters never count. Declare a `structure` instead.

### 22g: regions: borrow checking as typing ✅

```
def longest {ρa ρb : Region} (0 h : Outlives ρa ρb) (x : Shr ρa U64) (y : Shr ρb U64) : Result (Shr ρb U64) :=
  match U64.lt x.val y.val with
  | .true => .ok y
  | .false => .ok (Shr.weaken h x)                       -- without `h`: type mismatch
def bad {ρ : Region} (x : Shr ρ U64) : Result (Shr ρ U64) :=
  Shr.borrow ρ (U64.lit 5) (fun ρy hy y => .ok y)         -- E0515: type mismatch
```

`lib/Region.wiz` (`import Region`) is the lifetime layer of the Rust DSL's lowering
(`drafts/rust/`, RD12). A lifetime is an erased `ρ : Region`, and the borrow handles are
declared types, so with phantom parameters (22e) the region is part of their identity
and is inferred: `Shr ρ A` (`&'a A`), `Uniq ρ A` (`&'a mut A` passed in and handed back),
`Mut ρ A S` (a returned `&'a mut A` with its backward function to the lender `S`),
`MutOpt ρ A S`, and `Lent ρ S`, the lender while it is borrowed. Borrow checking is
typing:

* A borrow scope (`Shr.borrow`, `Uniq.borrow`, `Uniq.reborrow`, `Uniq.share`,
  `Uniq.zoom`, `Region.scope`) takes a body polymorphic in a fresh region, whose result
  type is chosen outside it (as `runST`), so no handle of the scope's region can leave
  it: returning a borrow of a local (E0515) or keeping one past its lender's scope
  (E0597) is a type mismatch.
* Inside a mutable borrow, the lender's name is rebound to a `Lent` token, which nothing
  accepts: using the lender, or borrowing it again, while the borrow lives (E0499,
  E0502) is a type mismatch.
* A reference flows to a place of a shorter region only through `Shr.weaken`, which
  takes an `Outlives ρ ρ'` proof (erased). Proofs come from scopes (a scope nested in `σ`
  hands out `Outlives σ ρ`) and from a function's `'a : 'b` bounds (erased proof
  arguments); `Outlives` is opaque, so there is no other way to get one.

Scopes run their body at the enclosing region (regions are erased, so this is sound);
the separation comes from parametricity alone. `drafts/rust/rejected/` has the classic
errors, lowered, each rejected (`sh drafts/rust/check.sh`); test group `regions`.
Not yet: the constructors of the handles are public (private-decls), so the guarantee
holds for code that follows the lowering rules (the DSL front end), not for hand-written
Wiz that forges a handle.

### 22h: one bit-vector family ✅

`BitVec n` (`lib/BitVec.wiz`) and `UIntN n` (`lib/Word.wiz`) are one type:

```
inductive UIntN (w : Nat) where | mk (toNat : Nat)   -- lib/Word.wiz: the model + natives
def BitVec (n : Nat) : Type := UIntN n               -- lib/BitVec.wiz: the HDL/proof names
def BitVec.add {ω n : Nat} (a b : BitVec n) : BitVec n := UIntN.add a b
def w (x : U32) : BitVec 32 := BitVec.add x (BitVec.ofNat 32 1)   -- no conversion
```

* **Design.** `UIntN` is the implementation: one model (a number below `2^w`), one set
  of natives (22c-d), one runtime representation (a word is its bits). `BitVec` is a
  view of it: a `def` alias plus the hardware vocabulary (`udiv`, `and`, `shl`, `lshr`,
  `ashr`, `slt`, `concat`, `extract`, `zeroExtend`, `signExtend`, `toVec`/`ofVec`, …),
  each defined as the `UIntN`/`IntN` operation it is (signed ones read the bits as
  `IntN n`, a free cast). The alias is enough because the width counts through
  `UIntN`'s phantom parameter (a `def` alias's own parameters never count, 22e):
  `BitVec 8` is not `U16`. The reverse (a `BitVec` structure `implemented_by` words)
  would need a second representation registration and conversions at every Rust/HDL
  boundary.
* **Proofs** see the definitions, which unfold to Word's model, so the BitVec lemmas
  are stated as before (`BitVec.add_comm` is `congrArg (UIntN.ofNat n)
  (Nat.add_comm …)`); `BitVec.add_eq : BitVec.add a b = UIntN.add a b` is `refl`.
  The literal tables (group `vec`) and the 34-operation and 64-bit word tables (group
  `word`) agree in the kernel, `#eval`, `#run`, C and LLVM.
* **Compiled**, a bit vector is a native word: no constructor or projection in the IR
  (group `vec`), no allocation below `2^63`. The model's object is now `⟨0 bits⟩`
  (the width no longer takes a slot), so a word read back prints as `.mk 18446744073709551613`.
* **For the HDL**: `Unsigned n`/`Signed n` (hdl-plan §2.2) can reuse the same
  representation as aliases (`def Unsigned (n : Nat) := UIntN n`, `Signed n := IntN n`);
  a `structure` wrapper would instead need its own `implemented_by mk get` to avoid a box.

## Libraries

### H0c: vectors and bit vectors ✅

`lib/Vec.wiz` (`import Vec`): `Fin n` (a `Nat` with an erased proof `Nat.lt val n = .true`;
`Fin.of 5 3 rfl`) and `Vec A n`, whose length is an **erased** index: at runtime a
vector is a list, and `Vec.length` counts it, with `Vec.length_eq : Vec.length v = n`.
Functions: `head`/`tail`/`last`/`init` on non-empty vectors, `get`/`set` by `Fin`,
`map`, `zipWith`, `zip`, `foldl`/`foldr`, `replicate`, `ofFn`, `append`, `reverse`
(linear, with a `cast` along `m + (k+1) = (m+k)+1`), `snoc`, `splitAt`, `shiftIn`,
`toList`/`fromList` (`fromList l : Vec A (List.length l)`). Theorems: `length_eq`,
`length_toList`, `toList_fromList`, `map_map`, `get_set` (`get (set v i x) i = x`),
`get_map`, and the `Nat` lemmas they need (`add_zero`, `add_succ`, `add_comm`), all by
structural recursion. `map_map`, `get_set` and `get_map` go through equations such as
`Vec.map_cons : map f (cons x xs) = cons (f x) (map f xs)`, which hold only up to casts at
the element type and are proved with the Prelude's axiom `castRefl` (below).

`lib/BitVec.wiz` (`import BitVec`): `BitVec n` (since 22h, `UIntN n` under another name), a `Nat` below `2^n` by construction
(every operation reduces mod `2^n`). Wrapping `add`/`sub`/`neg`/`mul`, `udiv`/`umod`,
`and`/`or`/`xor`/`not`, `shl`/`lshr`/`ashr`, `getBit`, `msb`, `beq`/`ult`/`ule`/`slt`/`sle`,
`concat`, `extract hi lo`, `zeroExtend`, `signExtend`, and `toVec`/`ofVec` (to and
from `Vec Bool n`, least significant bit first). Operations that need `2^n` take the
width at runtime (`{ω n : Nat}`). The arithmetic is the Prelude's native `Nat`
operations (22a), so the kernel computes on literal bit vectors:
`(BitVec.add (BitVec.ofNat 8 200) (BitVec.ofNat 8 100)).toNat = 44 := rfl`. Compiled code
runs `lib/Word.wiz`'s native words (22h).

Along the way the elaborator learned to:
* keep erased constructor fields and arguments erased when a `match` reverts them, and
  name a field directly instead of through a `let` at ω (`| .mk i h => … h …` with
  `0 h`);
* prove an equation that has already computed with `rfl` (`Nat.succ a = Nat.succ a`
  is a Σ of `True`s and `a = a`), and recompute an equation stuck on a metavariable
  once it is solved (`congrArg Nat.succ ih` against such a goal). The proof follows the
  elaborator's computed form; where the kernel computes the equation to another shape
  (a numeral on one side, a constructor on the other), the kernel rejects it;
* erase a `cast` against its source type (the solution rule casts a function, so
  `head`, `tail` and `zipWith` on vectors failed at runtime).

Not yet: facts like `Vec.get v (Fin.of 3 1 rfl) = 20 := rfl` (the `rfl` shape
problem above; `drafts/vec-lib/VecProofs.wiz`), arithmetic facts about `BitVec` in general, numerals and operators
(`a + b`) for `BitVec` (decision HD9).

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
registrations, info trees) in the cache directory (`--cache DIR`, default `~/.cache/wiz`;
`--no-cache` turns it off), under the command's chained content hash. A shared directory is a shared cache,
since equal keys mean equal results. Imported modules are cached command by command
too. Commands that change the grammar or the macros rerun (they are cheap).
`Wiz/Cache.lean` serialises terms as S-expressions (quantities through the rig's
literal syntax). Every example gives the same output from the cache as without it.

Next: finer dependencies (re-elaborate only what an edit affects, not everything
after it).

### 11d: the info tree, the infoview and code actions ✅

* **The info tree** (`Elab/Basic.lean`, `Elab/Info.lean`): while elaborating, the
  elaborator records identifiers, the expected type of every checked term (and of every
  hole), the open goals before and after each tactic, `match`es and declarations. It
  keeps values and contexts as it goes (free) and quotes and zonks them at the end of the
  declaration, into `Term`s, not strings. An error carries the state it was thrown in,
  so a declaration that fails (unsolved goals, a hole) still has its tree. The tree is
  memoised and cached with its command; hovers and go to definition read it.
* **The infoview** (`Wiz/Infoview.lean`): `Term.prettyTagged` prints a term exactly as
  `Term.pretty` does, as tagged text: every subterm is a tag whose ref points into the
  document's session table (valid until the next edit). `wiz lsp` answers
  `wiz/plainGoal`, `wiz/plainTermGoal`, `wiz/interactiveGoals`,
  `wiz/interactiveTermGoal` and `wiz/subtermInfo` (a subterm's type, from the kernel,
  and where a constant was declared); the protocol is in
  `wiz-notes/infoview-protocol.md`.
* **Code actions** (`Wiz/Actions.lean`): diagnostics carry a code and data; the server
  offers *did you mean* (edit distance ≤ 2 over locals and globals), *add missing cases*
  (`| .c x y => ?c` per missing constructor) and *add type ascription* to a `def` without
  a type, with edits inline or through `codeAction/resolve`.

```
def k : Nat → Bool → Nat := by
  intro n         -- wiz/plainGoal here:  n : Nat ⊢ Bool → Nat
  intro b
  exact n
def four : Nat := doubel 2    -- unknown identifier 'doubel'   [Did you mean 'double'?]
```

### 11l: the infoview socket ✅

`wiz lsp --infoview SOCK` also listens on the Unix socket `SOCK`, for infoviews that run
beside the editor (the terminal infoview connects there). The editor never says where
its cursor is, so the server infers it from the editor's requests: any request with a
position (hover, `documentHighlight`, which the server now advertises so that editors
send it on every move, go to definition, completion, …) and code actions (at the
range's start). When the cursor moves, and after each elaboration of its document,
every connected infoview gets `wiz/infoview/cursor` (uri, position, session) and pulls
with the ordinary `wiz/*` requests on the socket; sessions and refs are the editor's.
Lean's library has no Unix sockets, so `c/sockets.c` (compiled into the executables by
the linker, `moreLinkObjs` in the lakefile) listens, accepts, and turns a connection
into two ordinary Lean handles. The server's state stays single-threaded: a reader
thread per connection feeds one channel, and one loop answers in order. Protocol §8 of
`wiz-notes/infoview-protocol.md`; tested in-process (the `lsp-server` group: the editor
on a socket pair, an infoview on the socket).

### 11m–n: the infoview, in a terminal and in a browser ✅

```
wiz lsp --infoview /tmp/wiz.sock          # the editor's server (11l)
wiz-infoview /tmp/wiz.sock                # in a tmux split: the goals at the cursor
wiz-infoview --file t.wiz --at 4:5        # or on its own: starts `wiz lsp` itself
web/build.sh && web/bridge.sh             # the same infoview in a browser
```

Both clients are Wiz programs, and they share their logic:

* `lib/Json.wiz`: JSON values (mutual inductive types: Wiz has no nested ones), a
  parser and a printer. Strings are code points; `\uXXXX` escapes and surrogate pairs
  are decoded, and the printer escapes control characters (or everything non-ASCII,
  `Json.renderAscii`).
* `lib/Infoview.wiz`: the protocol's tagged text and goals; a **layout** that flattens
  tagged text into styled pieces (numbering the tags in reading order), word-wraps them
  to a width with hanging indents, and renders lines with SGR colours by kind; the same
  goals as **HTML** with a `data-ref` and `data-idx` on every subterm's `<span>`;
  navigation (next, previous, enclosing, first inside); `Content-Length` framing
  (counting UTF-8 bytes); and the decoding of terminal keys and SGR mouse reports.
* `infoview/Tui.wiz` (`infoview/build.sh`): the terminal program. The alternate screen,
  raw mode, `poll` over the keyboard, the socket and a `SIGWINCH` self-pipe, and Unix
  sockets are `infoview/term.c`, bound with `extern` (Wiz has no callbacks or
  structs in its FFI, so the event loop is Wiz around a blocking `iv_wait`). ←/→ select
  a subterm, ↑/↓ go out of and into it, and the bottom line says what it is
  (`wiz/subtermInfo`); a mouse click selects too.
* `web/Web.wiz` (`web/build.sh`): the page's language client, compiled to C and then to
  WebAssembly by Emscripten: wasm64 keeps the runtime's 62-bit small numbers, mini-gmp
  stands in for GMP, and Asyncify lets `js_next_event` wait for the page. The page
  (`web/infoview.html`, `web/infoview.js`, about 100 lines of JavaScript) only moves events
  in and HTML out. `web/bridge.sh` puts `websocat` in front of `wiz lsp` until the server
  speaks WebSocket itself.

Running it in tmux, next to an editor whose language server is `wiz lsp --infoview
/tmp/wiz.sock` (11l):

```
infoview/build.sh                                   # → .lake/build/bin/wiz-infoview
tmux split-window -h -l 60 '.lake/build/bin/wiz-infoview /tmp/wiz.sock'
```

The pane waits for the server, then follows the editor's cursor. Without an editor:
`wiz-infoview --file examples/tactics.wiz --at 6:3` (`[` and `]` move the line).
`infoview/test.sh` (in the `infoview` test group) runs the terminal infoview against
`infoview/stub_server.py` (canned goals; as text and in a pseudo-terminal) and against
the real `wiz lsp --infoview`, with `infoview/editor_stub.py` as the editor.
`web/test.sh` (needs nix: Emscripten, websocat, Chromium; not in CI) runs the Wasm
module under Node, then the page in headless Chromium over the DevTools protocol.

## Stage 23: grail, a build tool

### 23b: modules by path ✅

`import A.B` reads `A/B.wiz` under the first **module root** that has it; `lib/` is a
root, so `import Prelude` is `lib/Prelude.wiz` as before. The frontend stays pure: the
caller reads every module a file can reach up front, by scanning its import lines
(`Wiz/Module.lean`).

### 23c: a key per module, atomic writes ✅

A module's key is computed from text alone, before anything is elaborated:

    key(M) = hash(salt, toolchain, text of M, M's C headers, key(N) for each import N)

and a module is elaborated **in isolation**, from the empty state plus its own imports,
so what it elaborates to depends only on its key. An importer's chain of command keys
mixes in `key(M)` at the `import`. Editing a module now invalidates it and what imports
it, not the whole library, and a module imported by many files is cached once. A module
that uses a name it doesn't import is an error, with the cache or without (`--no-cache`
keeps the effects in memory for the run), and in `runFrontend`, which the tests and the
language server use: it checks each module once in isolation (errors are reported at
the `import`) and then elaborates it into the importer's state, unless that state is
still the initial one and the isolated result serves as it is. So the editor rejects
what `wiz check` rejects. Cache files are
written to a temporary name and renamed, so concurrent runs never see half a file.

### 23d: grail v0 ✅

A package is a directory with a `grail.wiz`, written in Wiz against `lib/Grail.wiz`:

```
import Grail
def package : Package := Package.new "wiz"
  |> Package.lib "std" "lib"                    -- check every module under lib/
  |> Package.check "app" "app.wiz"              -- check one file
  |> Package.exe "io" "examples/io.wiz"         -- compile `main`: .grail/bin/io
```

```sh
lake build grail
.lake/build/bin/grail build          # every target; `grail build std` for one
.lake/build/bin/grail targets        # list them; `grail config` prints the toolchain
```

grail evaluates `Package.render package` (an S-expression) in the interpreter and
builds a graph of **jobs**: `check` per file, and `ir → c → obj → link` per executable.
A job's key is computed from its inputs before it runs (a check from the file's key, an
object from the C text and the compiler flags), its output goes to
`.grail/build/<key>/` through a temporary directory and a rename, and a job whose
directory exists doesn't run: **a second build runs no jobs**, an edit reruns the checks
of the files that import what changed, and an edit that leaves the C alone stops there.
The key also covers the grail binary itself, so a new elaborator rebuilds everything.

There are no environment variables: the C compiler and its flags come from flags
(`--cc`, `--cflags`, `--ldflags`, `--llc`, `-I DIR`, `--cache DIR`, `--no-cache`) or from
an uncommitted `grail.local.wiz` with this machine's paths (`nix develop` writes it from
`flake.nix`):

```
import Grail
def settings : Settings := Settings.empty
  |> Settings.set "cflags" "-I/nix/store/…-gmp-…-dev/include"
  |> Settings.set "ldflags" "-L/nix/store/…-gmp-…/lib -Wl,-rpath,/nix/store/…-gmp-…/lib"
```

### 23a: the toolchain as flags ✅

`wiz` reads no environment variables: the toolchain record (`Wiz/Toolchain.lean`: C
compiler and flags, `llc`, the collector's flags, the cache, module roots) comes from
`--cc`, `--cflags`, `--ldflags`, `--libs`, `--llc`, `--cache DIR`/`--no-cache` and
`-I DIR` (which replaces `$WIZ_PATH`), and is passed explicitly to everything that
compiles. Its compiler fields are its `id`, which enters grail's keys.

### 23e: the self-hosted toolchain as targets ✅

`Package.selfhost NAME ROLE` builds the self-hosted programs from `selfhost/*.wiz`
(`Wiz/Selfhost.lean` generates their sources, parser tables included, for grail and the
tests alike): `checker`, `compiler`, and `bootstrap`, the fixpoint check of
`scripts/fixpoint.sh` as jobs (generate the source, build stage 1, `self1.c`, stage 2,
`self2.c`, compare). `grail build bootstrap` runs it (minutes); run again, it runs
nothing unless a source, `rt.c`, the toolchain or grail changed. `grail build` alone
leaves it out.

### 23f: a test runner ✅

`Package.tests NAME DIR` makes every `.wiz` file under `DIR` a test, with its expected
output beside it in `.expected`. The first line gives the kind: `-- test: check` (the
default: the messages, as `wiz check` prints them) or `-- test: run` (what `main` prints,
compiled through C). A pass is a job like any other, keyed by the file (and its
imports), the kind, the toolchain and the expected output, so `grail test` again runs
nothing; `grail test FILTER` runs the tests whose path contains it, and
`grail test --update` writes the actual output. Every example is a test
(`examples/*.expected`). The Lean tests stay in `lake test`.

### 23g: parallel jobs ✅

The jobs form an explicit graph (`Grail/Graph.lean`): `ir F` depends on `check F`, …,
`link E` on `obj F`, a check on the checks of the package modules it imports, a `run` test
on its executable, the bootstrap steps on each other. A node's key is computed when its
dependencies are done (an object's key hashes the C its `c` node wrote); a node whose
output exists is up to date, the rest are jobs in a ready queue. `grail build -j N`
(default: the cores, at most 4) runs up to `N` jobs at a time, each as a separate process
(`grail --grail-job …` with the toolchain as flags, or the C compiler) under `timeout`
(`--timeout SECS`, default 1800; tests `--test-timeout SECS`, default 300, so a test that
hangs fails instead of hanging the run). A failed job is reported and the jobs that depend
on it are skipped; the others still run. Each job's output is buffered and printed in the
graph's order, so `-j 1` and `-j 8` print the same report, and a second build still runs
no jobs.

### 23h: git dependencies and a lock file ✅

`Package.dep NAME URL REV` depends on the package at a git URL (a path, `file://`,
`https://`) and revision (tag, branch or commit). `grail update` resolves each
dependency, and theirs (from their own `grail.wiz`), to a commit, clones it to
`.grail/packages/NAME`, and writes `grail.lock`, which is committed:

```
(lock
  (dep greet "https://example.org/greet.git" v1 88bef64fe0c79f190976221e57f65d6b17a1866c 89d8a320ea2473de))
```

(name, URL, revision, commit, and a hash of the checked-out files). Builds use the lock
only: each dependency is checked out at its locked commit (fetched if missing), files
that don't match the hash are refused, and a `REV` changed in `grail.wiz` stays at the
locked commit, with a note, until `grail update`. The roots of a dependency's `lib`
targets become module roots, so `import Greet.Hello` finds
`.grail/packages/greet/src/Greet/Hello.wiz`; module keys already hash module texts.
Two different commits of one dependency name are refused (no version resolution yet).
