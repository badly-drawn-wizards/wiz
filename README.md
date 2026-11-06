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
