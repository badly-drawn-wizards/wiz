# Stage 2: the extensible parser

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

## Optional extensions to stage 2

* **2.7** Replace the token list with a trie.
* **2.8** Index leading parsers by their first token, so the Pratt loop only tries
  parsers that can start with the next token. This is how Lean keeps longest match
  cheap.
* **2.9** A syntax *formatter* (`Syntax → String`) that round-trips: parsing the output
  gives back the same tree. You'll need it for macro error messages and the LSP.
* **2.10** Ambiguity detection: when two equal-priority parsers tie on length, report
  an ambiguity instead of silently picking the later one, or keep both as a *choice
  node* (as Lean does) and let the elaborator decide.
