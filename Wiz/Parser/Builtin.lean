import Wiz.Parser.Descr

/-!
# The built-in grammar

Everything here is ordinary `ParserDescr` data, registered exactly as a user `syntax`
declaration would be. Node kinds and the shape of their children are the contract with
the elaborator (`Wiz.Elab`), so they're listed with each parser.

Notation: `[x]` means "a `null` node", so `optional p` gives `[]` or `[p...]`.

```
quantity          := num | "ω"
binder.explicit   := "(" [quantity] [names+] [":" type] ")"
binder.implicit   := "{" [quantity] [names+] [":" type] "}"
```

Quantities follow Idris 2: `(1 x : A)`, `{0 A : Type}`. An omitted quantity means ω
on explicit binders and 0 on implicit ones.
-/

namespace Wiz.Builtin

open ParserDescr

def term (prec : Nat := 0) : ParserDescr := cat "term" prec
def arrow : ParserDescr := orelse (atom "→") (atom "->")
def seqs (ps : List ParserDescr) : ParserDescr := seq ps.toArray

def quantity : ParserDescr := node "quantity" (orelse num (atom "ω"))

def hole : ParserDescr := node "term.hole" (atom "_")
def binderIdent : ParserDescr := orelse ident hole

/-- `[":" T]`, either optional or required (a required one is still a one-element
`null` node so both have the same shape). -/
def typeSpec (required : Bool) : ParserDescr :=
  if required then node "null" (seqs [":", term]) else optional (seqs [":", term])

def explicitBinder (requireType : Bool) : ParserDescr :=
  node "binder.explicit" <| seqs ["(", withoutPosition <| seqs
    [optional quantity, many1 binderIdent, typeSpec requireType], ")"]

def implicitBinder (requireType : Bool) : ParserDescr :=
  node "binder.implicit" <| seqs ["{", withoutPosition <| seqs
    [optional quantity, many1 binderIdent, typeSpec requireType], "}"]

def bracketedBinder (requireType : Bool) : ParserDescr :=
  orelse (explicitBinder requireType) (implicitBinder requireType)

/-- Binders of `fun` and `∀`: a bare name or a bracketed group with optional type. -/
def simpleBinder : ParserDescr := orelse (bracketedBinder false) binderIdent

def precedence : ParserDescr := node "prec" (orelse num ident)

def level (prec : Nat := 0) : ParserDescr := cat "level" prec

/-- `.{u, v}` after a name -/
def univParams : ParserDescr := optional (seqs [noWs, ".{", sepBy1 ident ",", "}"])

/-- Universe levels.

| kind          | children |
|---------------|----------|
| `level.num`   | num |
| `level.param` | ident |
| `level.hole`  | "_" |
| `level.paren` | "(" level ")" |
| `level.max`, `level.imax` | "max" level level |
| `level.add` (trailing) | level "+" num |
-/
def levelLeading : List LeadingParser := [
  { kind := "level.num", prec := maxPrec, p := num },
  { kind := "level.param", prec := maxPrec, p := ident },
  { kind := "level.hole", prec := maxPrec, p := "_" },
  { kind := "level.paren", prec := maxPrec, p := seqs ["(", withoutPosition (level 0), ")"] },
  { kind := "level.max", prec := leadPrec, p := seqs [nonReserved "max", level maxPrec, level maxPrec] },
  { kind := "level.imax", prec := leadPrec, p := seqs [nonReserved "imax", level maxPrec, level maxPrec] }
]

def levelTrailing : List TrailingParser := [
  { kind := "level.add", prec := 65, lhsPrec := 65, p := seqs ["+", num] }
]

/-- Term syntax.

| kind                 | prec | children |
|----------------------|------|----------|
| `term.ident`         | max  | ident |
| `term.num`, `term.str` | max | literal |
| `term.type`          | max  | "Type" [level] |
| `term.sort`          | max  | "Sort" [level] |
| `term.prop`          | max  | "Prop" |
| `term.identUniv`     | max  | ident ".{" [levels] "}" |
| `term.hole`          | max  | "_" |
| `term.syntheticHole` | max  | "?" ident |
| `term.paren`         | max  | "(" term ")" |
| `term.ascription`    | max  | "(" term ":" term ")" |
| `term.explicit`      | max  | "@" ident |
| `term.fun`           | max  | "fun" [binder+] "=>" term |
| `term.let`           | lead | "let" [quantity] ident [":" T] ":=" term [";"] term |
| `term.forall`        | lead | "∀" [binder+] "," term |
| `term.depArrow`      | 25   | binder "→" term |
| `term.app` (trailing)| lead | f [args+] |
| `term.arrow` (trailing)| 25 | A "→" B |
| `term.depSigma`      | 35   | binder "×" term |
| `term.prod` (trailing) | 35 | A "×" B |
| `term.tuple`         | max  | "(" term "," [terms] ")" |
| `term.unitVal`       | max  | "(" ")" |
| `term.proj` (trailing) | max | t "." num |
| `term.letPair`       | lead | "let" [quantity] "(" ident "," ident ")" ":=" term [";"] term |
| `term.absurd`        | lead | "absurd" term |

Field access by name (`p.x`) needs no syntax: `p.x` lexes as one dotted identifier,
and the elaborator resolves it.
-/
def termLeading : List LeadingParser := [
  { kind := "term.ident", prec := maxPrec, p := ident },
  { kind := "term.num", prec := maxPrec, p := num },
  { kind := "term.str", prec := maxPrec, p := str },
  { kind := "term.type", prec := maxPrec, p := seqs ["Type", optional (seqs [checkPrec leadPrec, level maxPrec])] },
  { kind := "term.sort", prec := maxPrec, p := seqs ["Sort", optional (seqs [checkPrec leadPrec, level maxPrec])] },
  { kind := "term.prop", prec := maxPrec, p := "Prop" },
  { kind := "term.identUniv", prec := maxPrec, p := seqs [ident, noWs, ".{", sepBy1 (level 0) ",", "}"] },
  { kind := "term.hole", prec := maxPrec, p := "_" },
  { kind := "term.syntheticHole", prec := maxPrec, p := seqs ["?", noWs, ident] },
  { kind := "term.paren", prec := maxPrec, p := seqs ["(", withoutPosition term, ")"] },
  { kind := "term.ascription", prec := maxPrec,
    p := seqs ["(", withoutPosition (seqs [term, ":", term]), ")"] },
  { kind := "term.explicit", prec := maxPrec, p := seqs ["@", noWs, ident] },
  { kind := "term.fun", prec := maxPrec,
    p := seqs [orelse "fun" "λ", many1 simpleBinder, orelse "=>" "↦", term] },
  { kind := "term.let", prec := leadPrec,
    p := withPosition <| seqs ["let", optional quantity, ident, typeSpec false, ":=", term,
      optional ";", term] },
  { kind := "term.forall", prec := leadPrec,
    p := seqs ["∀", many1 simpleBinder, ",", term] },
  { kind := "term.depArrow", prec := 25, p := seqs [bracketedBinder true, arrow, term 25] },
  { kind := "term.depSigma", prec := 35, p := seqs [explicitBinder true, "×", term 35] },
  { kind := "term.tuple", prec := maxPrec,
    p := seqs ["(", withoutPosition (seqs [term, ",", sepBy1 term ","]), ")"] },
  { kind := "term.unitVal", prec := maxPrec, p := seqs ["(", ")"] },
  { kind := "term.letPair", prec := leadPrec,
    p := withPosition <| seqs ["let", optional quantity, "(", ident, ",", ident, ")", ":=", term,
      optional ";", term] },
  { kind := "term.absurd", prec := leadPrec, p := seqs ["absurd", term maxPrec] }
]

def termTrailing : List TrailingParser := [
  { kind := "term.app", prec := leadPrec, lhsPrec := maxPrec,
    p := many1 (seqs [colGt, term argPrec]) },
  { kind := "term.arrow", prec := 25, lhsPrec := 26, p := seqs [arrow, term 25] },
  { kind := "term.prod", prec := 35, lhsPrec := 36, p := seqs ["×", term 35] },
  { kind := "term.proj", prec := maxPrec, lhsPrec := maxPrec, p := seqs [noWs, ".", noWs, num] }
]

/-- Commands. Each command is parsed inside `withPosition`, so an application can't
continue onto a line starting at the command's column.

| kind                         | children |
|------------------------------|----------|
| `command.def`                | "def" ident [".{" [us] "}"] [binders] [":" T] ":=" term |
| `command.axiom`              | "axiom" ident [".{" [us] "}"] [binders] ":" T |
| `command.check`              | "#check" term |
| `command.reduce`             | "#reduce" term |
| `command.declareSyntaxCat`   | "declare_syntax_cat" ident |
| `command.syntax`             | "syntax" [":" prec] [name] [priority] [stx+] ":" ident |
-/
def commandLeading : List LeadingParser := [
  { kind := "command.def", prec := maxPrec,
    p := seqs ["def", ident, univParams, many (bracketedBinder false), typeSpec false, ":=", term] },
  { kind := "command.axiom", prec := maxPrec,
    p := seqs ["axiom", ident, univParams, many (bracketedBinder false), typeSpec true] },
  { kind := "command.check", prec := maxPrec, p := seqs ["#check", term] },
  { kind := "command.reduce", prec := maxPrec, p := seqs ["#reduce", term] },
  { kind := "command.declareSyntaxCat", prec := maxPrec, p := seqs ["declare_syntax_cat", ident] },
  { kind := "command.syntax", prec := maxPrec,
    p := seqs ["syntax", optional (seqs [noWs, ":", noWs, precedence]),
      optional (seqs ["(", nonReserved "name", ":=", ident, ")"]),
      optional (seqs ["(", nonReserved "priority", ":=", num, ")"]),
      many1 (cat "stx" 0), ":", ident] }
]

/-- The grammar of grammars, used by the `syntax` command.

| kind            | children |
|-----------------|----------|
| `stx.atom`      | str |
| `stx.cat`       | ident [":" prec] (`ident`, `num`, `str`, `colGt`, `colGe`, `noWs` are special) |
| `stx.group`     | "(" [stx+] ")" |
| `stx.sepBy`     | "sepBy" "(" [stx+] "," str ["," "allowTrailingSep"] ")" (also `sepBy1`) |
| `stx.withPosition` | "withPosition" "(" [stx+] ")" |
| `stx.many`, `stx.many1`, `stx.optional` (trailing) | stx "*" / "+" / "?" |
-/
def stxLeading : List LeadingParser := [
  { kind := "stx.atom", prec := maxPrec, p := str },
  { kind := "stx.cat", prec := maxPrec, p := seqs [ident, optional (seqs [noWs, ":", noWs, precedence])] },
  { kind := "stx.group", prec := maxPrec, p := seqs ["(", many1 (cat "stx" 0), ")"] },
  { kind := "stx.sepBy", prec := maxPrec,
    p := seqs [nonReserved "sepBy", noWs, "(", many1 (cat "stx" 0), ",", str,
      optional (seqs [",", nonReserved "allowTrailingSep"]), ")"] },
  { kind := "stx.sepBy1", prec := maxPrec,
    p := seqs [nonReserved "sepBy1", noWs, "(", many1 (cat "stx" 0), ",", str,
      optional (seqs [",", nonReserved "allowTrailingSep"]), ")"] },
  { kind := "stx.withPosition", prec := maxPrec,
    p := seqs [nonReserved "withPosition", noWs, "(", many1 (cat "stx" 0), ")"] }
]

def stxTrailing : List TrailingParser := [
  { kind := "stx.many", prec := maxPrec, lhsPrec := maxPrec, p := seqs [noWs, "*"] },
  { kind := "stx.many1", prec := maxPrec, lhsPrec := maxPrec, p := seqs [noWs, "+"] },
  { kind := "stx.optional", prec := maxPrec, lhsPrec := maxPrec, p := seqs [noWs, "?"] }
]

def tables : ParserTables :=
  let t : ParserTables := {}
  let t := ["term", "command", "stx", "level"].foldl ParserTables.declareCategory t
  let t := levelLeading.foldl (·.addLeading "level" ·) t
  let t := levelTrailing.foldl (·.addTrailing "level" ·) t
  let t := termLeading.foldl (·.addLeading "term" ·) t
  let t := termTrailing.foldl (·.addTrailing "term" ·) t
  let t := commandLeading.foldl (·.addLeading "command" ·) t
  let t := stxLeading.foldl (·.addLeading "stx" ·) t
  stxTrailing.foldl (·.addTrailing "stx" ·) t

end Wiz.Builtin
