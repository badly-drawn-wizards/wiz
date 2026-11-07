import Wiz.Parser.Descr

/-!
# The built-in grammar

Everything here is ordinary `ParserDescr` data, registered exactly as a user `syntax`
declaration would be. Node kinds and the shape of their children are the contract with
the elaborator (`Wiz.Elab`), so they're listed with each parser.

Notation: `[x]` means "a `null` node", so `optional p` gives `[]` or `[p...]`.

```
quantity          := num | "ω" | "%" term
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

/-- `0`, `1`, `ω`, or `%t` for a quantity-valued term (stage 4d). -/
def quantity : ParserDescr :=
  node "quantity" (orelse num (orelse (atom "ω") (seqs ["%", noWs, cat "term" maxPrec])))

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

/-- `[x : C A]` or `[C A]`: an instance-implicit binder (stage 7) -/
def instBinder : ParserDescr :=
  node "binder.inst" <| seqs ["[", withoutPosition <| seqs [optional (seqs [ident, ":"]), term], "]"]

def bracketedBinder (requireType : Bool) : ParserDescr :=
  orelse (explicitBinder requireType) (orelse (implicitBinder requireType) instBinder)

/-- Binders of `fun` and `∀`: a bare name or a bracketed group with optional type. -/
def simpleBinder : ParserDescr := orelse (bracketedBinder false) binderIdent

/-- `| p₁, …, pₙ => rhs` -/
def matchAlt : ParserDescr :=
  node "match.alt" (seqs ["|", sepBy1 (cat "term" 0) ",", "=>", cat "term" 0])

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
| `term.field` (trailing) | max | t "." ident (a Σ field, or `T.f t` for a nominal `T`) |
| `term.letPair`       | lead | "let" [quantity] "(" ident "," ident ")" ":=" term [";"] term |
| `term.absurd`        | lead | "absurd" term |
| `term.eq` (trailing) | 50   | a "=" b |
| `term.refl`          | lead | "refl" term |
| `term.rfl`           | max  | "rfl" |
| `term.cast`          | lead | "cast" term term |
| `term.transp`        | lead | "transp" term term term |
| `term.enum`          | max  | "Enum" "[" [idents] "]" |
| `term.tag`           | max  | "'" ident |
| `term.ecase`         | lead | "ecase" term "[" [terms] "]" |
| `term.dotIdent`      | max  | "." ident (a constructor of the expected type) |
| `term.match`         | lead | "match" [terms] "with" [alts] |
| `term.szInf`, `term.szSuc`, `term.sizeLt` | | "∞", "↑" s, "Size<" s |
| `term.sized` (trailing) | max | T "^" s: an inductive or coinductive type at size `s` |

The data primitives `Desc`, `Desc.ret`, `Desc.arg`, `Desc.rec`, `Desc.elim`,
`Desc.interp`, `Desc.All`, `μ`, `ν`, `con`, `ind`, `out` and `coit` have no syntax of their
own: they are names the elaborator recognises when applied (unless shadowed).

Field access by name (`p.x`) needs no syntax: `p.x` lexes as one dotted identifier,
and the elaborator resolves it.
-/
def termLeading : List LeadingParser := [
  { kind := "term.ident", prec := maxPrec, p := ident },
  { kind := "term.num", prec := maxPrec, p := num },
  { kind := "term.omega", prec := maxPrec, p := "ω" },
  { kind := "term.str", prec := maxPrec, p := str },
  -- the level must be right of the enclosing position: in a structure, `op : Type` and a
  -- field `ret` on the next line are two fields, not `Type ret`
  { kind := "term.type", prec := maxPrec, p := seqs ["Type", optional (seqs [checkPrec leadPrec, colGt, level maxPrec])] },
  { kind := "term.sort", prec := maxPrec, p := seqs ["Sort", optional (seqs [checkPrec leadPrec, colGt, level maxPrec])] },
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
  { kind := "term.absurd", prec := leadPrec, p := seqs ["absurd", term maxPrec] },
  { kind := "term.refl", prec := leadPrec, p := seqs ["refl", term maxPrec] },
  { kind := "term.rfl", prec := maxPrec, p := "rfl" },
  { kind := "term.cast", prec := leadPrec, p := seqs ["cast", term maxPrec, term maxPrec] },
  { kind := "term.transp", prec := leadPrec, p := seqs ["transp", term maxPrec, term maxPrec, term maxPrec] },
  { kind := "term.enum", prec := maxPrec, p := seqs [nonReserved "Enum", "[", sepBy ident ",", "]"] },
  { kind := "term.tag", prec := maxPrec, p := seqs ["'", noWs, ident] },
  { kind := "term.dotIdent", prec := maxPrec, p := seqs [".", noWs, ident] },
  { kind := "term.szInf", prec := maxPrec, p := "∞" },
  { kind := "term.szSuc", prec := maxPrec, p := seqs ["↑", term maxPrec] },
  { kind := "term.sizeLt", prec := leadPrec, p := seqs ["Size<", term maxPrec] },
  { kind := "term.match", prec := leadPrec,
    -- alternatives line up at or right of the first `|`, so an outer match's next
    -- alternative ends a nested match (as in Lean)
    p := seqs ["match", sepBy1 term ",", "with", withPosition (many1 (seqs [colGe, matchAlt]))] },
  -- tactics line up (or are separated by `;`); the tactics themselves come from the prelude
  { kind := "term.by", prec := leadPrec,
    p := seqs ["by", withPosition (many1 (seqs [colGe, cat "tactic" 0, optional ";"]))] },
  { kind := "term.ecase", prec := leadPrec,
    p := seqs [nonReserved "ecase", term maxPrec, "[", withoutPosition (sepBy term ","), "]"] }
]

def termTrailing : List TrailingParser := [
  { kind := "term.app", prec := leadPrec, lhsPrec := maxPrec,
    p := many1 (seqs [colGt, term argPrec]) },
  { kind := "term.arrow", prec := 25, lhsPrec := 26, p := seqs [arrow, term 25] },
  { kind := "term.prod", prec := 35, lhsPrec := 36, p := seqs ["×", term 35] },
  { kind := "term.eq", prec := 50, lhsPrec := 51, p := seqs ["=", term 51] },
  { kind := "term.proj", prec := maxPrec, lhsPrec := maxPrec, p := seqs [noWs, ".", noWs, num] },
  { kind := "term.field", prec := maxPrec, lhsPrec := maxPrec, p := seqs [noWs, ".", noWs, ident] },
  { kind := "term.sized", prec := maxPrec, lhsPrec := maxPrec, p := seqs [noWs, "^", term maxPrec] }
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
| `command.inductive`          | "inductive" ident [".{" us "}"] [binders] [":" T] "where" [ctors] |
| `command.structure`          | "structure" ident [".{" us "}"] [binders] [":" T] "where" [fields] |
| `command.coinductive`        | like `structure`; the fields are observations |
| `command.defEqns`            | "def" ident [".{" us "}"] [binders] ":" T [alts] |

A constructor is `inductive.ctor`: "|" ident [binders] [":" T]. A field is
`structure.field`: [quantity] ident ":" T, on its own line.
-/
def commandLeading : List LeadingParser := [
  { kind := "command.def", prec := maxPrec,
    p := seqs ["def", ident, univParams, many (bracketedBinder false), typeSpec false, ":=", term] },
  { kind := "command.defEqns", prec := maxPrec,
    p := seqs ["def", ident, univParams, many (bracketedBinder false), typeSpec true, many1 matchAlt] },
  { kind := "command.axiom", prec := maxPrec,
    p := seqs ["axiom", ident, univParams, many (bracketedBinder false), typeSpec true] },
  { kind := "command.check", prec := maxPrec, p := seqs ["#check", term] },
  { kind := "command.reduce", prec := maxPrec, p := seqs ["#reduce", term] },
  { kind := "command.eval", prec := maxPrec, p := seqs ["#eval", term] },
  { kind := "command.erase", prec := maxPrec, p := seqs ["#erase", ident] },
  { kind := "command.import", prec := maxPrec, p := seqs ["import", ident] },
  -- stage 8: run through the backend pipeline (IR, reference counting), print the IR
  { kind := "command.run", prec := maxPrec, p := seqs ["#run", term] },
  { kind := "command.ir", prec := maxPrec, p := seqs ["#ir", ident] },
  { kind := "command.builtin", prec := maxPrec, p := seqs ["builtin", ident, ":=", ident] },
  -- stage 9: a foreign (C) function
  { kind := "command.glue", prec := maxPrec,
    p := seqs ["glue", ident, many (bracketedBinder false), ":", term, ":=", str] },
  { kind := "command.foreignType", prec := maxPrec,
    p := seqs ["foreign_type", ident, optional (seqs ["(", nonReserved "finalizer", ":=", str, ")"])] },
  { kind := "command.importC", prec := maxPrec,
    p := seqs ["import_c", str, optional (seqs ["(", nonReserved "pure", ")"])] },
  { kind := "command.extern", prec := maxPrec,
    p := seqs ["extern", str, optional (seqs ["(", nonReserved "header", ":=", str, ")"]), ident, ":", term] },
  { kind := "command.attrMacro", prec := maxPrec,
    p := seqs ["attribute", "[", nonReserved "macro", ident, "]", ident] },
  { kind := "command.attrTactic", prec := maxPrec,
    p := seqs ["attribute", "[", nonReserved "tactic", ident, "]", ident] },
  { kind := "command.declareSyntaxCat", prec := maxPrec, p := seqs ["declare_syntax_cat", ident] },
  { kind := "command.syntax", prec := maxPrec,
    p := seqs ["syntax", optional (seqs [noWs, ":", noWs, precedence]),
      optional (seqs ["(", nonReserved "name", ":=", ident, ")"]),
      optional (seqs ["(", nonReserved "priority", ":=", num, ")"]),
      many1 (cat "stx" 0), ":", ident] },
  { kind := "command.inductive", prec := maxPrec,
    p := seqs ["inductive", ident, univParams, many (bracketedBinder false), optional (seqs [":", term]),
      "where", many (node "inductive.ctor" (seqs ["|", ident, many (bracketedBinder false),
        optional (seqs [":", term])]))] },
  { kind := "command.structure", prec := maxPrec,
    p := seqs ["structure", ident, univParams, many (bracketedBinder false), optional (seqs [":", term]),
      "where", many (node "structure.field" (withPosition (seqs [optional quantity, ident, ":", term])))] },
  -- stage 7: a class is a structure whose values are found by instance resolution
  { kind := "command.class", prec := maxPrec,
    p := seqs ["class", ident, univParams, many (bracketedBinder false), optional (seqs [":", term]),
      "where", many (node "structure.field" (withPosition (seqs [optional quantity, ident, ":", term])))] },
  { kind := "command.instance", prec := maxPrec,
    p := seqs ["instance", optional (seqs ["(", nonReserved "priority", ":=", num, ")"]),
      many (bracketedBinder false), ":", term,
      orelse (seqs [":=", term])
        (seqs ["where", withPosition (many1 (node "instance.field" (seqs [colGe, ident, ":=", term])))])] },
  { kind := "command.coinductive", prec := maxPrec,
    p := seqs ["coinductive", ident, univParams, many (bracketedBinder false), optional (seqs [":", term]),
      "where", many (node "structure.field" (withPosition (seqs [optional quantity, ident, ":", term])))] }
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

/-- Metaprogramming support for a category `c`: antiquotations `$x` inside it, and the
quotation `` `(c| …) `` as a term.

An antiquotation wins ties against the category's other rules (a user rule like
`syntax term : doSeq` would otherwise also read `$x` as a `doSeq`). To mean the
other reading, annotate the category: in a `doSeq`, `$x:term` is a term, because
it consumes more input than the `doSeq` antiquotation `$x`. -/
def addMetaParsers (t : ParserTables) (c : Name) : ParserTables :=
  let plain := seqs ["$", noWs, ident]
  let annotated := seqs ["$", noWs, ident, noWs, ":", noWs, nonReserved c]
  let t := t.addLeading c { kind := "antiquot", prec := maxPrec, priority := 1000, p := plain }
  let t := t.addLeading c { kind := "antiquot", prec := maxPrec, priority := 1000, p := annotated }
  let q : LeadingParser :=
    { kind := "quote." ++ c, prec := maxPrec,
      p := seqs ["`(", nonReserved c, "|", withoutPosition (cat c 0), ")"] }
  t.addLeading "term" q

/-- Macro commands.

| kind                   | children |
|------------------------|----------|
| `command.macroRules`   | "macro_rules" [alts] (each `| `(c| pattern) => `(c| template)`) |
| `command.notation`     | "notation" [":" prec] [items] "=>" term (items: str or ident [":" prec]) |
| `command.infix`        | ("infixl" / "infixr" / "infix") ":" num str "=>" term |
-/
def macroCommands : List LeadingParser := [
  { kind := "command.macroRules", prec := maxPrec, p := seqs ["macro_rules", many1 matchAlt] },
  { kind := "command.notation", prec := maxPrec,
    p := seqs ["notation", optional (seqs [noWs, ":", noWs, precedence]),
      many1 (node "notation.item" (orelse str (seqs [ident, optional (seqs [noWs, ":", noWs, precedence])]))),
      "=>", term] },
  { kind := "command.infix", prec := maxPrec,
    p := seqs [orelse "infixl" (orelse "infixr" "infix"), noWs, ":", noWs, num, str, "=>", term] }
]

def tables : ParserTables :=
  let t : ParserTables := {}
  let t := ["term", "command", "stx", "level", "tactic"].foldl ParserTables.declareCategory t
  let t := levelLeading.foldl (·.addLeading "level" ·) t
  let t := levelTrailing.foldl (·.addTrailing "level" ·) t
  let t := termLeading.foldl (·.addLeading "term" ·) t
  let t := termTrailing.foldl (·.addTrailing "term" ·) t
  let t := commandLeading.foldl (·.addLeading "command" ·) t
  let t := stxLeading.foldl (·.addLeading "stx" ·) t
  let t := stxTrailing.foldl (·.addTrailing "stx" ·) t
  let t := macroCommands.foldl (·.addLeading "command" ·) t
  ["term", "command", "level", "tactic"].foldl addMetaParsers t

end Wiz.Builtin
