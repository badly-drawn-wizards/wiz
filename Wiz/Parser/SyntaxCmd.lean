import Wiz.Parser.Descr

/-!
# The `syntax` command

```
syntax "if" term "then" term "else" term : term
syntax:65 term:65 " + " term:66 : term
syntax (name := myList) "[" sepBy(term, ",") "]" : term
```

translates the parsed declaration into a `ParserDescr` and registers it.

* If the first item is the target category itself (`term:65` above), the rule is
  **trailing**: that item is the left-hand side, its precedence is `lhsPrec`, and the
  rest of the items form the parser.
* Otherwise it is **leading**.
* The rule's own precedence is `syntax:prec`, defaulting to `maxPrec`.
* Atoms are trimmed, since `" + "` is written with spaces for readability.
* The node kind is the given `name`, or else generated from the category and atoms,
  such as `term.if_then_else` or `term.+`, with `_1`, `_2`, ... appended if that kind
  already exists. Generated names depend only on declaration order, which keeps them
  deterministic.
-/

namespace Wiz

/-- `prec := num | max | arg | lead | min` -/
def precValue (s : Syntax) : Except String Nat :=
  match s.getArg 0 with
  | .ident _ "max" => pure maxPrec
  | .ident _ "arg" => pure argPrec
  | .ident _ "lead" => pure leadPrec
  | .ident _ "min" => pure minPrec
  | n => match n.getNat? with
    | some v => pure v
    | none => throw s!"invalid precedence {s}"

/-- **Exercise 2.6a.** Translate one `stx` item into a descriptor. See the table in
`Builtin.stxLeading` for the shapes. Category references must name a declared
category (look in `tables.cats`), except for the special names `ident`, `num`, `str`,
`colGt`, `colGe` and `noWs`. A category without a precedence means precedence 0. -/
partial def stxToDescr (tables : ParserTables) (s : Syntax) : Except String ParserDescr :=
  --<sol
  let items (n : Syntax) : Except String ParserDescr := do
    let ps ← n.args.mapM (stxToDescr tables)
    pure (if h : ps.size = 1 then ps[0] else .seq ps)
  match s.kind with
  | "stx.atom" => match (s.getArg 0).getStr? with
    | some v => pure (.atom v.trimAscii.toString)
    | none => throw "malformed stx.atom"
  | "stx.cat" => do
    let some c := (s.getArg 0).getId? | throw "malformed stx.cat"
    let precOpt := s.getArg 1
    let prec ← if precOpt.isNone then pure 0 else precValue (precOpt.getArg 1)
    match c with
    | "ident" => pure .ident
    | "num" => pure .num
    | "str" => pure .str
    | "colGt" => pure .colGt
    | "colGe" => pure .colGe
    | "noWs" => pure .noWs
    | _ =>
      unless tables.cats.contains c do throw s!"unknown syntax category {c}"
      pure (.cat c prec)
  | "stx.group" => items (s.getArg 1)
  | "stx.sepBy" | "stx.sepBy1" => do
    let p ← items (s.getArg 2)
    let some sep := (s.getArg 4).getStr? | throw "malformed sepBy"
    let trailing := !(s.getArg 5).isNone
    let sep := sep.trimAscii.toString
    pure (if s.kind == "stx.sepBy" then .sepBy p sep trailing else .sepBy1 p sep trailing)
  | "stx.withPosition" => return .withPosition (← items (s.getArg 2))
  | "stx.many" => return .many (← stxToDescr tables (s.getArg 0))
  | "stx.many1" => return .many1 (← stxToDescr tables (s.getArg 0))
  | "stx.optional" => return .optional (← stxToDescr tables (s.getArg 0))
  | k => throw s!"unexpected syntax item of kind {k}"
  --sol>

/-- Generate a fresh kind name from the category and the atoms of the rule. -/
def mkKindName (tables : ParserTables) (cat : Name) (p : ParserDescr) : Name :=
  let toks := p.tokens
  let base := cat ++ "." ++ (if toks.isEmpty then "syntax" else "_".intercalate toks)
  if !tables.kinds.contains base then base else go base 1 (tables.kinds.size + 1)
where
  go (base : Name) (i : Nat) : Nat → Name
    | 0 => base ++ "_" ++ toString i
    | fuel + 1 =>
      let n := base ++ "_" ++ toString i
      if tables.kinds.contains n then go base (i + 1) fuel else n

/-- **Exercise 2.6b.** Process a `command.syntax` node (see `Builtin.commandLeading`
for its children) and register the rule. Decide leading vs trailing as described in
the module docstring. The target category must exist. -/
def addSyntax (tables : ParserTables) (cmd : Syntax) : Except String ParserTables := do
  --<sol
  let some cat := (cmd.getArg 6).getId? | throw "malformed syntax command"
  unless tables.cats.contains cat do throw s!"unknown syntax category {cat}"
  let precOpt := cmd.getArg 1
  let prec ← if precOpt.isNone then pure maxPrec else precValue (precOpt.getArg 1)
  let nameOpt := cmd.getArg 2
  let prioOpt := cmd.getArg 3
  let priority := if prioOpt.isNone then 0 else ((prioOpt.getArg 3).getNat?).getD 0
  let items := (cmd.getArg 4).args
  let some first := items[0]? | throw "empty syntax rule"
  let isTrailing := first.isOfKind "stx.cat" && (first.getArg 0).getId? == some cat
  let rest := if isTrailing then items.extract 1 items.size else items
  let ps ← rest.mapM (stxToDescr tables)
  let p := if h : ps.size = 1 then ps[0] else .seq ps
  let kind := match nameOpt.getArg 3 |>.getId? with
    | some n => cat ++ "." ++ n
    | none => mkKindName tables cat p
  if isTrailing then
    let lhsOpt := first.getArg 1
    let lhsPrec ← if lhsOpt.isNone then pure 0 else precValue (lhsOpt.getArg 1)
    pure (tables.addTrailing cat { kind, prec, lhsPrec, priority, p })
  else
    pure (tables.addLeading cat { kind, prec, priority, p })
  --sol>

end Wiz
