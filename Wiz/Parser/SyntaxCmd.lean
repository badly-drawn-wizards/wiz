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
  sorry

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
  sorry

end Wiz
