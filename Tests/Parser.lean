import Wiz
import Tests.Harness

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Parser

def chars (s : String) : Array Char := s.toList.toArray

def lexGroup : Group where
  name := "lexer"
  exercise := "Exercises 2.1–2.3"
  cases := [
    { name := "skip spaces and newlines", run := fun _ => checkEq 4 (skipWs (chars "  \n x") 0) },
    { name := "line comment", run := fun _ => checkEq 11 (skipWs (chars "-- hello\n  x") 0) },
    { name := "block comment", run := fun _ => checkEq 8 (skipWs (chars "/- a -/ x") 0) },
    { name := "nested block comment",
      run := fun _ => checkEq 18 (skipWs (chars "/- a /- b -/ c -/ x") 0) },
    { name := "unterminated block comment runs to the end",
      run := fun _ => checkEq 7 (skipWs (chars "/- abc ") 0) },
    { name := "a lone '-' is not a comment", run := fun _ => checkEq 1 (skipWs (chars " - x") 0) },
    { name := "identifier", run := fun _ => checkEq ("foo_1'", 6) (readIdent (chars "foo_1' x") 0) },
    { name := "dotted identifier", run := fun _ => checkEq ("Nat.add", 7) (readIdent (chars "Nat.add") 0) },
    { name := "trailing dot is not part of an identifier",
      run := fun _ => checkEq ("x", 1) (readIdent (chars "x. y") 0) },
    { name := "greek and subscripts", run := fun _ => checkEq ("α₁", 2) (readIdent (chars "α₁ ") 0) },
    { name := "string with escapes", run := fun _ =>
        match readStr (chars "\"a\\n\\\"b\\\\\" rest") 0 with
        | .ok (s, j) => do checkEq "a\n\"b\\" s; checkEq 10 j
        | .error e => throw (IO.userError e) },
    { name := "unterminated string", run := fun _ =>
        check (readStr (chars "\"abc") 0 matches .error _) "expected an error" },
    { name := "longest token", run := fun _ =>
        checkEq (some "=>") (longestToken #["=", "=>", ">"] (chars "=> x") 0) },
    { name := "no token", run := fun _ =>
        checkEq none (longestToken #["=", "=>"] (chars "+") 0) }
  ]

def parseTerm (s : String) (tables := Builtin.tables) : IO String :=
  match parseCategory tables "term" s with
  | .ok stx => pure stx.toSExpr
  | .error e => throw (IO.userError s!"parse error: {e}")

def parses (input expected : String) : IO Unit := do
  checkEq expected (← parseTerm input)

def fails (input : String) (errFragment : String) : IO Unit :=
  match parseCategory Builtin.tables "term" input with
  | .ok stx => throw (IO.userError s!"expected a parse error, got {stx}")
  | .error e => check ((e.splitOn errFragment).length > 1) s!"error {e} does not mention {errFragment}"

def termGroup : Group where
  name := "parser: terms"
  exercise := "Exercises 2.4–2.5"
  cases := [
    { name := "identifier", run := fun _ => parses "x" "(term.ident x)" },
    { name := "application", run := fun _ =>
        parses "f a b" "(term.app (term.ident f) [(term.ident a) (term.ident b)])" },
    { name := "arrow is right associative", run := fun _ =>
        parses "A → B -> C"
          "(term.arrow (term.ident A) (term.arrow (term.ident B) (term.ident C)))" },
    { name := "application binds tighter than →", run := fun _ =>
        parses "f a → b" "(term.arrow (term.app (term.ident f) [(term.ident a)]) (term.ident b))" },
    { name := "Type and Type 1", run := fun _ => do
        parses "Type" "(term.type [])"
        parses "Type 1" "(term.type [1])" },
    { name := "parenthesis vs ascription", run := fun _ => do
        parses "(x)" "(term.paren (term.ident x))"
        parses "(x : A)" "(term.ascription (term.ident x) (term.ident A))" },
    { name := "dependent arrow with quantity (longest match beats ascription)", run := fun _ =>
        parses "(1 x : A) → B"
          "(term.depArrow (binder.explicit [(quantity 1)] [x] [(term.ident A)]) (term.ident B))" },
    { name := "implicit erased binder, several names", run := fun _ =>
        parses "{0 A B : Type} → A"
          "(term.depArrow (binder.implicit [(quantity 0)] [A B] [(term.type [])]) (term.ident A))" },
    { name := "ω quantity", run := fun _ =>
        parses "(ω f : A) → A"
          "(term.depArrow (binder.explicit [(quantity)] [f] [(term.ident A)]) (term.ident A))" },
    { name := "fun with mixed binders", run := fun _ =>
        parses "fun x (1 y : A) {B} _ => y"
          "(term.fun [x (binder.explicit [(quantity 1)] [y] [(term.ident A)]) (binder.implicit [] [B] []) (term.hole)] (term.ident y))" },
    { name := "λ and ↦", run := fun _ => parses "λ x ↦ x" "(term.fun [x] (term.ident x))" },
    { name := "fun as last argument", run := fun _ =>
        parses "f fun x => x" "(term.app (term.ident f) [(term.fun [x] (term.ident x))])" },
    { name := "∀", run := fun _ =>
        parses "∀ (A : Type) x, A"
          "(term.forall [(binder.explicit [] [A] [(term.type [])]) x] (term.ident A))" },
    { name := "let with semicolon", run := fun _ =>
        parses "let 1 x : A := f a; x"
          "(term.let [(quantity 1)] x [(term.ident A)] (term.app (term.ident f) [(term.ident a)]) [] (term.ident x))" },
    { name := "let with layout: next line is the body, not an argument", run := fun _ =>
        parses "let x := f a\nx"
          "(term.let [] x [] (term.app (term.ident f) [(term.ident a)]) [] (term.ident x))" },
    { name := "let with indented continuation is an argument", run := fun _ =>
        parses "let x := f\n  a; x"
          "(term.let [] x [] (term.app (term.ident f) [(term.ident a)]) [] (term.ident x))" },
    { name := "holes and explicit", run := fun _ =>
        parses "@f _ ?m" "(term.app (term.explicit f) [(term.hole) (term.syntheticHole m)])" },
    { name := "comments are whitespace", run := fun _ =>
        parses "f /- a /- nested -/ -/ b -- c" "(term.app (term.ident f) [(term.ident b)])" },
    { name := "error: missing body", run := fun _ => fails "fun x =>" "term" },
    { name := "error: unbalanced paren", run := fun _ => fails "(f a" "')'" },
    { name := "error reports the farthest position", run := fun _ => fails "f (a b" "1:7" },
    { name := "deep nesting is fast (packrat memo)", run := fun _ => do
        let n := 40
        let s := String.join (List.replicate n "(") ++ "x" ++ String.join (List.replicate n ")")
        let _ ← parseTerm s }
  ]

def parseFileOk (input : String) : IO ParsedFile := do
  let r := parseFile input
  unless r.messages.isEmpty do
    throw (IO.userError s!"errors: {r.messages.map (·.render input)}")
  pure r

def cmdGroup : Group where
  name := "parser: commands and syntax"
  exercise := "Exercises 2.4–2.6"
  cases := [
    { name := "def with binders and type", run := fun _ => do
        let r ← parseFileOk "def id {0 A : Type} (1 x : A) : A := x"
        checkEq "(command.def id [(binder.implicit [(quantity 0)] [A] [(term.type [])]) (binder.explicit [(quantity 1)] [x] [(term.ident A)])] [(term.ident A)] (term.ident x))"
          r.commands[0]!.toSExpr },
    { name := "commands split by layout", run := fun _ => do
        let r ← parseFileOk "def a := f\n  x\n#check a\naxiom b : Type"
        checkEq 3 r.commands.size
        checkEq "(command.def a [] [] (term.app (term.ident f) [(term.ident x)]))" r.commands[0]!.toSExpr },
    { name := "error recovery", run := fun _ => do
        let r := parseFile "def a := (\ndef b := x\n#check b"
        checkEq 1 r.messages.size
        checkEq 2 r.commands.size },
    { name := "leading syntax: if-then-else", run := fun _ => do
        let r ← parseFileOk "syntax \"if\" term \"then\" term \"else\" term : term\n#check if a then b else c"
        checkEq "(command.check (term.if_then_else (term.ident a) (term.ident b) (term.ident c)))"
          r.commands[1]!.toSExpr },
    { name := "trailing syntax with precedence: + and *", run := fun _ => do
        let r ← parseFileOk ("syntax:65 term:65 \" + \" term:66 : term\n" ++
          "syntax:70 term:70 \" * \" term:71 : term\n#check a + b * c + d")
        checkEq "(command.check (term.+ (term.+ (term.ident a) (term.* (term.ident b) (term.ident c))) (term.ident d)))"
          r.commands[2]!.toSExpr },
    { name := "application binds tighter than user infix", run := fun _ => do
        let r ← parseFileOk "syntax:65 term:65 \" + \" term:66 : term\n#check f a + g b"
        checkEq "(command.check (term.+ (term.app (term.ident f) [(term.ident a)]) (term.app (term.ident g) [(term.ident b)])))"
          r.commands[1]!.toSExpr },
    { name := "named rule with sepBy", run := fun _ => do
        let r ← parseFileOk "syntax (name := list) \"[\" sepBy(term, \",\") \"]\" : term\n#check [a, b, c]"
        checkEq "(command.check (term.list [(term.ident a) (term.ident b) (term.ident c)]))"
          r.commands[1]!.toSExpr },
    { name := "custom category with many", run := fun _ => do
        let r ← parseFileOk ("declare_syntax_cat item\nsyntax ident \"=\" num : item\n" ++
          "syntax \"items\" item* \"end\" : term\n#check items a = 1 b = 2 end")
        checkEq "(command.check (term.items_end [(item.= a 1) (item.= b 2)]))" r.commands[3]!.toSExpr },
    { name := "new keywords are reserved afterwards", run := fun _ => do
        let r := parseFile "syntax \"if\" term \"then\" term \"else\" term : term\ndef if := x"
        checkEq 1 r.messages.size },
    { name := "later rule overrides an equally long earlier one", run := fun _ => do
        let r ← parseFileOk "syntax (name := a) \"foo\" : term\nsyntax (name := b) \"foo\" : term\n#check foo"
        checkEq "(command.check (term.b))" r.commands[2]!.toSExpr },
    { name := "unknown category is an error", run := fun _ => do
        let r := parseFile "syntax \"x\" : nope"
        checkEq 1 r.messages.size }
  ]

end Tests.Parser
