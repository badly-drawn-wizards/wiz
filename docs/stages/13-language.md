# Stage 13: the language, for programs this size

Writing the lexer and parser in Wiz showed what the language lacked:

* **Recursion on any argument.** The structural argument is the first one the first
  clause matches; parameters before the colon may be passed unchanged or left out.
* **`partial def` and `mutual … end`.** General recursion: the kernel treats the
  definition as opaque, justified by a witness of its type (22f, so no `False`), and its
  implementation (checked against the type) is what `#eval` and compiled code run. The
  parser's core is a mutual block, with no fuel.
* **Mutual inductive types.** `mutual inductive A … inductive B … end` becomes one
  family indexed by a tag type, `A_B : A_B.Tag → Type`, with `def A := A_B .A`.
  Recursion over a family at a concrete index (`SyntaxF .false`) works.
* **`match` without an expected type**, **tuple patterns** `(a, b, c)`, and `x |> f`.
* Keywords of tactic syntax (`first`, `exact` …) are no longer reserved words.
* The prelude has `Nat.lt` (native at runtime), `Nat.le`, `Nat.max`, `Bool.and/or/not`.

## 13a: named arguments ✅

```
class BitPack (A : Type) where
  width : Nat
def bitWidth (0 A : Type) [BitPack A] : Nat := BitPack.width (A := A)
def sub (a b : Nat) : Nat := Nat.sub a b
#eval sub (b := 1) 5                    -- 4
#eval @BitPack.width (A := Bool) _
```

As in Lean, an argument `(x := e)` fills the parameter named `x`, wherever it is:
implicit, instance or explicit. The other arguments fill the explicit parameters in
order (with `@f`, every parameter), and implicit and instance parameters before a named
one get metavariables and instance problems. A named argument after the last positional
one fills its parameter; an explicit parameter before it with no argument is an error
(Lean would abstract it). Unknown and repeated names are errors (`inferAppNamed`,
`Elab/Term.lean`; test group `elabfix`).

## 13b: private declarations and private constructors ✅

```
private def secret : Nat := 42          -- visible only in this module
structure Shr (ρ : Region) (A : Type) where
  private mk ::                         -- only this module makes a `Shr`
  val : A
```

`private` before a command makes every name it declares (a definition, an axiom, a
structure with its constructor and projections, an inductive type with its
constructors and recursors) private to its **module**: other modules get "'x' is
private to module M"; the module itself, including its later declarations, uses the
names as usual. Privacy is per module ([23c](23-grail.md): each module is elaborated in isolation and
under its own name), and the main file is a module of its own.

`private mk ::` right after a structure's `where` keeps the type and its projections
public but makes the constructor private. Types are structural, so a private name
alone would not stop another module from building a value: a tuple `(5, ())`, or a
structure of its own with the same fields, converts to the type. So outside its module
such a structure is also **opaque** to the elaborator: its definition doesn't unfold
(`Globals.elabView`), it is equal only to itself, and `p.val` reads it through the
projection function `S.val` (`p.1` doesn't work). Within the module nothing changes.
Like Lean's, privacy is enforced by the elaborator: the kernel checks every declaration
against the full environment, where an opaque structure is its Σ again (which is sound:
whatever converts with the definition hidden converts with it unfolded).

The motivating use is `lib/Region.wiz` ([22g](22-numbers.md)): the constructors of the borrow handles
`Shr`, `Uniq`, `Mut` and `Lent` are private, so a handle at a region comes only from a
scope or an operation of the library, and hand-written Wiz can't forge one
(`drafts/rust/rejected/forge_handle.wiz`; test group `regions`). `MutOpt`'s constructors
stay public: their fields are handles already.

```
inductive Tok where
  | num (n : Nat)
  | private secret (n : Nat)            -- only this module makes a `.secret`
coinductive Signal (d : Domain) (A : Type) where
  private head : A                      -- only this module observes a signal
  private tail : Signal d A
structure Acct where
  owner : Nat
  private bal : Nat                     -- `Acct.bal` is private; `Acct.mk` isn't
```

The same opacity covers the other declarations with private parts. In each case the
private names are private to the module, and **elsewhere the type is opaque**: it is a
type constant that equals only itself, so the primitives (`con`, `cocon`, `out`, `.1`),
tuples and look-alike types don't convert to it.

* `| private c …` (an `inductive`): `T.c` is private, and so are the recursors `T.rec`,
  `T.casesOn` (and `scasesOn`, `recN`, `casesOnN`). The public constructors stay usable,
  also as `.c` against an expected `T`. Outside the module a `T` can't be **matched**,
  not even on its public constructors with a catch-all: a `match` compiles to
  `T.casesOn`, whose case for `c` hands out `c`'s fields, and the case tree needs `T`'s
  description, which is what the opacity hides. So exhaustiveness never comes up
  there; the module exports the eliminators it wants (`Tok.value`, or a fold). In a
  `mutual` block the types are one indexed family, so a private constructor makes the
  whole family opaque.
* `private f : A` (an observation of a `coinductive`): `T.f` is private, and so is the
  coconstructor `T.mk` (it would build a value from the private observation's value).
  Outside the module a `T` isn't observed through `f` (`s.f`, `T.f s`, `out s`) and
  isn't defined by **copatterns**, which give every observation ("'Signal.head' is
  private to module Signal: a Signal can't be defined by copatterns outside it"); public
  observations are read through their functions, `s.g`.
* `private f : A` (a field of a `structure`): `S.f` is private and `S` is opaque
  elsewhere, as with `private mk ::`; the constructor stays public unless it is
  `private mk ::` too. A class's methods can't be private.
* A type declared `private` (`private inductive T`) is not opaque, but its recursors are
  private, so a value of it that reaches another module (through a public definition)
  isn't matched there either.

All of this is elaboration only, as above: the kernel checks against the full
environment, and whatever the elaborator accepts with `T`'s definition hidden also
checks with it unfolded. The self-hosted frontend parses the `private` markers and
ignores them. The motivating use is the HDL's signals (`drafts/hdl/Signal.wiz`): user
code builds and observes them only through the library's combinators and `sample`
(`drafts/hdl/rejected/observe_signal.wiz`). Tests: group `elabfix`.

## 13j: keyword scopes ✅

A keyword of a `term` or `command` rule is reserved in the whole file; a keyword of any
other category is reserved nowhere (`"if"` there matches an identifier spelled `if`).
That is right for tactics, whose names stay usable as variables, and wrong for an
embedded language with identifiers and application by juxtaposition: its `ident` rule
accepts `then` too, so `if c then a else b` is the application of `if` to five arguments.
Reserving the words globally (by listing them in a `command` rule) takes `if`, `in`,
`mut`, `fn` … away from every file that imports the language.

```
declare_syntax_cat feral_expr (keywords := feral)
declare_syntax_cat feral_stmt (keywords := feral)
```

puts the categories in the **keyword scope** `feral`. The identifier-like atoms of their
rules are the scope's keywords, and an `ident` item inside a category of the scope does
not match them:

* inside the language, `if c then a else b` is the `if` rule, and `let if := 1` is
  `expected identifier ('if' is a keyword here)`;
* outside it (in `term`, in `command`, in another language, and in a `term` nested
  inside the language) the words are ordinary identifiers;
* categories share a scope by naming it, because a keyword of statements (`return`) must
  not be an identifier of expressions (or `f x` and a `return y` on the next line are
  one application).

The scope's name is an identifier, so it can't be a word that is reserved at that point
(declare the categories before the `syntax "feral" … : command` rule, or pick another
name). A category keeps the scope it was first declared with. Symbol atoms (`+=`, `..`)
are still tokens everywhere: they never take an identifier away.

The parser stays scannerless with one token table (`Wiz/Parser/Token.lean`): the scope is
a property of the category being parsed (`ParserTables.reservedIn`, read by the `ident`
case of `runDescr`), so the memo key, which already names the category, is unchanged.
The design options are in the notes (`scoped-keywords.md`). The self-hosted parser
interprets the built-in tables, which use no scope, and has no `syntax` command yet.
Tests: `parser: commands and syntax`, `language`.
