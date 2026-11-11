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
under its own name), and the main file is a module of its own. In a module, a private
function, axiom or foreign function gets a kernel name of its own (`_private.M.0.secret`,
as in Lean), so two modules' private `secret`s don't clash; see
[23b](23-grail.md).

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

**The elaborator never leaves a comparison to the kernel.** The other direction is not
sound for privacy: the kernel accepts what converts with the definition *unfolded*, so a
check that the elaborator skips is answered by shape. `rfl` used to be such a check: at a
stuck equation `X = Y` it produced `reflTy X` and let the kernel compare `X` with `Y`.
For a look-alike `structure Look (A) where val : A`, `rfl : Look Nat = Pos Nat` was
accepted, and `cast` along it made a `Pos Nat` without `Pos.mk` (against `lib/Region.wiz`,
a `Shr ρ Nat` at any region). Now `rfl` compares the two sides itself, in its own view
(`sameSides` in `Elab/Term.lean`: unification, then the type-directed conversion with
the elaborator's globals), for values as well as types, and at every equation left
inside one that has computed (`rflProof`). A false `rfl` is reported at the `rfl`
("rfl: the two sides are not definitionally equal"), not as "kernel rejected …", and
`first | rfl | …` in a tactic can fail. The proof that structural recursion passes to an
induction hypothesis at a concrete index (`trivialProof`) is compared the same way.

What this does and does not give. It stops the *elaborator* from producing an equation
between a private type and a look-alike. The kernel still considers the two types
equal, so a term that reaches the kernel without the elaborator comparing its types
would still be accepted:

| path | status |
|---|---|
| `rfl` at a type or value equation, also under pairs, functions and data types | closed |
| `refl X`, `cast e x`, `transp`, a tuple or look-alike against the type, `p.1` | closed (their types are unified in the elaborator's view) |
| `exact`, `rfl` and other tactics that elaborate syntax; macros (they produce syntax) | closed (they go through the same rules) |
| the tactic request `assign` with a term that still has holes | closed: such a term is kept in the tactic state and its type is inferred and compared with its goal at the end of the `by` block (it was a real bypass: `K x ?n : Look Nat` for a goal `Pos Nat`) |
| a hole solved by unification: the solution is never type-checked by the elaborator | **OPEN, with a forgery**: `def sel {F : Pos Nat → Type} (p : Pos Nat) (w : F p) : Pos Nat := p` and `sel _ (G.mk x)` for `G : Look Nat → Type` solve `?F := G`, `?p := x`, and the kernel accepts `x : Look Nat` as a `Pos Nat` (test `elabfix`, "OPEN"; `/workspace/wiz-notes/structural-probes/priv/forge-unify-first-order.wiz`) |
| the self-hosted frontend (`selfhost/Frontend.wiz`) | open, tracked as a parity item: it parses `private` and ignores it |
| `T.desc` of an inductive or coinductive type with private parts: `μ T.desc i` written out is the type with nothing hidden, and a raw `con` builds a value of it | closed: `T.desc` is private with the constructors and recursors (a structure has no description). Generic code over `Desc` in another module can't be pointed at such a type; it could not be applied to its values before either, since the type is opaque there. `deriving` reads the kernel's declarations, not the name, and is unaffected (a derived instance that matches on the type is refused as before) |
| inside the declaring module | by design: there the look-alike is the same type |

So privacy is **not sealed**: it holds against the rules listed as closed, not against
every term the elaborator can produce. Closing it for good needs the kernel to tell a
type from its look-alike (`/workspace/wiz-notes/structural-vs-nominal.md`, §6a).

**`wiz --strict-privacy`** (off by default; an experiment to measure). Every declaration
of a module that sees a type opaque to it is checked a second time, by the kernel's
checker, against the elaborator's view (`privacyCheck`, `Elab/Command.lean`). A
declaration that passes used no hidden shape, so this closes the open path too: the
forgery above is rejected with "forge depends on the definition of Pos (module Priv),
which is hidden outside its module". It is not the default because it also rejects
legitimate proofs that compute through a library operation on such a type: the
elaborator quotes evaluated values into terms, and a raw pair or projection at a type
without a definition does not type-check (`drafts/rust/lowered/03_get_mut.wiz`,
`get_mut.is_place` and `get_mut.spec_under`). With the flag a type with private parts is
abstract for proofs as well.

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

## 13g: as-patterns `x@p` ✅

```
def last (A : Type) (d : A) : List A → A
  | .nil => d
  | .cons x .nil => x
  | .cons _ xs@(.cons _ _) => last A d xs     -- `xs` is the tail that was matched
def dup : List Nat → List Nat
  | .nil => .nil
  | l@(.cons x _) => .cons x l
```

`x@p` (no space around the `@`; `p` an atomic pattern, so a constructor with arguments
goes in parentheses) matches `p` and binds `x` to the value that was matched. It may be
nested anywhere a pattern may, on any kind of pattern (`q@(a, b)`, `n@m@(.succ _)`).

`x` is bound exactly as a variable pattern in that position would be (`compileMatch`,
`Elab/Term.lean`): to the scrutinised variable itself, so no constructor is rebuilt,
unless the goal depends on that variable; then it is the constructor applied to the
fields, which is what has the refined type. Because `x` *is* the matched variable, an
as-pattern on a recursive field is structurally smaller: `last A d xs` above is the
induction hypothesis of the tail. (Without the as-pattern one had to write a helper
that takes the head and the tail separately: "recursive call must be on a variable".)

Limits: when the goal depends on the matched variable, `x` is the rebuilt constructor,
and a recursive call on it is not recognised ("not a recursive field"). In a term,
`x@p` is an error ("only allowed in a pattern").

Not solved by as-patterns: recursion over a family at an index that is not a variable.
`Vec.last : Vec A (Nat.succ n) → A` with `| .cons _ xs@(.cons _ _) => Vec.last xs` now
gets as far as the kernel, which rejects it ("expected: n = .succ (.succ n)"): the
induction hypothesis of a definition matched at the index `succ n` is for that same `n`
(the parameters before the colon are fixed), and the tail is a `Vec A n`. `lib/Vec.wiz`
keeps its helper `Vec.lastFrom`, whose index is a variable that the motive generalises.

Syntax: `term.asPat`, a trailing parser at the highest precedence, `x "@" p` with no
whitespace on either side of the `@`. Explicit application is unchanged, `f @g` and
also `f@g`: where both readings are as long, the application wins, so an as-pattern
whose pattern is a bare name (`x@y`, a second name for the same value) is not available;
`x@_` and `x@(y)` are. Tests: `language` ("as-patterns …"),
`parser: terms`.

## 13h: patterns on structures, `⟨…⟩` ✅

```
structure Stats where
  hits : Nat
  misses : Nat
def total (s : Stats) : Nat := match s with
  | .mk h m => Nat.add h m                 -- also `Stats.mk h m` and `⟨h, m⟩`
def total' (s : Stats) : Nat :=
  let ⟨h, m⟩ := s                           -- or `let (.mk h m) := s`
  Nat.add h m
def stats : Stats := ⟨3, 4⟩                 -- `Stats.mk 3 4`, from the expected type
```

A structure is a Σ type, not a data type, so there is no eliminator to split it with
("cannot match on a value of type Nat × Nat × …" before). A constructor pattern on a
scrutinee whose type is a structure `S` (`.mk p…`, `S.mk p…` or `⟨p…⟩`) is now
rewritten to the **tuple pattern** over the components of `S`'s Σ, which binds every
field as a projection of the scrutinee (`let h := s.1; let m := s.2.1; …`); the
sub-patterns are ordinary patterns, so structure patterns nest in constructor and tuple
patterns and the other way round, and mix with as-patterns.

**One place knows the encoding.** How the Σ of a structure is laid out (which
component is which field, and which are not fields at all: today the tail
`(0 fields✝ : …) → Unit` after the last field, 22i) is read from the declaration by
`structLayout?` (`Elab/Struct.lean`), as a list of components, each a field or a marker;
structure patterns, the pattern `let` and structure update (13i) go through it and
nothing else there looks at the Σ. It classifies the components by what the
declaration says (a Σ binder with a phantom name is a marker, the final component is a
field exactly if `S.mk` has a field left for it), so moving the marker to a 0-quantity
component before the last field needs no change here; any other re-encoding is a change
to that one function.

The anonymous constructor `⟨e₁, …, eₙ⟩` is new syntax (`term.anon`), as a term and as a
pattern. Against a structure it is `S.mk e₁ … eₙ`; against a pair, the tuple
`(e₁, …, eₙ)`; against a data type with exactly one constructor, that constructor. It
needs an expected type ("cannot infer the type of an anonymous constructor").

`let pat := e; body` with `pat` an anonymous constructor or any pattern in parentheses
(`term.letPat`) is `match e with | pat => body`, so it also works without an expected
type.

**Linear structures.** A `match` is a case at ω and projections need an unrestricted
pair, so neither takes apart a structure held at quantity 1. With a quantity,
`let 1 ⟨a, b⟩ := s; body` (or `let 1 (.mk a b) := s`) therefore elaborates to nested
splits at that quantity, one per component of the layout, as `let 1 (a, b, c) := t`
does for a tuple (and `let 1 ⟨a, b, c⟩ := t` is accepted on a tuple too); the components
are then names or `_`, and the form is check-mode only. **Today this is rejected for
every structure**: the Σ ends in the marker tail, which is not a field, and the last
split would bind it at quantity 1 and never use it. The elaborator reports that itself
("cannot take a value of the structure Stats apart at quantity 1: the Σ type of a
structure ends in a component that is not a field …") instead of leaving it to the
kernel's usage count. The check is on the layout (a marker that the Σ does not bind at
quantity 0), so once the marker is an erased component the same `let` goes through with
no change here. At quantity ω (`let ω ⟨a, b⟩ := s`) the splits are accepted today.

A structure whose constructor or fields are private to another module (13b) is opaque
there and can't be matched or taken apart ("its constructor is private to module M").

Tests: `language` ("structure patterns …", "anonymous constructors …", "let with a
structure pattern …"), `parser: terms`.

## 13i: structure update `{ s with f := v }` ✅

```
def bump (s : Stats) : Stats := { s with hits := Nat.succ s.hits }
def reset (s : Stats) : Stats := { s with hits := 0, misses := 0 }
```

`{ s with f₁ := v₁, …, fₖ := vₖ }` is `S.mk` applied to the structure's parameters
(taken from the type of `s`) and to every field: `vᵢ` for a named field, checked against
the field's type, and the projection of `s` for the others. `s` is any term; unless it
is a variable it is bound once (`let s✝ := s`). The type of `s` must be a structure,
and it is the type of the result; nothing is taken from the expected type. Unknown
fields ("Stats has no field 'x' (its fields are hits, misses)") and repeated ones are
errors. With dependent fields, a kept field whose type mentions an updated one must
still fit: `{ d with n := 3 }` for `structure D where n : Nat; v : Vec Nat n` is "field
'v' keeps its value, but its type … depends on an updated field"; update both.

The projections make this an unrestricted use of `s`: a structure held at quantity 1
can't be updated this way (take it apart with the pattern `let` of 13h, once that works
for linear structures). Like 13h it reads the fields through `structLayout?`, and it is
refused for a structure that is opaque in the current module.

Syntax: `term.structUpdate`, `"{" term "with" (ident ":=" term),+ "}"`. No new reserved
word (`with` already is one). Tests: `language` ("structure update …"), `parser: terms`.

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

## 13k: list literals ✅

`[a, b, c]` is `List.cons a (List.cons b (List.cons c List.nil))` and `[]` is `List.nil`,
in terms and in patterns:

```
def xs : List Nat := [1, 2, 3]
def len : List Nat → Nat
  | [] => 0
  | [_] => 1
  | _ => 2
```

It is a Prelude `syntax` with a procedural macro (`ListLit.expand`), not built-in
grammar, so the self-hosted toolchain's generated parser tables are unchanged (its own
prelude, `preludeText` in `selfhost/Frontend.wiz`, has no list literals, and its sources
don't use them). `[` already starts an instance binder in a dependent arrow
(`[Monad m] → m A`, `[inst : C A] → B`): that is one leading parser that also consumes
the arrow, so it is longer than a list literal and wins (longest match, `Wiz/Parser/Interp.lean`);
`Enum [a, b]`, `ecase t [..]` and `attribute [..]` are leading parsers that consume their
brackets in the same way. The elements are checked at the element type of the expected
`List A` (`List.cons a …` is an ordinary application), so numerals at a non-`Nat` element
type go through `OfNat` like any argument (7e).

**Patterns.** The match compiler (`patView`) reads constructors, applications, tuples and
parentheses. Patterns are now macro-expanded first (`expandPattern`, `Wiz/Elab/Term.lean`;
in `match` and in definitions by equations): every syntax kind other than those forms is
expanded if a macro applies, so `[x, y]` becomes `List.cons x (List.cons y List.nil)`,
and a user notation whose expansion is a constructor application works in patterns too.
Tests: group `language`.

## 13l: `++` for lists and strings ✅

`a ++ b` is `Append.append a b`, a method of the homogeneous class
`class Append (A : Type) where append : A → A → A`, with instances for `List A`
(`List.append`) and `String` (`String.append`): the same design as the numeric classes
(7e, HD9 stage 1). A heterogeneous `HAppend A B C` would need default instances, which
the numeric classes also left for later. Other types get `++` by an instance.
(`lib/Hdl/Core.wiz`'s `<+>` and `selfhost/Parse.wiz`'s `+++` are older local spellings
of `String.append`; the self-hosted prelude keeps `infixr " ++ " => List.append`.)
Tests: group `language`.

## 13m: local notation ✅

A grammar command marked `local` stays in its module: modules that import it don't see
the syntax.

```
local infixr:67 " & " => String.append
local syntax (name := shout) "shout" term : term
local macro_rules
  | `(term| shout $x) => `(term| $x & "!")
```

`local` applies to `syntax`, `declare_syntax_cat`, `notation`, `infixl`/`infixr`/`infix`,
`macro_rules` and `attribute [macro …]`; anything else is an error. In the main file it
changes nothing. `local` is not a reserved word.

An `import` elaborates the module's text into the importer's state, so its
syntax lands in the importer's parser tables. The state records what each `local`
command added (new node kinds and categories, and which macro rules and macro
registrations, by position), and when the import ends (`CommandState.endModule`, called
by `runFrontend` and by the command cache's import walker) those are removed: the
parsers of the kinds (and the categories), every macro rule, macro and tactic of those
kinds, and the local rules; a token that no remaining parser mentions is no longer
reserved (so a local keyword `shout` is an identifier again in the importer). Kind
names stay taken, so an importer that declares the same notation gets a new kind and
none of the dropped rules. Definitions written with the notation are unaffected (they
are terms by then). Lean also has `scoped` notation, active where a namespace is open;
Wiz has no `open`, so the module is the only scope. The design notes are in the notes
(`notation.md`). `command.local` is built-in grammar (`Wiz/Parser/Builtin.lean`), so the
self-hosted parser's generated tables have it too; the self-hosted frontend has no
`syntax` command yet and doesn't elaborate it. Tests: groups `language`,
`parser: commands and syntax`.

## 13n: `rfl` at an equation that has computed ✅

An equation at a Σ type computes as soon as it is formed: `a = b` becomes
`(0 e : a.1 = b.1) × (cast (B a.1) (B b.1) ê a.2 = b.2)`. The elaborator's `rfl` used to
prove that Σ field by field. Every field after the first then needed the cast to
disappear, and at a type variable (`B`, `List A`, a function type) it does not: regularity
holds only at inert types (P1). So `s = s` at `A × B`, `(p.1, p.2) = p`,
`Pair2.mk s.fst s.snd = s` (structure η, which conversion already has), and the field
lenses' laws all failed with "the two sides are not definitionally equal".

Now `vEq` keeps the equation's type at the end of the Σ's closure (the body doesn't use
it), and `eqSigmaSides?` reads `A`, `a`, `b` back. When `a ≡ b`, `rfl` is a single
`refl A a`, whose type computes to the same Σ, with the same cast on both sides. This is
the optional exercise 4.16, done by recording the equation in its computed form. No axiom
is used: `#print axioms` lists none for these proofs. An equation at a constructor
(`List.cons x xs = List.cons x xs`) works the same way, through its payload's Σ.

Nothing else changed. A Σ of field equations written by hand, with a cast at a type
variable in it, is still not `rfl`. `rfl` never adds an axiom; whoever needs that
equation writes `castRefl` themselves.

`lib/Optic.wiz` now states the `Pair2` lens laws with their implicit arguments
(`@Lens.Lawful (Pair2 A B) A …`), so that the equation has computed when `rfl` sees it.
Before, they checked only because unsolved holes kept the equation from computing.
Research note: `wiz-notes/structure-eta.md`. Tests: group `elabfix`, "rfl at an equation
that has computed"; group `optic`.
