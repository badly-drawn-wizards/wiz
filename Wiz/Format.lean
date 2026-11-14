import Wiz.Frontend.Frontend

set_option maxHeartbeats 1000000

/-!
# `wiz fmt`: reprinting source from the syntax tree

A formatter has two possible architectures:

1. **reprint from the tree**: parse the file, then print every command from its syntax
   tree, using the parser's own grammar (the `PPFormat` table the notation-aware printer
   walks, 11r) to place the tokens, and a small pretty-printing document (`Doc`, below)
   to choose line breaks; or
2. **rewrite the token/whitespace stream**, keeping every token and every line as it is
   and normalising the space between tokens.

This module takes (1). The grammar is the single source of truth for what the tokens are
and how they bind, so a formatter built on it cannot disagree with the parser about
`a + b` or `(fun x => b) c`; it formats user-declared `syntax` (the tables are the same
ones the parser used); and it can check itself: **the formatted text of a command must
parse back, with the tables that were in effect at that command, to the same tree**, or
the command keeps its original text and is reported. A token-rewriting formatter keeps
comments for free, but it can never reindent a block, join or split lines, or drop the
parentheses a reprint makes unnecessary, and it must reimplement the declared spacing of
every `syntax` rule anyway.

Comments are the one thing a syntax tree does not keep (`Token.skipWs` drops them). They
are recovered from the source: every leaf keeps its byte range (`SourceInfo`), so the
text between two consecutive leaves is a run of comments, emitted before the later one,
each on its own line. Layout-sensitive constructs (`match`'s alternatives, `by`'s
tactics, `let`'s body) are printed with the breaks the parser's `colGe`/`colGt` rules
need: alternatives and tactics one per line at their block's indent, a `let`'s body at
the `let`'s indent.

## The fragment

Everything the grammar can parse is reprinted. A command is **refused** (kept verbatim,
reported, exit status 1) when its kind has no grammar in the tables, when the source has
something between two tokens that is not a comment, or when the reprint does not parse
back to the same tree. Outside the fragment nothing changes: the formatter never
guesses.
-/

namespace Wiz
namespace Fmt

/-! ### A pretty-printing document

Strictly pretty (Lindig): `group` decides, by measuring the flat rendering against the
remaining width, whether the `line`s inside it are spaces or newlines. `line true` always
breaks. A `group` is measured together with the text that follows on the line, so a break
is only taken when it is needed. -/

inductive Doc where
  | nil
  | txt (s : String)
  | cat (ds : Array Doc)
  | line (hard : Bool)
  | nest (n : Int) (d : Doc)
  /-- indent what follows like the construct it belongs to: at the line's indentation
  when the construct starts its line, else two columns deeper (`match`'s alternatives,
  `by`'s tactics) -/
  | align (d : Doc)
  | group (d : Doc)

namespace Doc

partial def first? : Doc → Option Char
  | .txt s => s.toList.head?
  | .cat ds => ds.toList.findSome? first?
  | .nest _ d | .group d | .align d => first? d
  | _ => none

partial def last? : Doc → Option Char
  | .txt s => s.toList.getLast?
  | .cat ds => ds.toList.reverse.findSome? last?
  | .nest _ d | .group d | .align d => last? d
  | _ => none

/-- The column after printing `s`, starting at `col` (text may contain newlines). -/
def colAfter (col : Int) (s : String) : Int :=
  match s.splitOn "\n" with
  | [one] => col + one.length
  | lines => (lines.getLast!).length

end Doc

open Doc

/-- A document, the indentation of its line, and whether it is flat. -/
structure Cmd where
  indent : Int
  flat : Bool
  doc : Doc

/-- Does the flat rendering of these commands fit in `w` columns? A break in non-flat
mode ends the measurement (`true`: it fits up to there). -/
partial def fits (w : Int) : List Cmd → Bool
  | [] => true
  | c :: rest =>
    match c.doc with
    | .nil => fits w rest
    | .txt s =>
      if s.contains '\n' then true
      else if w - s.length < 0 then false
      else fits (w - s.length) rest
    | .cat ds => fits w (ds.toList.map (fun d => { c with doc := d }) ++ rest)
    | .nest _ d => fits w ({ c with doc := d } :: rest)
    | .align d => fits w ({ c with doc := d } :: rest)
    | .group d => fits w ({ c with flat := true, doc := d } :: rest)
    | .line _ => if c.flat then (if w <= 0 then false else fits (w - 1) rest) else true

/-- Render a document at most `width` columns wide (text with no break point in it may
be longer).

A `nest n` is relative to the **indentation of the line it starts on**, not to the
column: a `match` in `def f := match x with` puts its alternatives at 2, and the same
`match` on a line already indented by 2 puts them at 4. That is the house layout, and it
is what the parser's `colGe` rules accept. -/
partial def render (width : Nat) (d : Doc) : String :=
  let rec go (out : String) (col lineIndent : Int) : List Cmd → String
    | [] => out
    | c :: rest =>
      match c.doc with
      | .nil => go out col lineIndent rest
      | .txt s => go (out ++ s) (Doc.colAfter col s) lineIndent rest
      | .cat ds => go out col lineIndent (ds.toList.map (fun d => { c with doc := d }) ++ rest)
      | .nest n d => go out col lineIndent ({ c with indent := lineIndent + n, doc := d } :: rest)
      | .align d =>
        let ind := if col == lineIndent then col else lineIndent + 2
        go out col lineIndent ({ c with indent := ind, doc := d } :: rest)
      | .group d =>
        let flat := fits (Int.ofNat width - col) ({ c with flat := true, doc := d } :: rest)
        go out col lineIndent ({ c with flat, doc := d } :: rest)
      | .line hard =>
        if hard || !c.flat then
          let ind := if c.indent < 0 then 0 else c.indent
          go (out ++ "\n" ++ String.ofList (List.replicate ind.toNat ' ')) ind ind rest
        else go (out ++ " ") (col + 1) lineIndent rest
  go "" 0 0 [{ indent := 0, flat := false, doc := d }]

/-! ### Chunks: tokens, and the spacing the grammar asks for

A node is printed by walking its `ParserDescr` against its children. Each item becomes a
`text` chunk; the space between two of them follows the declared spelling (`" + "`,
`"!"`, from `syntax`/`notation`) when there is one, and otherwise the rules the
infoview's printer uses: keywords are separated, nothing goes inside brackets or before
a `,`/`;`, and `noWs` glues. `brk`/`nest` chunks are layout: a break after `:=` or
`with`, and the nesting of what follows. -/

inductive Chunk where
  | text (doc : Doc) (first last : Option Char) (raw : Option String) (sep : Bool := false)
  | brk (hard : Bool)
  /-- nest what follows in this node (a negative number dedents) -/
  | nest (n : Int)
  /-- indent what follows like its construct (`match`'s alternatives, `by`'s tactics) -/
  | align
  /-- no space before the next token (`noWs`) -/
  | glue

def mkChunk (d : Doc) (raw : Option String) (sep : Bool := false) : Chunk :=
  .text d d.first? d.last? raw sep

/-- Identifier and keyword characters (Greek letters and subscripts too). -/
def identish (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\'' || (c.val ≥ 0x370 && c.val < 0x400) ||
  (c.val ≥ 0x2080 && c.val < 0x209d)

def endsWithWs (s : String) : Bool := s.toList.getLast?.any (·.isWhitespace)

def startsWithWs (s : String) : Bool := s.toList.head?.any (·.isWhitespace)

/-- Is a space needed between two chunks? (The rules of `Core/Pretty.lean`'s
`needSpace`.) -/
def needSpace (a b : Chunk) : Bool :=
  match a, b with
  | .text _ _ al ar asep, .text _ bf _ br bsep =>
    match al, bf with
    | some x, some y =>
      if ar.any endsWithWs then false
      else if br.any startsWithWs then false
      else if bsep then false
      else if asep || x == ',' || x == ';' then true
      else if "([{⟨".toList.contains x || ")]}⟩,;".toList.contains y then false
      else if !identish x && !identish y then true
      else if ar.isSome && !identish x then false
      else if br.isSome && !identish y then false
      else true
    | _, _ => false
  | _, _ => false

/-- Join chunks: the tokens with their spacing, the breaks and nests as they come. -/
def joinChunks (cs : List Chunk) : Doc :=
  let rec go (cs : List Chunk) (prev : Option Chunk) (glue : Bool) (out : Array Doc) : Doc :=
    match cs with
    | [] => .cat out
    | .glue :: rest => go rest prev true out
    | .brk h :: rest => go rest none true (out.push (.line h))
    | .nest n :: rest => .cat (out.push (.nest n (go rest prev glue #[])))
    | .align :: rest => .cat (out.push (.align (go rest prev glue #[])))
    | c@(.text ..) :: rest =>
      let sp := match prev with
        | some p => !glue && needSpace p c
        | none => false
      let out := if sp then out.push (.txt " ") else out
      let d := match c with | .text d .. => d | _ => .nil
      go rest (some c) false (out.push d)
  go cs none false #[]

/-! ### The syntax table -/

/-- How a syntax kind formats: its rule (see `PPFormat`), from the parser tables. -/
def formatsOf (s : CommandState ZeroOneMany) : Std.HashMap Name PPFormat :=
  s.tables.cats.fold (init := ({} : Std.HashMap Name PPFormat)) fun m c cat =>
    let m := cat.leading.foldl (init := m) fun m lp =>
      let raw := s.rawAtoms.getD lp.kind #[]
      m.insert lp.kind { cat := c, leading := true, prec := lp.prec, p := lp.p, raw := raw }
    cat.trailing.foldl (init := m) fun m tp =>
      let raw := s.rawAtoms.getD tp.kind #[]
      m.insert tp.kind { cat := c, leading := false, prec := tp.prec, lhsPrec := tp.lhsPrec, p := tp.p, raw := raw }

/-! ### Layout: where the breaks go

The parser's layout rules are relative columns (`colGt`/`colGe`), so a reprint that keeps
blocks at their construct's indent re-parses the same way: `match`'s alternatives at the
`match` line's indent + 2, `by`'s tactics likewise, a `let`'s body at the `let`'s. -/

/-- Chunks to insert after the atom `tok` of a node of kind `kind`. -/
def layoutAfter (kind : Name) (tok : String) : List Chunk :=
  match kind, tok with
  | "command.def", ":=" => [.nest 2, .brk false]
  | "term.fun", "=>" | "term.fun", "↦" => [.nest 2, .brk false]
  | "match.alt", "=>" => [.nest 2, .brk false]
  | "term.let", ";" | "term.letPair", ";" | "term.letTuple", ";" | "term.letUnit", ";"
  | "term.letPat", ";" => [.brk false]
  | _, "," => [.brk false]
  | _, _ => []

/-- Chunks to insert before the atom `tok` of a node of kind `kind`. -/
def layoutBefore (kind : Name) (tok : String) : List Chunk :=
  match kind, tok with
  | "command.mutual", "end" => [.nest (-2), .brk true]
  | "command.inductive", "deriving" | "command.structure", "deriving" | "command.cStruct", "deriving" =>
    [.brk true]
  | _, _ => []

/-- Chunks to insert after a child node of kind `child` inside a node of kind `kind`. -/
def layoutAfterNode (_kind _child : Name) : List Chunk := []

/-- Do the items of this descriptor go one per line (alternatives, constructors,
tactics, fields, a `mutual` block's commands)? -/
partial def hardItems : ParserDescr → Bool
  | .node k _ => k == "match.alt" || k == "inductive.ctor" || k == "structure.field" ||
      k == "instance.field" || k.startsWith "command."
  | .cat "tactic" _ | .cat "command" _ => true
  | .seq ps => ps.any hardItems
  | .many p | .many1 p | .optional p | .withPosition p | .withoutPosition p => hardItems p
  | .sepBy p _ _ | .sepBy1 p _ _ => hardItems p
  | .orelse p q => hardItems p || hardItems q
  | _ => false

/-! ### Walking the grammar -/

/-- How many syntax items a descriptor produces (`none`: it depends). -/
partial def itemCount : ParserDescr → Option Nat
  | .seq ps => ps.foldlM (fun n p => (n + ·) <$> itemCount p) 0
  | .withPosition p | .withoutPosition p => itemCount p
  | .orelse p q => do let a ← itemCount p; let b ← itemCount q; if a == b then some a else none
  | .colGt | .colGe | .noWs | .checkPrec _ => some 0
  | _ => some 1

/-- The precedence of the term that ends a descriptor, if it ends in one (`fun x => b`
ends in `term 0`: open to the right). -/
partial def lastCatPrec : ParserDescr → Option Nat
  | .cat "term" p => some p
  | .seq ps => (ps.toList.reverse.find? (itemCount · != some 0)).bind lastCatPrec
  | .withPosition p | .withoutPosition p | .many p | .many1 p | .optional p => lastCatPrec p
  | .sepBy p _ _ | .sepBy1 p _ _ => lastCatPrec p
  | .orelse p q => match lastCatPrec p, lastCatPrec q with
    | some a, some b => some (min a b)
    | a, b => a <|> b
  | _ => none

def effPrec (f : PPFormat) : Nat := match lastCatPrec f.p with
  | some q => min f.prec q
  | none => f.prec

def rawOf (f : PPFormat) (tok : String) : Option String :=
  f.raw.find? fun r =>
    String.ofList ((r.toList.dropWhile (·.isWhitespace)).reverse.dropWhile (·.isWhitespace)).reverse == tok

/-- What the printer needs: the grammar of every kind, and the source (for the text of
literals and for the comments between tokens). -/
structure Ctx where
  fmts : Std.HashMap Name PPFormat
  src : Array Char
  /-- the comments before the leaf that starts at this offset: their text, and whether
  the comment starts on the same source line as the token before it (a trailing
  comment) -/
  comments : Std.HashMap Nat (Array (String × Bool)) := {}

abbrev EM := Except String

/-- Drop trailing whitespace. -/
def trimRight (s : String) : String :=
  String.ofList (s.toList.reverse.dropWhile (·.isWhitespace)).reverse

/-- The source text of a leaf (its original spelling: `0x3F` stays hex, a string keeps
its escapes), or a fallback when there is no range. -/
def leafText (ctx : Ctx) (s : Syntax) : String :=
  let i := s.info
  if !i.synthetic && i.stop > i.start && i.stop ≤ ctx.src.size then
    String.ofList (ctx.src.extract i.start i.stop).toList
  else match s with
    | .atom _ v => v
    | .ident _ n => n
    | .node _ "num" #[.atom _ v] => v
    | .node _ "str" #[.atom _ v] => v.quote
    | _ => ""

/-- The chunks for a leaf: the comments in front of it (each on its own line), then the
token with its declared spelling. -/
def leafChunks (ctx : Ctx) (s : Syntax) (raw : Option String) : Array Chunk := Id.run do
  let mut out : Array Chunk := #[]
  let mut pending := false
  for (c, trailing) in ctx.comments.getD s.info.start #[] do
    if trailing then
      out := out.push (mkChunk (.txt c) none) |>.push (.brk true)
      pending := false
    else
      out := out.push (.brk true) |>.push (mkChunk (.txt c) none)
      pending := true
  if pending then out := out.push (.brk true)
  out := out.push (mkChunk (.txt (leafText ctx s)) raw)
  out

mutual

partial def fmtNode (ctx : Ctx) (s : Syntax) (cat : Name) (prec : Nat) : EM Doc := do
  match s with
  | .missing => throw "missing syntax"
  | .atom .. | .ident .. => pure (.group (joinChunks (leafChunks ctx s none).toList))
  | .node _ "null" _ => throw "a `null` node where a node was expected"
  | .node _ k args =>
    let some f := ctx.fmts[k]? | throw s!"no grammar for the syntax kind {k}"
    let parenIf (d : Doc) : Doc := if cat == "term" && prec > effPrec f then .cat #[.txt "(", d, .txt ")"] else d
    if f.leading then
      let (cs, j) ← walk ctx cat k f args 0 f.p
      if j != args.size then throw s!"{k}: its children don't fit its grammar"
      let cs := if k == "term.match" || k == "term.by" then #[.align] ++ cs else cs
      pure (.group (parenIf (joinChunks cs.toList)))
    else
      let some lhs := args[0]? | throw s!"{k}: no left-hand side"
      let ld ← fmtNode ctx lhs f.cat f.lhsPrec
      let (cs, j) ← walk ctx cat k f args 1 f.p
      if j != args.size then throw s!"{k}: its children don't fit its grammar"
      pure (.group (parenIf (joinChunks ((#[mkChunk ld none] ++ cs).toList))))

/-- Walk a descriptor over the children `args` from `i`: the chunks, and the next child. -/
partial def walk (ctx : Ctx) (cat : Name) (kind : Name) (f : PPFormat) (args : Array Syntax)
    (i : Nat) (d : ParserDescr) : EM (Array Chunk × Nat) := do
  match d with
  | .atom tok | .nonReserved tok =>
    match args[i]? with
    | some a@(.atom _ v) =>
      if v != tok then throw s!"{kind}: expected '{tok}', found '{v}'"
      let cs := leafChunks ctx a (rawOf f tok)
      pure ((layoutBefore kind tok).toArray ++ cs ++ (layoutAfter kind tok).toArray, i + 1)
    | _ => throw s!"{kind}: expected '{tok}'"
  | .ident =>
    match args[i]? with
    | some a@(.ident ..) => pure (leafChunks ctx a none, i + 1)
    | _ => throw s!"{kind}: expected an identifier"
  | .num =>
    match args[i]? with
    | some a@(.node _ "num" _) => pure (leafChunks ctx a none, i + 1)
    | _ => throw s!"{kind}: expected a numeral"
  | .str =>
    match args[i]? with
    | some a@(.node _ "str" _) => pure (leafChunks ctx a none, i + 1)
    | _ => throw s!"{kind}: expected a string"
  | .cat c p =>
    match args[i]? with
    | some a => do
      let d ← fmtNode ctx a c p
      pure (#[mkChunk d none], i + 1)
    | none => throw s!"{kind}: missing a {c}"
  | .seq ps =>
    let mut acc : Array Chunk := #[]
    let mut j := i
    for p in ps do
      let (xs, j') ← walk ctx cat kind f args j p
      acc := acc ++ xs
      j := j'
    pure (acc, j)
  | .withPosition p | .withoutPosition p => walk ctx cat kind f args i p
  | .colGt | .colGe | .checkPrec _ => pure (#[], i)
  | .noWs => pure (#[.glue], i)
  | .orelse p q =>
    match walk ctx cat kind f args i p with
    | .ok r => pure r
    | .error e1 => match walk ctx cat kind f args i q with
      | .ok r => pure r
      | .error e2 => throw s!"{e1} / {e2}"
  | .node k p =>
    match args[i]? with
    | some (.node _ k' as) =>
      if k != k' then throw s!"{kind}: expected a {k}, found a {k'}"
      let (cs, j) ← walk ctx cat k f as 0 p
      if j != as.size then throw s!"{kind}: a {k} doesn't fit its grammar"
      -- the child's layout nests are its own (they must not reach the next sibling)
      pure (#[mkChunk (joinChunks cs.toList) none] ++ (layoutAfterNode kind k).toArray, i + 1)
    | _ => throw s!"{kind}: expected a {k}"
  | .many p | .many1 p =>
    match args[i]? with
    | some (.node _ "null" es) =>
      if d matches .many1 _ && es.isEmpty then throw s!"{kind}: expected one more item"
      let hard := hardItems p
      let mut acc : Array Chunk := #[]
      -- (`match` and `by` already set their own alignment at the node)
      if hard && !es.isEmpty && kind != "term.match" && kind != "term.by" then
        acc := acc.push (.nest 2)
      for e in es do
        if hard then acc := acc.push (.brk true)
        let xs ← iter ctx cat kind f p e
        acc := acc ++ xs
      pure (acc, i + 1)
    | _ => throw s!"{kind}: expected a list"
  | .optional p =>
    match args[i]? with
    | some (.node _ "null" es) =>
      if es.isEmpty then pure (#[], i + 1)
      else
        let (xs, j) ← walk ctx cat kind f es 0 p
        if j != es.size then throw s!"{kind}: an optional part doesn't fit"
        pure (xs, i + 1)
    | _ => throw s!"{kind}: expected an optional part"
  | .sepBy p sep _ | .sepBy1 p sep _ =>
    match args[i]? with
    | some (.node _ "null" es) =>
      if d matches .sepBy1 .. && es.isEmpty then throw s!"{kind}: expected one more item"
      let mut acc : Array Chunk := #[]
      for (e, k) in es.toList.zipIdx do
        if k % 2 == 1 then
          unless e matches .atom .. do throw s!"{kind}: expected a separator"
          acc := acc.push (mkChunk (.txt sep) none (sep := true)) |>.push (.brk false)
        else
          let xs ← iter ctx cat kind f p e
          acc := acc ++ xs
      pure (acc, i + 1)
    | _ => throw s!"{kind}: expected a list"

/-- One iteration of `many`/`sepBy`: a single item stays as it is, several are a `null`
node (`packItems`). -/
partial def iter (ctx : Ctx) (cat : Name) (kind : Name) (f : PPFormat) (p : ParserDescr)
    (e : Syntax) : EM (Array Chunk) := do
  let whole (xs : Array Syntax) : EM (Array Chunk) := do
    let (ps, j) ← walk ctx cat kind f xs 0 p
    if j != xs.size then throw s!"{kind}: an item doesn't fit its grammar"
    pure ps
  match itemCount p with
  | some 1 => whole #[e]
  | some _ => match e with
    | .node _ "null" xs => whole xs
    | _ => throw s!"{kind}: expected a list of items"
  | none =>
    match whole #[e] with
    | .ok r => pure r
    | .error _ => match e with
      | .node _ "null" xs => whole xs
      | _ => throw s!"{kind}: an item doesn't fit its grammar"

end

/-! ### Comments, from the source between the leaves -/

/-- The leaves of a command, in source order: atoms and identifiers, and the `num`/`str`
nodes (whose range covers the whole literal). -/
partial def leafSpans (s : Syntax) (acc : Array (Nat × Nat) := #[]) : Array (Nat × Nat) :=
  match s with
  | .atom i _ | .ident i _ => acc.push (i.start, i.stop)
  | .node i "num" _ | .node i "str" _ => acc.push (i.start, i.stop)
  | .node _ _ as => as.foldl (fun acc a => leafSpans a acc) acc
  | _ => acc

/-- The comments in `[lo, hi)`, with whether each starts on the same line as `lo`
(the end of the token before it). Every non-whitespace run must be a comment. -/
partial def commentsIn (src : Array Char) (lo hi : Nat) : EM (Array (String × Bool)) := do
  let mut out : Array (String × Bool) := #[]
  let mut i := lo
  while i < hi do
    let c := src[i]!
    if c.isWhitespace then i := i + 1
    else if c == '-' && src[i + 1]? == some '-' then
      let mut j := i + 2
      while j < hi && src[j]! != '\n' do j := j + 1
      let text := trimRight (String.ofList (src.extract i j).toList)
      out := out.push (text, !(src.extract lo i).toList.contains '\n')
      i := j
    else if c == '/' && src[i + 1]? == some '-' then
      let mut j := i + 2
      let mut depth := 1
      while j < hi && depth > 0 do
        if src[j]? == some '/' && src[j + 1]? == some '-' then depth := depth + 1; j := j + 2
        else if src[j]? == some '-' && src[j + 1]? == some '/' then depth := depth - 1; j := j + 2
        else j := j + 1
      if depth != 0 then throw "an unterminated block comment inside a command"
      let text := trimRight (String.ofList (src.extract i j).toList)
      out := out.push (text, !(src.extract lo i).toList.contains '\n')
      i := j
    else throw s!"something between two tokens that is not a comment (offset {i})"
  pure out

/-- The comments before each leaf of `cmd`, by the leaf's start offset. -/
def commentsOf (src : Array Char) (cmd : Syntax) : EM (Std.HashMap Nat (Array (String × Bool))) := do
  let spans := leafSpans cmd
  let mut m : Std.HashMap Nat (Array (String × Bool)) := {}
  let mut prev := cmd.info.start
  for (start, stop) in spans do
    if start > prev then
      let cs ← commentsIn src prev start
      if !cs.isEmpty then m := m.insert start cs
    prev := max prev stop
  pure m

/-! ### Formatting a command -/

/-- The text of a command, reprinted from its tree (comments included). -/
def formatCommand (tables : Std.HashMap Name PPFormat) (src : Array Char) (cmd : Syntax)
    (width : Nat := 100) : EM String := do
  let comments ← commentsOf src cmd
  let ctx : Ctx := { fmts := tables, src, comments }
  let doc ← fmtNode ctx cmd "command" 0
  pure (render width doc)

/-! ### The driver: parse, format, check the reprint, repeat -/

structure Options where
  width : Nat := 100
  deriving Inhabited

structure Result where
  /-- the formatted file -/
  text : String := ""
  /-- commands kept as they were, with the reason (by line) -/
  refused : Array String := #[]
  /-- the file didn't parse: nothing was formatted -/
  errors : Array String := #[]
  deriving Inhabited

/-- Drop trailing spaces from every line. -/
def stripTrailing (s : String) : String :=
  "\n".intercalate ((s.splitOn "\n").map trimRight)

def sliceText (chars : Array Char) (lo hi : Nat) : String :=
  if lo ≥ hi then "" else String.ofList (chars.extract lo (min hi chars.size)).toList

/-- Format a file: parse each command with the tables in effect at it (imports and
`syntax` commands included), reprint it, and keep the reprint only when it parses back
to the same tree. -/
partial def run (init : CommandState ZeroOneMany) (input : String) (opts : Options := {}) : Result :=
  let chars := input.toList.toArray
  let rec go (s : CommandState ZeroOneMany) (pos prevStop : Nat) (out : String)
      (refused : Array String) : Result :=
    if skipWs chars pos ≥ chars.size then
      { text := stripTrailing (out ++ sliceText chars prevStop chars.size), refused }
    else match parseCommand chars s.tables pos with
    | .error e => { refused, errors := #[e.render input] }
    | .ok (cmd, stop) =>
      let rawGap := sliceText chars prevStop cmd.info.start
      let gap := if !rawGap.isEmpty && rawGap.toList.getLast! != '\n' then rawGap ++ "\n" else rawGap
      let original := sliceText chars cmd.info.start stop
      let fmts := formatsOf s
      -- the reprint, but only when it parses back to the same tree with these tables
      let checked : Except String String :=
        match formatCommand fmts chars cmd opts.width with
        | .error e => .error e
        | .ok text =>
          let fchars := text.toList.toArray
          match parseCommand fchars s.tables 0 with
          | .error e =>
            .error s!"the reprint does not parse: {(e.render text).splitOn ": " |>.drop 1 |> ": ".intercalate}"
          | .ok (cmd', stop') =>
            if skipWs fchars stop' != fchars.size then .error "the reprint does not parse to one command"
            else if cmd'.toSExpr (atoms := true) != cmd.toSExpr (atoms := true) then
              .error "the reprint parses to a different tree"
            else .ok text
      let lineNo := (lineCol input cmd.info.start).1 + 1
      let s' := runFrontend.go input init (chars.extract 0 stop) pos s
      match checked with
      | .error why =>
        go s' stop stop (out ++ gap ++ original) (refused.push s!"line {lineNo}: left as written ({why})")
      | .ok text => go s' stop stop (out ++ gap ++ text) refused
  go init 0 0 "" #[]

end Fmt
end Wiz
