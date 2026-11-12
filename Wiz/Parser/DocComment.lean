/-!
# Doc comments (stage 11s)

`/-- … -/` right before a command (only whitespace between) documents the declarations
the command makes, as in Lean; before a constructor (`| /-- … -/ c …`) or a field of a
`structure` or `class`, that constructor or field. `/-! … -/` documents the module.

To the lexer a doc comment is a block comment (it starts like one), so the grammar, the
self-hosted lexer and every existing file are unchanged: the frontend finds a command's
doc comment from where the command starts (`docCommentBefore`) and stores it on the
declarations (`CommandState.declDocs`).
-/

namespace Wiz

/-- The text of a doc comment's body: without the delimiters, the common indentation of
its lines removed, blank lines at either end dropped. -/
def docText (body : String) : String :=
  let lines := body.splitOn "\n"
  let indent (l : String) : Option Nat :=
    if l.trimAscii.isEmpty then none else some (l.toList.takeWhile (· == ' ')).length
  -- (the first line follows `/--` on the same line: its indentation doesn't count)
  let common := ((lines.drop 1).filterMap indent).foldl min 1000000
  let common := if common == 1000000 then 0 else common
  let lines : List String := match lines with
    | [] => []
    | l :: ls => l.trimAscii.toString :: ls.map fun (l : String) => (String.ofList (l.toList.drop common)).trimAsciiEnd.toString
  let lines : List String := (lines.dropWhile (fun (l : String) => l.isEmpty)).reverse.dropWhile (fun (l : String) => l.isEmpty) |>.reverse
  "\n".intercalate lines

/-- Where the block comment that ends just before `stop` (`stop` is past its closing
delimiter) starts, counting nested comments; `none` if there is no such comment. -/
def blockCommentStart (chars : Array Char) (stop : Nat) : Option Nat := Id.run do
  if stop < 4 || chars[stop - 1]? != some '/' || chars[stop - 2]? != some '-' then return none
  let mut depth := 1
  let mut j := stop - 2
  -- scan backwards: `-/` opens a level, `/-` closes one
  while j > 0 do
    if chars[j - 1]? == some '-' && j ≥ 2 && chars[j - 2]? == some '/' then
      -- (`/-/`: not both an opener and a closer)
      depth := depth - 1
      if depth == 0 then return some (j - 2)
      j := j - 2
    else if chars[j - 1]? == some '/' && j ≥ 2 && chars[j - 2]? == some '-' then
      depth := depth + 1
      j := j - 2
    else
      j := j - 1
  return none

/-- The doc comment that ends right before offset `pos` (only whitespace between), if any:
its text (`docText`). -/
def docCommentBefore (chars : Array Char) (pos : Nat) : Option String := do
  let mut e := min pos chars.size
  while e > 0 && (chars[e - 1]?.map (" \t\r\n".toList.contains ·)).getD false do
    e := e - 1
  let s ← blockCommentStart chars e
  -- `/--`, and not `/--/` (an empty block comment) nor `/---` (a rule)
  unless chars[s + 2]? == some '-' && chars[s + 3]? != some '/' && chars[s + 3]? != some '-' do none
  -- not inside a line comment (`-- see /-- … -/`): nothing but whitespace before it on its line
  let mut b := s
  while b > 0 && chars[b - 1]? != some '\n' do
    unless (chars[b - 1]?.map (" \t".toList.contains ·)).getD false do
      -- (another comment or code before it on the line: still a doc comment unless `--`)
      let line := String.ofList (chars.extract b s).toList
      if (line.splitOn "--").length > 1 then none
      break
    b := b - 1
  pure (docText (String.ofList (chars.extract (s + 3) (e - 2)).toList))

/-- The module's documentation: its `/-! … -/` comments, in order (outside other
comments), or else the `--` comment block at the top of the file. -/
def moduleDocOf (src : String) : Option String := Id.run do
  let chars := src.toList.toArray
  let mut docs : Array String := #[]
  let mut i := 0
  while i < chars.size do
    match chars[i]?, chars[i + 1]? with
    | some '-', some '-' =>
      while i < chars.size && chars[i]? != some '\n' do i := i + 1
    | some '"', _ =>
      i := i + 1
      while i < chars.size && chars[i]? != some '"' do
        if chars[i]? == some '\\' then i := i + 1
        i := i + 1
      i := i + 1
    | some '/', some '-' =>
      let start := i
      let mut depth := 1
      i := i + 2
      while i < chars.size && depth > 0 do
        if chars[i]? == some '/' && chars[i + 1]? == some '-' then depth := depth + 1; i := i + 2
        else if chars[i]? == some '-' && chars[i + 1]? == some '/' then depth := depth - 1; i := i + 2
        else i := i + 1
      if chars[start + 2]? == some '!' then
        docs := docs.push (docText (String.ofList (chars.extract (start + 3) (i - 2)).toList))
    | _, _ => i := i + 1
  if !docs.isEmpty then return some ("\n\n".intercalate docs.toList)
  -- the leading `--` block (after any `import` lines)
  let lines := (src.splitOn "\n").dropWhile fun l => l.trimAscii.isEmpty || l.startsWith "import "
  let block := lines.takeWhile (·.startsWith "--")
  if block.isEmpty then return none
  let text := block.map fun l => (String.ofList ((l.toList.drop 2).dropWhile (· == ' ')))
  -- (a `-- ##` header line or `--<sol` marker is not prose)
  return some (docText ("\n".intercalate text))

end Wiz
