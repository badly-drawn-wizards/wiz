" Vim syntax file for Wiz (wiz.nvim). Regex highlighting; no tree-sitter needed.
if exists('b:current_syntax')
  finish
endif

syn iskeyword @,48-57,_,',!,?,192-255

syn keyword wizCommand def theorem lemma abbrev axiom inductive coinductive codata structure class instance
syn keyword wizCommand mutual where deriving extends import open namespace section end variable universe
syn keyword wizCommand syntax macro macro_rules notation infix infixl infixr prefix postfix declare_syntax_cat
syn keyword wizCommand attribute extern export
syn keyword wizModifier private partial unsafe noncomputable protected
syn match   wizCommand '#\(eval\|check\|reduce\|print\|run\)\>'
syn keyword wizKeyword fun let in match with do by if then else return for unless mut at
syn keyword wizKeyword have show from calc
syn keyword wizSort Type Prop Sort
syn keyword wizTactic intro intros exact apply assumption rfl refl rewrite rw cases induction simp absurd cast transp ecase sorry
syn keyword wizBool true false

syn match wizDecl '\%(\<\%(def\|theorem\|lemma\|abbrev\|axiom\|inductive\|coinductive\|codata\|structure\|class\|instance\)\s\+\)\@<=[^ \t(:{\[]\+'
syn match wizCtor '\.\@<!\.\h[A-Za-z0-9_'!?]*'
syn match wizType '\<\u[A-Za-z0-9_'!?]*\%(\.\u[A-Za-z0-9_'!?]*\)*\>'
syn match wizNumber '\<\d\+\%(\.\d\+\)\?\>'
syn match wizNumber '\<0x\x\+\>'
syn match wizHole '?\h[A-Za-z0-9_']*'
syn match wizHole '\<_\>'
syn match wizOperator '[→←↔⟶⇒×≡≠≤≥∀∃λΠΣ⊢⧺∘⟨⟩⟦⟧↦·▸¬∧∨∣:=<>+*/|&^%$@-]\+'
syn region wizAttribute matchgroup=wizAttrDelim start='@\[' end='\]' contains=wizString,wizNumber
syn region wizString start='"' skip='\\\\\|\\"' end='"' contains=wizEscape
syn match  wizEscape contained '\\\%([nrt\\"'0]\|x\x\x\|u{\x\+}\)'
syn region wizRawString start='r\z(#*\)"' end='"\z1'
syn match  wizChar "'\%([^\\']\|\\[nrt\\'\"0]\)'"
syn keyword wizTodo contained TODO FIXME XXX NOTE
syn match  wizComment '--.*$' contains=wizTodo,@Spell
syn region wizBlockComment start='/-' end='-/' contains=wizBlockComment,wizTodo,@Spell
syn region wizDocComment start='/--' end='-/' contains=wizBlockComment,wizTodo,@Spell

hi def link wizCommand      Keyword
hi def link wizModifier     StorageClass
hi def link wizKeyword      Keyword
hi def link wizSort         Type
hi def link wizTactic       Special
hi def link wizBool         Boolean
hi def link wizDecl         Function
hi def link wizCtor         Constant
hi def link wizType         Type
hi def link wizNumber       Number
hi def link wizHole         Special
hi def link wizOperator     Operator
hi def link wizAttribute    PreProc
hi def link wizAttrDelim    PreProc
hi def link wizString       String
hi def link wizRawString    String
hi def link wizEscape       SpecialChar
hi def link wizChar         Character
hi def link wizTodo         Todo
hi def link wizComment      Comment
hi def link wizBlockComment Comment
hi def link wizDocComment   SpecialComment

let b:current_syntax = 'wiz'
