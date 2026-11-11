import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- (13m) The messages of `input` with the module `Loc` (`loc`) importable besides the
library, through the frontend (`runFrontend`) and through the command cache
(`Cache.elaborateUncached`, what `wiz check` runs): errors (rendered) and the rest. -/
def runLoc (loc input : String) : IO (List (Array String × Array String)) := do
  let lib ← preludeLoader
  let init : CommandState ZeroOneMany := { trustedModule := Tests.libModule, loader := fun m => if m == "Loc" then some loc else lib m }
  let split (s : CommandState ZeroOneMany) :=
    ((s.messages.filter (·.severity == .error)).map (·.render input), (s.messages.filter (·.severity != .error)).map (·.text))
  pure [split (runFrontend input init), split (← Cache.elaborateUncached input init)]

def okLoc (loc input : String) (infos : List String := []) : IO Unit := do
  for (errs, msgs) in ← runLoc loc input do
    unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
    checkEq (repr infos).pretty (repr msgs.toList).pretty

def failsLoc (loc input fragment : String) : IO Unit := do
  for (errs, _) in ← runLoc loc input do
    unless errs.size == 1 do throw (IO.userError s!"expected one error, got {errs.size}: {errs}")
    unless (errs[0]!.splitOn fragment).length > 1 do
      throw (IO.userError s!"error does not mention '{fragment}':\n{errs[0]!}")

/-- A module with `local` notation (an operator, a keyword with its macro rule) and an
exported operator that is defined with them. -/
def locMod : String := "import Prelude
local infixr:67 \" & \" => String.append
local infixr:67 \" :> \" => List.cons
local syntax (name := shout) \"shout\" term : term
local macro_rules
  | `(term| shout $x) => `(term| $x & \"!\")
infixr:67 \" &&& \" => String.append
def greet (s : String) : String := shout (\"hi \" & s)
def three : List Nat := 1 :> 2 :> 3 :> .nil
"

/-- A term language with identifiers, juxtaposition and `if … then … else`, run by macros
(13j); `decl` follows `declare_syntax_cat` (a keyword scope, or nothing). The file also
defines `then` and `else` as Wiz names. -/
def calcDsl (decl : String) : String := "import Prelude\ndeclare_syntax_cat calc_e" ++ decl ++ "
syntax (name := var) ident : calc_e
syntax (name := host) \"[\" term \"]\" : calc_e
syntax:lead (name := app) calc_e:max calc_e:max : calc_e
syntax:20 (name := ifE) \"when\" calc_e \"yes\" calc_e:20 \"no\" calc_e:20 : calc_e
syntax (name := calc) \"run_calc\" calc_e \"done\" : term
macro_rules
  | `(term| run_calc [ $t ] done) => `(term| $t)
macro_rules
  | `(term| run_calc $f $a done) => `(term| (run_calc $f done) (run_calc $a done))
macro_rules
  | `(term| run_calc when $c yes $a no $b done) => `(term| match run_calc $c done with | .true => run_calc $a done | .false => run_calc $b done)
def yes : Nat := 1
def no (when : Nat) : Nat := Nat.succ when
def isZero : Nat → Bool
  | .zero => .true
  | .succ _ => .false
"

/-- (R1) A linear token, for the projection tests. -/
def r1Header : String := "import Prelude\naxiom Tok : Type\n"

def languageGroup : Group where
  name := "language"
  exercise := "Stage 13"
  cases := [
    { name := "linear transport: Eq.subst, Eq.substBack and Eq.cast take a linear value (L4)", run := fun _ =>
        okLib ("import Prelude\naxiom Tok : Nat → Type\naxiom Tok.close : (1 t : Tok 0) → Unit\n" ++
          "def closeAt (0 n : Nat) (0 e : n = 0) (1 t : Tok n) : Unit := Tok.close (Eq.subst Tok e t)\n" ++
          "def closeBack (0 n : Nat) (0 e : 0 = n) (1 t : Tok n) : Unit := Tok.close (Eq.substBack Tok e t)\n" ++
          "def closeCast (0 n : Nat) (0 e : Tok n = Tok 0) (1 t : Tok n) : Unit := Tok.close (Eq.cast e t)\n" ++
          "def listCast (0 A B : Type) (0 e : A = B) (v : List A) : List B := Eq.subst List e v\n") },
    { name := "... still used exactly once", run := fun _ =>
        failsLib ("import Prelude\naxiom Tok : Nat → Type\naxiom Tok.close : (1 t : Tok 0) → Unit\n" ++
          "def twice (0 n : Nat) (0 e : n = 0) (1 t : Tok n) : Unit × Unit := (Tok.close (Eq.subst Tok e t), Tok.close (Eq.subst Tok e t))")
          "quantity 1 but used ω" },
    { name := "... where a transport with an unrestricted argument can't carry a linear value", run := fun _ =>
        failsLib ("import Prelude\naxiom Tok : Nat → Type\naxiom Tok.close : (1 t : Tok 0) → Unit\n" ++
          "def substω (0 P : Nat → Type) {0 a b : Nat} (0 e : a = b) (pa : P a) : P b := cast (transp (fun b _ => P a = P b) (refl (P a)) e) pa\n" ++
          "def closeAt (0 n : Nat) (0 e : n = 0) (1 t : Tok n) : Unit := Tok.close (substω Tok e t)")
          "quantity 1 but used ω" },
    -- (R1) projections are available only on unrestricted pairs
    { name := "p.1 and p.2 on a linear pair are rejected, whatever the components (R1: the audit's probes)", run := fun _ => do
        let needs := "a projection needs an unrestricted pair"
        failsLib (r1Header ++ "def drop1 {A : Type} (1 p : A × Tok) : A := p.1") needs
        failsLib (r1Header ++ "def drop2 {A : Type} (1 p : (1 a : A) × Tok) : A := p.1") needs
        failsLib (r1Header ++ "def drop3 {A : Type} (1 p : (1 t : Tok) × A) : A := p.2") needs
        -- the error says what to write
        failsLib (r1Header ++ "def drop1 {A : Type} (1 p : A × Tok) : A := p.1") "take the pair apart with `let 1 (x, y) := p; …`"
        -- a `let` at 1 of a projection is no better, and a pair in the middle of a tuple neither
        failsLib (r1Header ++ "def let1 {A : Type} (1 p : A × Tok) : A := let 1 a : A := p.1; a") needs
        failsLib (r1Header ++ "def mid {A : Type} (1 p : A × Tok × Tok) : Tok := p.2.1") needs },
    { name := "... a projection of an expression uses the expression ω times (R1)", run := fun _ => do
        failsLib (r1Header ++ "def bad {A : Type} (f : (1 t : Tok) → A × Tok) (1 t : Tok) : A := (f t).1")
          "cannot project (f t).1"
        okLib (r1Header ++ "def fine {A : Type} (f : (1 t : Tok) → A × Tok) (t : Tok) : A := (f t).1\n" ++
          "def split {A : Type} (f : (1 t : Tok) → A × Tok) (1 t : Tok) : (1 u : Tok) × A := let 1 (a, u) := f t; (u, a)") },
    { name := "... a linear pair is taken apart with let 1 (x, y) := p, which accounts for both components", run := fun _ => do
        okLib (r1Header ++ "def swap {A : Type} (1 p : A × Tok) : (1 t : Tok) × A := let 1 (a, t) := p; (t, a)\n" ++
          "def nest {A : Type} (1 p : A × Tok × Tok) : (1 t : Tok) × (1 u : Tok) × A := let 1 (a, r) := p; let 1 (t, u) := r; (u, t, a)\n" ++
          "def inTy (1 p : (A : Type) × A) (f : (0 A : Type) → (1 x : A) → Nat) : Nat := let 1 (A, x) := p; f A x")
        -- the split may not drop the bare second component either
        failsLib (r1Header ++ "def dropSplit {A : Type} (1 p : A × Tok) : A := let 1 (a, t) := p; a") "variable t declared with quantity 1 but used 0"
        -- and without a quantity it is a split at ω
        failsLib (r1Header ++ "def atω {A : Type} (1 p : A × Tok) : (1 t : Tok) × A := let (a, t) := p; (t, a)") "quantity 1 but used ω" },
    { name := "... an unrestricted pair has both projections, whatever its fields' quantities", run := fun _ =>
        okLib (r1Header ++ "def fstω {A : Type} (p : A × Tok) : A := p.1\ndef sndω {A : Type} (p : (1 a : A) × Tok) : Tok := p.2\n" ++
          "def both {A : Type} (p : A × Tok) : Tok × A := (p.2, p.1)\ndef mid {A : Type} (p : A × (1 t : Tok) × Tok) : Tok := p.2.1") },
    { name := "... a pair at a quantity variable can't be projected, but it can be split at that quantity", run := fun _ => do
        failsLib (r1Header ++ "def polyq {A : Type} {q : Qty} (%q p : A × Tok) : A := p.1") "a projection needs an unrestricted pair"
        okLib (r1Header ++ "def poly {A : Type} {q : Qty} (%q p : A × Tok) (k : (%q a : A) → (%q t : Tok) → Nat) : Nat := let %q (a, t) := p; k a t") },
    { name := "... erased positions project freely: a 0 argument, a let at 0, a 0 field, a split at 0", run := fun _ => do
        okLib (r1Header ++ "def erasedArg {A : Type} (0 p : A × Tok) (g : (0 a : A) → Nat) : Nat := g p.1\n" ++
          "def peek {A : Type} (1 p : A × Tok) (g : (0 a : A) → (1 p : A × Tok) → Nat) : Nat := g p.1 p\n" ++
          "def let0 {A : Type} (1 p : A × Tok) : A × Tok := let 0 a : A := p.1; p\n" ++
          "def field0 {A : Type} (1 p : A × Tok) : ((0 a : A) × Unit) × (A × Tok) := ((p.1, ()), p)\n" ++
          "def split0 {A : Type} (1 p : A × Tok) : A × Tok := let 0 (a, t) := p; p")
        -- what is bound at 0 there can't be used at runtime, and an erased variable has no runtime projection
        failsLib (r1Header ++ "def use0 {A : Type} (1 p : A × Tok) : A × (A × Tok) := let 0 a : A := p.1; (a, p)") "variable a declared with quantity 0"
        failsLib (r1Header ++ "def use00 {A : Type} (1 p : A × Tok) : A × (A × Tok) := let 0 (a, t) := p; (a, p)") "variable a declared with quantity 0"
        failsLib (r1Header ++ "def run0 {A : Type} (0 p : A × Tok) : A := p.1") "a projection needs an unrestricted pair" },
    { name := "... a 0 position is never evaluated: #eval of a let at 0, a 0 field, a split at 0, a 0 argument", run := fun _ =>
        okLib ("import Prelude\npartial def loop (u : Unit) : Nat × Nat := loop u\n" ++
          "def a : Nat := let 0 x : Nat := (loop ()).1; 1\ndef b : (0 x : Nat) × Nat := ((loop ()).1, 2)\n" ++
          "def c : Nat := let 0 (x, y) := loop (); 3\ndef d (f : (0 x : Nat) → Nat) : Nat := f (loop ()).1\n" ++
          "#eval a\n#eval b.2\n#eval c\n#eval d (fun _ => 4)") ["1", "2", "3", "4"] },
    { name := "... a structure can't be held at quantity 1 yet: no field access, no match, no nested split (R1)", run := fun _ => do
        let guard := r1Header ++ "structure Guard where\n  n : Nat\n  tok : Tok\n"
        okLib (guard ++ "def readω (g : Guard) : Nat × Tok := (g.n, g.tok)\ndef pass (1 g : Guard) : Guard := g")
        failsLib (guard ++ "def s1 (1 g : Guard) : Nat := g.n") "a structure can't be held at a quantity other than ω yet"
        failsLib (guard ++ "def s2 (1 g : Guard) : Tok := g.tok") "use a tuple `A × B` instead"
        -- (13h) `.mk n t` on a structure is the tuple pattern over its Σ: two projections,
        -- rejected at quantity 1 like a tuple pattern on a linear pair (`m1` below)
        failsLib (guard ++ "def s3 (1 g : Guard) : Nat × Tok := match g with\n  | .mk n t => (n, t)") "quantity 1 but used ω"
        failsLib (guard ++ "def s4 (1 g : Guard) : (1 t : Tok) × Nat := let 1 (n, rest) := g; let 1 (t, tail) := rest; (t, n)")
          "variable tail declared with quantity 1 but used 0"
        -- a tuple pattern in `match` is two projections: not for a linear pair
        failsLib (r1Header ++ "def m1 (1 p : Nat × Tok) : (1 t : Tok) × Nat := match p with\n  | (n, t) => (t, n)") "quantity 1 but used ω" },
    -- (linear-case p05) raw `ind` binds the payload at ω, so its scrutinee counts ω times
    { name := "ind on a linear scrutinee is rejected: it could duplicate or drop the payload", run := fun _ => do
        let box := r1Header ++ "def BoxD : Desc Unit := Desc.arg 1 Tok (fun _ => Desc.ret ())\ndef Box : Type := μ BoxD ()\n" ++
          "def box (1 t : Tok) : Box := con (t, (), ())\n"
        failsLib (box ++ "def dup (1 b : Box) : Tok × Tok := ind (fun _ _ => Tok × Tok) (fun i xs ih => (xs.1, xs.1)) b")
          "variable b declared with quantity 1 but used ω"
        failsLib (box ++ "def dropTok (1 t : Tok) : Unit := ind (fun _ _ => Unit) (fun i xs ih => ()) (box t)")
          "variable t declared with quantity 1 but used ω"
        okLib (box ++ "def dupω (b : Box) : Tok × Tok := ind (fun _ _ => Tok × Tok) (fun i xs ih => (xs.1, xs.1)) b") },
    { name := "a 0 position is never evaluated: a constructor field at 0, a 0 field of a structure (#eval)", run := fun _ =>
        okLib ("import Prelude\n" ++ zeroFieldDecls ++ "#eval e1\n#eval e2\n#eval e3\n#eval e4") ["7", "8", "9", "2"] },
    { name := "castRefl: a propositional regularity axiom in the Prelude; it doesn't compute (D1)", run := fun _ =>
        okLib ("import Prelude\ndef r (A : Type) (e : A = A) (a : A) : (cast e a : A) = a := castRefl e a\n" ++
          "#reduce fun (A : Type) (e : A = A) (a : A) => castRefl e a")
          ["fun A e a => castRefl A e a"] },
    { name := "an equation between numbers has one shape, numeral or constructor", run := fun _ =>
        okLib ("import Prelude\n#reduce ((0 : Nat) = 0)\n#reduce (Nat.zero = Nat.zero)\n#reduce ((0 : Nat) = Nat.zero)\n" ++
          "#reduce ((2 : Nat) = Nat.succ (Nat.succ Nat.zero))\n#reduce fun (m n : Nat) => (Nat.succ m = Nat.succ n)\n" ++
          "def t (e : (0 : Nat) = 0) : Nat.zero = Nat.zero := e\n")
          ["True", "True", "True", "True", "fun m n => m = n"] },
    { name := "a proof of True is not a pair", run := fun _ =>
        failsLib "import Prelude\ndef bad (x : True) : True := x.1\n" "cannot project" },
    { name := "recursion on a later argument, with parameters before the colon", run := fun _ =>
        okLib ("import Prelude\ndef addE (w : Nat) : List Nat → List Nat\n  | .nil => .cons w .nil\n" ++
          "  | .cons x xs => .cons x (addE w xs)\ndef app2 : Nat → List Nat → List Nat → List Nat\n" ++
          "  | k, .nil, ys => ys\n  | k, .cons x xs, ys => .cons (Nat.add x k) (app2 k xs ys)\n" ++
          "#eval addE 9 (.cons 1 .nil)\n#eval app2 10 (.cons 1 .nil) (.cons 7 .nil)")
          [".cons 1 (.cons 9 .nil)", ".cons 11 (.cons 7 .nil)"] },
    { name := "a parameter must be passed unchanged", run := fun _ =>
        failsLib "import Prelude\ndef bad (w : Nat) : List Nat → Nat\n  | .nil => w\n  | .cons x xs => bad x xs"
          "must pass the parameter w unchanged" },
    { name := "mutual (partial) definitions", run := fun _ =>
        okLib ("import Prelude\nmutual\ndef isEven : Nat → Bool\n  | .zero => .true\n  | .succ n => isOdd n\n" ++
          "def isOdd : Nat → Bool\n  | .zero => .false\n  | .succ n => isEven n\nend\n#eval isOdd 7\n" ++
          "partial def down (n : Nat) : Nat := match n with\n  | .zero => 0\n  | .succ m => down m\n#eval down 5")
          [".true", "0"] },
    { name := "a partial definition needs an inhabited type", run := fun _ =>
        failsLib "import Prelude\ninductive Void where\npartial def loop (n : Nat) : Void := loop n"
          "no witness found" },
    { name := "match without an expected type", run := fun _ =>
        okLib ("import Prelude\ndef f (b : Bool) (n : Nat) : Nat :=\n  let k := match b with\n    | .true => n\n" ++
          "    | .false => 0;\n  Nat.add k 1\n#eval f .true 4") ["5"] },
    { name := "tuple patterns", run := fun _ =>
        okLib ("import Prelude\ndef sum3 : Nat × Nat × Nat → Nat\n  | (a, b, c) => Nat.add a (Nat.add b c)\n" ++
          "def firstZero : Nat × Nat → Bool\n  | (.zero, _) => .true\n  | p => .false\n" ++
          "#eval sum3 (1, 2, 3)\n#eval firstZero (0, 5)\n#eval firstZero (2, 5)") ["6", ".true", ".false"] },
    { name := "the pipe operator", run := fun _ =>
        okLib "import Prelude\n#eval 3 |> Nat.succ |> Nat.succ" ["5"] },
    -- 13g
    { name := "as-patterns: x@p binds the matched value, and recursion on it is structural", run := fun _ =>
        okLib ("import Prelude\ndef last (A : Type) (d : A) : List A → A\n  | .nil => d\n  | .cons x .nil => x\n" ++
          "  | .cons _ xs@(.cons _ _) => last A d xs\n#eval last Nat 0 (.cons 1 (.cons 2 (.cons 3 .nil)))\n" ++
          "def dup : List Nat → List Nat\n  | .nil => .nil\n  | l@(.cons x _) => .cons x l\n#eval dup (.cons 1 (.cons 2 .nil))\n" ++
          "def both (p : Nat × Nat) : Nat := match p with\n  | q@(a, b) => Nat.add (Nat.add a b) q.1\n#eval both (1, 2)\n" ++
          "def nm : Nat → Nat\n  | n@m@(.succ _) => Nat.add n m\n  | z@_ => z\n#eval nm 3\n#eval nm 0")
          ["3", ".cons 1 (.cons 1 (.cons 2 .nil))", "4", "6", "0"] },
    { name := "as-patterns: the name must be a variable; not a term", run := fun _ => do
        failsLib "import Prelude\ndef f : Nat → Nat\n  | (.succ k)@n => n\n  | _ => 0" "an as-pattern is `x@p` with a variable"
        failsLib "import Prelude\ndef f (n : Nat) : Nat := n@n" "only allowed in a pattern"
        failsLib "import Prelude\ndef f : List Nat → Nat\n  | l@(.cons x) => x\n  | _ => 0" "cons expects 2 explicit arguments" },
    -- 13h
    { name := "structure patterns: .mk, S.mk and ⟨…⟩ bind the fields; nested and with parameters", run := fun _ =>
        okLib ("import Prelude\nstructure Stats where\n  hits : Nat\n  misses : Nat\n" ++
          "def t1 (s : Stats) : Nat := match s with\n  | .mk h m => Nat.add h m\n" ++
          "def t2 : Stats → Nat\n  | Stats.mk h m => Nat.add h m\n" ++
          "def t3 (s : Stats) : Nat := match s with\n  | ⟨h, m⟩ => Nat.add h m\n" ++
          "#eval t1 (Stats.mk 3 4)\n#eval t2 (Stats.mk 3 4)\n#eval t3 (Stats.mk 3 4)\n" ++
          "structure Box (A : Type) where\n  val : A\ndef unbox {A : Type} : Box A → A\n  | .mk a => a\n#eval unbox (Box.mk 7)\n" ++
          "def nested (p : Stats × Nat) : Nat := match p with\n  | (.mk (.succ h) _, k) => Nat.add h k\n" ++
          "  | (s@(.mk _ m), _) => Nat.add m s.hits\n#eval nested (Stats.mk 3 4, 10)\n#eval nested (Stats.mk 0 5, 10)\n" ++
          "structure Unit' where\ndef u (x : Unit') : Nat := match x with\n  | .mk => 1\n#eval u Unit'.mk")
          ["7", "7", "7", "7", "12", "5", "1"] },
    { name := "structure patterns: wrong constructor, wrong number of fields", run := fun _ => do
        failsLib ("import Prelude\nstructure Stats where\n  hits : Nat\n  misses : Nat\n" ++ "def f (s : Stats) : Nat := match s with\n  | .mk h => h")
          "Stats.mk expects 2 arguments (the fields hits, misses), got 1"
        failsLib ("import Prelude\nstructure Stats where\n  hits : Nat\n  misses : Nat\n" ++ "def f (s : Stats) : Nat := match s with\n  | .make h m => h")
          "Stats is a structure: its constructor is Stats.mk, not .make"
        failsLib ("import Prelude\nstructure Stats where\n  hits : Nat\n  misses : Nat\n" ++ "def f (n : Nat) : Nat := match n with\n  | ⟨h, m⟩ => h")
          "needs a type with one constructor, and Nat has 2" },
    { name := "anonymous constructors: a structure, a pair, a one-constructor data type; as terms and patterns", run := fun _ =>
        okLib ("import Prelude\nstructure Stats where\n  hits : Nat\n  misses : Nat\n" ++ "def s0 : Stats := ⟨3, 4⟩\n#eval s0.misses\n" ++
          "def swap (p : Nat × Bool) : Bool × Nat := match p with\n  | ⟨a, b⟩ => ⟨b, a⟩\n#eval (swap (1, .true)).2\n" ++
          "inductive Wrap where\n  | wrap (n : Nat) (b : Bool)\ndef w0 : Wrap := ⟨5, .true⟩\n" ++
          "def unwrap (w : Wrap) : Nat := match w with\n  | ⟨n, _⟩ => n\n#eval unwrap w0")
          ["4", "1", "5"] },
    { name := "anonymous constructors need an expected type with one constructor", run := fun _ => do
        failsLib "import Prelude\ndef f := ⟨1, 2⟩" "needs a structure, a pair or a data type with one constructor"
        failsLib "import Prelude\ndef f : Nat := ⟨1, 2⟩" "needs a type with one constructor, and Nat has 2"
        failsLib "import Prelude\ndef f : Nat → Nat := ⟨1, 2⟩" "needs a structure, a pair or a data type with one constructor" },
    { name := "let with a structure pattern: projections without a quantity, also with no expected type", run := fun _ =>
        okLib ("import Prelude\nstructure Stats where\n  hits : Nat\n  misses : Nat\n" ++ "def t4 (s : Stats) : Nat :=\n  let ⟨h, m⟩ := s\n  Nat.add h m\n" ++
          "def t5 (s : Stats) : Nat :=\n  let (.mk h m) := s;\n  Nat.add h m\n" ++
          "def t6 (s : Stats) := let ⟨h, _⟩ := s; Nat.succ h\n" ++
          "#eval t4 (Stats.mk 3 4)\n#eval t5 (Stats.mk 3 4)\n#eval t6 (Stats.mk 3 4)\n" ++
          "def t7 (s : Stats) : Nat :=\n  let ω ⟨h, m⟩ := s\n  Nat.add h m\n#eval t7 (Stats.mk 1 1)\n" ++
          "axiom Tok : Type\naxiom Tok.close : (1 t : Tok) → Unit\n" ++
          "def lin3 (1 p : Nat × Tok × Tok) : Unit × Unit :=\n  let 1 ⟨n, s, t⟩ := p\n  (Tok.close s, Tok.close t)\n")
          ["7", "7", "4", "2"] },
    -- the documented limitation (13h): the Σ of a structure ends in a marker tail that a
    -- linear split leaves unused; when the encoding changes this becomes a positive test
    { name := "let 1 ⟨a, b⟩ := s on a structure: nested splits, rejected today for the leftover tail", run := fun _ => do
        failsLib ("import Prelude\nstructure Stats where\n  hits : Nat\n  misses : Nat\n" ++ "def lin (1 s : Stats) : Nat × Nat :=\n  let 1 ⟨h, m⟩ := s\n  (h, m)")
          "cannot take a value of the structure Stats apart at quantity 1"
        failsLib ("import Prelude\nstructure Stats where\n  hits : Nat\n  misses : Nat\n" ++ "def lin (1 s : Stats) : Nat × Nat :=\n  let 1 (.mk h m) := s\n  (h, m)")
          "ends in a component that is not a field"
        failsLib ("import Prelude\nstructure Stats where\n  hits : Nat\n  misses : Nat\n" ++ "def f (s : Stats × Nat) : Nat :=\n  let ω ⟨⟨h, m⟩, k⟩ := s\n  h")
          "its components are names or `_`"
        failsLib ("import Prelude\ndef f (n : Nat) : Nat :=\n  let 1 ⟨a, b⟩ := n\n  a")
          "expects a structure or a tuple, got Nat" },
    -- 13i
    { name := "structure update: named fields replaced, the others projected", run := fun _ =>
        okLib ("import Prelude\nstructure Stats where\n  hits : Nat\n  misses : Nat\n" ++ "def bump (s : Stats) : Stats := { s with hits := Nat.succ s.hits }\n" ++
          "#eval (bump (Stats.mk 3 4)).hits\n#eval (bump (Stats.mk 3 4)).misses\n" ++
          "def both (s : Stats) : Stats := { { s with hits := 0 } with misses := 10, hits := 1 }\n" ++
          "#eval Nat.add (both (Stats.mk 3 4)).hits (both (Stats.mk 3 4)).misses\n" ++
          "structure Box (A : Type) where\n  val : A\n  tag : Nat\n" ++
          "def retag {A : Type} (b : Box A) (n : Nat) : Box A := { b with tag := n }\n#eval (retag (Box.mk Bool.true 1) 9).tag\n" ++
          "structure D where\n  n : Nat\n  p : n = 0\n" ++
          "def d2 (d : D) : D := { d with n := 0, p := rfl }\n#eval (d2 (D.mk 0 rfl)).n\n" ++
          "def t (s : Stats) : (bump s).misses = s.misses := rfl")
          ["4", "4", "11", "9", "0"] },
    { name := "structure update: unknown and repeated fields, a non-structure, a kept dependent field", run := fun _ => do
        failsLib ("import Prelude\nstructure Stats where\n  hits : Nat\n  misses : Nat\n" ++ "def f (s : Stats) : Stats := { s with hit := 1 }")
          "Stats has no field 'hit' (its fields are hits, misses)"
        failsLib ("import Prelude\nstructure Stats where\n  hits : Nat\n  misses : Nat\n" ++ "def f (s : Stats) : Stats := { s with hits := 1, hits := 2 }")
          "field 'hits' is updated twice"
        failsLib "import Prelude\ndef f (n : Nat) : Nat := { n with hits := 1 }"
          "structure update needs a value of a structure type"
        failsLib ("import Prelude\nstructure D where\n  n : Nat\n  p : n = 0\ndef f (d : D) : D := { d with n := 3 }")
          "field 'p' keeps its value, but its type" },
    { name := "recursion over a family at a concrete index", run := fun _ =>
        okLib ("import Prelude\ndef len : SyntaxF .false → Nat\n  | .nil => 0\n  | .cons _ xs => Nat.succ (len xs)\n" ++
          "#eval len (.cons .missing (.cons .missing .nil))") ["2"] },
    { name := "mutual inductive types", run := fun _ =>
        okLib ("import Prelude\nmutual\ninductive Tm where\n  | var (i : Nat)\n  | lam (body : Tm)\n  | app (f : Tm) (args : Tms)\n" ++
          "inductive Tms where\n  | nil\n  | cons (t : Tm) (ts : Tms)\nend\nmutual\ndef size : Tm → Nat\n  | .var _ => 1\n" ++
          "  | .lam b => Nat.succ (size b)\n  | .app f args => Nat.add (size f) (sizes args)\ndef sizes : Tms → Nat\n" ++
          "  | .nil => 0\n  | .cons t ts => Nat.add (size t) (sizes ts)\nend\n" ++
          "#eval size (.app (.lam (.var 0)) (.cons (.var 1) (.cons (.var 2) .nil)))") ["4"] },
    { name := "tactic keywords are not reserved", run := fun _ =>
        okLib "import Prelude\ndef f (first exact : Nat) : Nat := Nat.add first exact\n#eval f 1 2\ndef t : Nat := by exact 3" ["3"] },
    { name := "a catch-all of a recursive definition is the value at hand", run := fun _ =>
        okLib ("import Prelude\ndef g : Nat → Nat\n  | .succ k => g k\n  | x => Nat.succ x\n" ++
          "def t : g 3 = 1 := rfl\n#eval g 3") ["1"] },
    { name := "structural recursion through a function field of a mutual family", run := fun _ =>
        okLib ("import Prelude\nmutual\ninductive A where\n  | a0\n  | a1 (f : Unit → A)\n" ++
          "inductive B where\n  | b0\n  | b1 (x : A)\nend\n" ++
          "def depthA : A → Nat\n  | .a1 f => Nat.succ (depthA (f ()))\n  | .a0 => 0\n" ++
          "#eval depthA (.a1 (fun _ => .a1 (fun _ => .a0)))") ["2"] },
    { name := "13c: if, &&, || and ! in the Prelude", run := fun _ =>
        okLib ("import Prelude\ndef f (b : Bool) (n : Nat) : Nat := if b then n + 1 else 0\n#eval f .true 3\n" ++
          "#eval if Nat.beq 1 1 && !(Nat.beq 2 3) then \"yes\" else \"no\"\n" ++
          "#eval Nat.beq 1 1 && !(Nat.beq 2 3) || Bool.false\n#eval (Bool.false || Bool.true) && Bool.false\n" ++
          "def nested (n : Nat) : Nat := match n with\n  | .zero => if Nat.beq n 0 then 1 else 2\n  | .succ m => m\n#eval nested 0\n" ++
          "def t1 (b : Bool) : (Bool.true && b) = b := rfl\ndef t2 (b : Bool) : (Bool.false || b) = b := rfl\n")
          ["4", "\"yes\"", ".true", ".false", "1"] },
    { name := "13c: && and || short-circuit in compiled code", run := fun _ =>
        ioRun ("import IO\npartial def spin (n : Nat) : Bool := spin n\n" ++
          "def main : IO Unit := IO.println (if Bool.false && spin 0 then \"bad\" else if Bool.true || spin 1 then \"lazy ok\" else \"bad\")")
          "lazy ok\n" },
    { name := "13d: Functor and Applicative (import Functor)", run := fun _ =>
        okLib ("import Functor\n#eval Nat.add <$> Option.some 1 <*> Option.some 2\n" ++
          "#eval (fun (a b : Nat) => (a, b)) <$> List.cons 1 (List.cons 2 .nil) <*> List.cons 3 .nil\n" ++
          "#eval Nat.succ <$> List.cons 1 (List.cons 2 .nil)\n#eval Nat.succ <$> (Except.error \"e\" : Except String Nat)\n" ++
          "def addOpt (x y : Option Nat) : Option Nat := do\n  a ← x;\n  b ← y;\n  Monad.pure (a + b)\n#eval addOpt (.some 1) (.some 2)\n" ++
          "def pairT : TacticM (Nat × Nat) := (fun (a b : Nat) => (a, b)) <$> TacticM.pure 1 <*> TacticM.pure 2\n")
          [".some 3", ".cons (1, 3) (.cons (2, 3) .nil)", ".cons 2 (.cons 3 .nil)", ".error \"e\"", ".some 3"] },
    { name := "13d: <$> and <*> for IO, from its Monad instance", run := fun _ =>
        ioRun ("import IO\nimport Functor\ndef main : IO Unit := do\n  n ← Nat.add <$> IO.pure 40 <*> IO.pure 2;\n" ++
          "  IO.println (Nat.toString n)") "42\n" },
    { name := "13e: ∃ binders, ¬, and ASCII spellings (import Logic)", run := fun _ =>
        okLib ("import Logic\ndef t1 : ∃ n, n = 3 := Ex.intro (fun n => n = 3) 3 rfl\n" ++
          "def t2 : ∃ n : Nat, n + n = 4 := Ex.intro _ 2 rfl\ndef t3 : ∃ (n : Nat), n = 3 := Ex.intro _ 3 rfl\n" ++
          "def t5 : ∃ (n : Nat) m, n = m ∧ m = n := Ex.intro (fun n => ∃ m, n = m ∧ m = n) 3 (Ex.intro (fun m => 3 = m ∧ m = 3) 3 (rfl, rfl))\n" ++
          "def same {A : Type} (P : A → A → Prop) : (∃ x y : A, P x y) → @Ex A (fun x => @Ex A (fun y => P x y)) := fun h => h\n" ++
          "def swap {A : Type} {P : A → A → Prop} (h : ∃ x y, P x y) : ∃ y x, P x y :=\n" ++
          "  Ex.elim h (fun x h' => Ex.elim h' (fun y p => Ex.intro (fun y => ∃ x, P x y) y (Ex.intro (fun x => P x y) x p)))\n" ++
          "def nope : ¬ (exists (b : Bool), b = .true ∧ b = .false) :=\n  fun h => Ex.elim h (fun b p => Bool.trueNeFalse (Eq.trans (Eq.symm p.1) p.2))\n" ++
          "def t7 : forall (n : Nat), n = n := fun n => rfl\n" ++
          "def t8 {P Q : Prop} (h : P <-> Q) (p : P) : (Q /\\ P) \\/ False := Or.inl (h.1 p, p)\n#check t5")
          ["t5 : Ex Nat (fun n => Ex Nat (fun m => And (n = m) (m = n)))"] },
    { name := "13f: let with a tuple pattern of three or more names", run := fun _ =>
        okLib ("import Prelude\ndef f (p : Nat × Nat × Nat) : Nat := let (a, b, c) := p; a + b * c\n#eval f (1, 2, 3)\n" ++
          "def g (p : Nat × Bool × Nat × Nat) : Nat := let (a, b, c, d) := p; match b with\n  | .true => a + c + d\n  | .false => 0\n" ++
          "#eval g (1, .true, 3, 4)\ndef tuple : Nat := 7\ndef noCapture (p : Nat × Nat × Nat) : Nat := let (a, b, c) := p; tuple\n" ++
          "#eval noCapture (1, 2, 3)\naxiom Tok : Type\naxiom Tok.close : (1 t : Tok) → Unit\n" ++
          "def lin (1 p : Nat × Tok × Tok) : Unit × Unit :=\n  let 1 (n, s, t) := p;\n  (Tok.close s, Tok.close t)\n")
          ["7", "8", "7"] },
    { name := "... and a linear one still binds each component once", run := fun _ =>
        failsLib ("import Prelude\naxiom Tok : Type\naxiom Tok.close : (1 t : Tok) → Unit\n" ++
          "def lin (1 p : Nat × Tok × Tok) : Unit × Unit :=\n  let 1 (n, s, t) := p;\n  (Tok.close s, Tok.close s)\n")
          "quantity 1 but used" },
    -- (13k) list literals: a Prelude macro
    { name := "list literals: [a, b, c], [], nested, multi-line, with ++", run := fun _ =>
        okLib ("import Prelude\ndef xs : List Nat := [1, 2, 3]\ndef ys : List String := []\n" ++
          "def zs : List (List Nat) := [[], [1], [Nat.add 1 1, 3]]\ndef ws : List Nat := [\n  4,\n  5\n]\n" ++
          "def t : List.length [1, 2, 3] = 3 := rfl\n" ++
          "#eval xs\n#eval ys\n#eval zs\n#eval ws ++ [6]\n#eval List.length ([] : List Nat)")
          [".cons 1 (.cons 2 (.cons 3 .nil))", ".nil", ".cons .nil (.cons (.cons 1 .nil) (.cons (.cons 2 (.cons 3 .nil)) .nil))",
           ".cons 4 (.cons 5 (.cons 6 .nil))", "0"] },
    { name := "... in patterns: [], [x], [x, y], inside tuples, constructors, ⟨…⟩ and x@p", run := fun _ =>
        okLib ("import Prelude\ndef len : List Nat → Nat\n  | [] => 0\n  | [_] => 1\n  | [_, _] => 2\n  | _ => 9\n" ++
          "def f (p : List Nat × List Nat) : Nat := match p with\n  | ([x], [y, z]) => Nat.add x (Nat.add y z)\n" ++
          "  | ([], _) => 0\n  | (.cons x _, _) => x\n" ++
          "def g : List (List Nat) → Nat\n  | .cons [x] _ => x\n  | _ => 0\n" ++
          "structure P where\n  a : List Nat\n  b : Nat\ndef h : P → Nat\n  | ⟨[x], _⟩ => x\n  | _ => 0\n" ++
          "def k : List Nat → List Nat\n  | xs@[_] => xs ++ xs\n  | xs => xs\n" ++
          "#eval len []\n#eval len [5]\n#eval len [5, 6]\n#eval len [5, 6, 7]\n#eval f ([1], [2, 3])\n#eval g [[7]]\n" ++
          "#eval h ⟨[8], 0⟩\n#eval k [9]")
          ["0", "1", "2", "9", "6", "7", "8", ".cons 9 (.cons 9 .nil)"] },
    { name := "... numerals in a list literal are elaborated at the element type (7e)", run := fun _ => do
        let lib ← preludeLoader
        let int ← IO.FS.readFile "lib/Int.wiz"
        let input := "import Word\nimport Int\n#eval ([1, 2] : List U8)\n#eval ([1, 2] : List Int)\n" ++
          "def w : List U8 := [255, 1 + 2]\n#eval w"
        let s := runFrontend (R := ZeroOneMany) input { trustedModule := Tests.libModule, loader := fun m => if m == "Int" then some int else lib m }
        let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render input
        unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
        checkEq (repr [".cons (.mk 1) (.cons (.mk 2) .nil)", ".cons 1 (.cons 2 .nil)", ".cons (.mk 255) (.cons (.mk 3) .nil)"]).pretty
          (repr (s.messages.toList.map (·.text))).pretty },
    { name := "... instance binders and Enum [..] still parse", run := fun _ =>
        okLib ("import Prelude\ndef f {m : Type → Type} [Monad m] : m Nat := Monad.pure 1\n" ++
          "def g : (m : Type → Type) → [Monad m] → m Nat := fun m => Monad.pure 2\n" ++
          "def h : [inst : Monad TacticM] → Nat := 3\ndef E : Type := Enum [a, b]") },
    -- (13l) `++` is a class method
    { name := "++ appends lists and strings (class Append)", run := fun _ =>
        okLib ("import Prelude\ndef a (ys : List Nat) : List Nat := .cons 1 .nil ++ ys ++ .nil\n" ++
          "def b {A : Type} (xs : List A) : List A := xs ++ xs\ndef c (s : String) : String := \"<\" ++ s ++ \">\"\n" ++
          "#eval a [2]\n#eval b [1]\n#eval c \"x\"")
          [".cons 1 (.cons 2 .nil)", ".cons 1 (.cons 1 .nil)", "\"<x>\""] },
    -- (13m) `local` notation
    { name := "local notation is used in its module and not seen by importers", run := fun _ => do
        okLoc locMod "import Loc\n#eval greet \"a\" &&& \"b\"\n#eval three" ["\"hi a!b\"", ".cons 1 (.cons 2 (.cons 3 .nil))"]
        failsLoc locMod "import Loc\ndef x : String := \"a\" & \"b\"" "unexpected character '&'"
        -- the local keyword is an identifier again
        okLoc locMod "import Loc\ndef shout : Nat := 4\n#eval shout" ["4"] },
    { name := "... an importer may define the same notation at another meaning", run := fun _ =>
        okLoc locMod "import Loc\ninfixr:67 \" & \" => List.append\n#eval [1] & [2]\nsyntax (name := shout) \"shout\" term : term\nmacro_rules\n  | `(term| shout $x) => `(term| [$x])\n#eval shout 1"
          [".cons 1 (.cons 2 .nil)", ".cons 1 .nil"] },
    { name := "... in the main file it is ordinary notation; only grammar commands can be local", run := fun _ => do
        okLib "import Prelude\nlocal infixl:65 \" +! \" => Nat.add\n#eval 1 +! 2" ["3"]
        failsLib "import Prelude\nlocal def x : Nat := 1" "can be `local`" },
    -- keyword scopes (13j): `when`/`yes`/`no` are keywords inside `run_calc … done` only
    -- (not `if`/`then`/`else`: the Prelude's `if` (13c) reserves those in every file)
    { name := "keyword scope: a DSL's keywords are identifiers outside it (13j)", run := fun _ =>
        okLib (calcDsl " (keywords := calc_kw)" ++
          "#eval run_calc when [isZero] [0] yes [no] [yes] no [no (no yes)] done\n" ++
          "#eval run_calc when [isZero] [yes] yes [5] no [no 7] done") ["2", "8"] },
    { name := "... and not its own identifiers", run := fun _ =>
        failsLib (calcDsl " (keywords := calc_kw)" ++ "#eval run_calc [no] yes done")
          "identifier ('yes' is a keyword here)" },
    { name := "... without the scope the DSL's `when` is an application", run := fun _ => do
        let prelude ← IO.FS.readFile "lib/Prelude.wiz"
        let input := calcDsl "" ++ "#eval run_calc when [isZero] [0] yes [no] [yes] no [no (no yes)] done"
        let s := runFrontend (R := ZeroOneMany) input { trustedModule := Tests.libModule, loader := fun m => if m == "Prelude" then some prelude else none }
        check ((s.messages.filter (·.severity == .error)).size > 0) "expected errors" }
  ]

builtin_initialize registerGroup languageGroup

end Tests.Elab
