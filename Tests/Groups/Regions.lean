import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-! ## Regions: borrow checking as typing (lib/Region.wiz, Feral RD12) -/

def regionsPush : String :=
  "def push1 {ρ : Region} (v : Uniq ρ (List Nat)) : Result (Unit × Uniq ρ (List Nat)) :=\n  .ok ((), Uniq.set v (List.cons 1 v.val))\n"

def regionsLongest : String :=
  "def longest {ρa ρb : Region} (0 h : Outlives ρa ρb) (x : Shr ρa Nat) (y : Shr ρb Nat) : Result (Shr ρb Nat) :=\n" ++
  "  match Nat.lt x.val y.val with\n  | .true => .ok y\n  | .false => .ok (Shr.weaken h x)\n"

/-- `swap` through two `&mut`, called on two locals borrowed in nested scopes. -/
def regionsSwap : String := r#"def swap {ρ₁ ρ₂ : Region} {A : Type} (x : Uniq ρ₁ A) (y : Uniq ρ₂ A) : Result (Unit × Uniq ρ₁ A × Uniq ρ₂ A) :=
  let t := x.val;
  .ok ((), Uniq.set x y.val, Uniq.set y t)
"#

/-- A linked list through `&mut`: recursion on reborrows of the tails, and a cursor. -/
def regionsList : String := r#"partial def incrAll {ρ : Region} (l : Uniq ρ (List Nat)) : Result (Unit × Uniq ρ (List Nat)) :=
  Uniq.reborrow l (fun ρ' h l r =>
    match r.val with
    | .nil => .ok ((), r)
    | .cons x tail => (match Uniq.borrow ρ' tail (fun ρt ht tail rt => incrAll rt) with
      | .ok q => let (u, tail) := q; .ok ((), Uniq.set r (List.cons (Nat.succ x) tail))
      | .err e => .err e))
partial def pushBack.loop {ρ : Region} (x : Nat) (cur : Mut ρ (List Nat) (List Nat)) : Mut ρ (List Nat) (List Nat) :=
  match Mut.get cur with
  | .cons y next => pushBack.loop x (Mut.comp cur (fun (_ : List Nat) => (next, fun (n : List Nat) => List.cons y n)))
  | .nil => Mut.set cur (List.cons x List.nil)
def pushBack {ρ : Region} (l : Uniq ρ (List Nat)) (x : Nat) : Result (Unit × Uniq ρ (List Nat)) :=
  .ok ((), Mut.release (pushBack.loop x (Mut.whole l)))
def listMain (xs : List Nat) : Result (List Nat) :=
  match Uniq.borrow Region.static xs (fun ρ h xs r =>
    match incrAll r with
    | .ok q => let (u, r) := q; pushBack r 7
    | .err e => .err e) with
  | .ok p => let (u, xs) := p; .ok xs
  | .err e => .err e
"#

/-- Returning one of two `&mut` borrows: `'a : 'b` is the evidence for `Mut.weaken`. -/
def regionsPick (bound : Bool := true) : String :=
  let (hb, hx) := if bound then ("(0 h : Outlives ρa ρb) ", "Mut.weaken h (Mut.ofUniq x)") else ("", "Mut.ofUniq x")
  s!"def pick \{ρa ρb : Region} {hb}(c : Bool) (x : Uniq ρa Nat) (y : Uniq ρb Nat) :
    Result (Mut ρb Nat (Uniq ρa Nat × Uniq ρb Nat)) :=
  match c with
  | .true => .ok (Mut.mapBack ({hx}) (fun (x : Uniq ρa Nat) => (x, y)))
  | .false => .ok (Mut.mapBack (Mut.ofUniq y) (fun (y : Uniq ρb Nat) => (x, y)))
"

/-- Two locals `a := 1` and `b := 2`, borrowed in nested scopes (`outer` first), and `body`
on the borrows `ra`, `rb` (evidence `ha`, `hb`); `body` hands back `(ra, rb)` as `.ok`. -/
def regionsTwo (name outer body : String) : String :=
  let (o, i) := if outer == "a" then ("a", "b") else ("b", "a")
  s!"def {name} : Result (Nat × Nat) :=
  match Uniq.borrow Region.static {if o == "a" then 1 else 2} (fun ρ{o} h{o} {o} r{o} =>
    match Uniq.borrow ρ{o} {if i == "a" then 1 else 2} (fun ρ{i} h{i} {i} r{i} =>
      match {body} with
      | .ok q => let (ra, rb) := q; .ok ({if o == "a" then "ra, rb" else "rb, ra"})
      | .err e => .err e) with
    | .ok q => let (r, x) := q; .ok (x, r)
    | .err e => .err e) with
  | .ok p => let (x, y) := p; .ok {if o == "a" then "(y, x)" else "(x, y)"}
  | .err e => .err e
"

/-- The front end's state for `src`, with every library importable. -/
def libsState (src : String) (unbox : Bool := false) : IO (CommandState ZeroOneMany) := do
  let s := runFrontend (R := ZeroOneMany) src
    { trustedModule := Tests.libModule, loader := ← libLoader, globals := { unboxStructs := unbox } }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  pure s

/-- The optimised IR of the program computing `n`: `n` and the functions lifted from it. -/
def libsIR (s : CommandState ZeroOneMany) (n : Name) : IO (List String) := do
  match (do
      let code ← (compileReachable s.globals s.builtins [n]).mapError toString
      IR.lowerProgram code (.global n) : Except String (Array IR.Decl)) with
  | .ok decls =>
    pure ((decls.filter (·.name.startsWith n)).toList.map (·.optimize.toString))
  | .error e => throw (IO.userError e)

/-- The objects allocated computing `n` on the checked heap (a leak is an error). -/
def libsAllocs (s : CommandState ZeroOneMany) (n : Name) : IO Nat := do
  match (do
      let code ← (compileReachable s.globals s.builtins [n]).mapError toString
      let decls ← IR.lowerProgram code (.global n)
      let (_, a) ← IR.runProgram (decls.map (·.optimize))
      pure a : Except String Nat) with
  | .ok a => pure a
  | .error e => throw (IO.userError s!"{n}: {e}")

def regionsGroup : Group where
  name := "regions"
  exercise := "lib/Region.wiz (Feral lifetimes)"
  cases := [
    { name := "handles in different regions are different types; regions are inferred", run := fun _ => do
        okLibs ("import Region\ndef same {ρ : Region} (m : Mut ρ Nat (List Nat)) : Mut ρ Nat (List Nat) := m\n" ++
          "def get {ρ : Region} (x : Shr ρ Nat) : Nat := x.val\n#eval Shr.borrow Region.static 4 (fun ρ h x => .ok (get x))") [".ok 4"]
        failsLibs "import Region\ndef bad {ρ ρ' : Region} (m : Mut ρ Nat (List Nat)) : Mut ρ' Nat (List Nat) := m" "mismatch"
        failsLibs "import Region\ndef bad {ρ ρ' : Region} (x : Shr ρ Nat) : Shr ρ' Nat := x" "mismatch" },
    { name := "a mutable borrow scope hands the lender back", run := fun _ =>
        okLibs ("import Region\n" ++ regionsPush ++
          "#eval Uniq.borrow Region.static List.nil (fun ρ h v r => push1 r)") [".ok ((), .cons 1 .nil)"] },
    { name := "outlives evidence from nested scopes lets a reference flow outward", run := fun _ =>
        okLibs ("import Region\n" ++ regionsLongest ++
          "#eval Shr.borrow Region.static 3 (fun ρa ha a => Shr.borrow ρa 5 (fun ρb hb b =>\n" ++
          "  match longest hb a b with\n  | .ok r => .ok r.val\n  | .err e => .err e))") [".ok 5"] },
    { name := "without the bound, a &'a is not a &'b", run := fun _ =>
        failsLibs ("import Region\ndef longest {ρa ρb : Region} (x : Shr ρa Nat) (y : Shr ρb Nat) : Result (Shr ρb Nat) :=\n" ++
          "  match Nat.lt x.val y.val with\n  | .true => .ok y\n  | .false => .ok x") "mismatch" },
    { name := "returning a borrow of a local is a type error (E0515)", run := fun _ =>
        failsLibs ("import Region\ndef bad {ρ : Region} (x : Shr ρ Nat) : Result (Shr ρ Nat) :=\n" ++
          "  Shr.borrow ρ 5 (fun ρy hy y => .ok y)") "mismatch" },
    { name := "a borrow can't outlive its scope (E0597)", run := fun _ =>
        failsLibs ("import Region\n" ++ regionsLongest ++
          "def bad : Result Nat := Shr.borrow Region.static 3 (fun ρa ha a =>\n" ++
          "  match Shr.borrow ρa 5 (fun ρb hb b => longest hb a b) with\n  | .ok r => .ok r.val\n  | .err e => .err e)")
          "escapes the scope" },
    { name := "using the lender while it is mutably borrowed is a type error (E0499/E0502)", run := fun _ => do
        failsLibs ("import Region\n" ++ regionsPush ++
          "def bad : Result (Nat × List Nat) := Uniq.borrow Region.static List.nil (fun ρ h v r =>\n" ++
          "  match push1 r with\n  | .ok q => .ok (List.length v, q.2)\n  | .err e => .err e)") "mismatch"
        failsLibs ("import Region\n" ++ regionsPush ++
          "def bad : Result (Unit × List Nat) := Uniq.borrow Region.static List.nil (fun ρ1 h1 v r1 =>\n" ++
          "  match Uniq.borrow ρ1 v (fun ρ2 h2 v r2 => push1 r2) with\n  | .ok q => .ok ((), r1)\n  | .err e => .err e)") "mismatch" },
    { name := "swap through two &mut, each borrow in its own region", run := fun _ =>
        okLibs ("import Region\n" ++ regionsSwap ++ "def swap2 {ρ₁ ρ₂ : Region} (x : Uniq ρ₁ Nat) (y : Uniq ρ₂ Nat) : Result (Uniq ρ₁ Nat × Uniq ρ₂ Nat) :=\n  match swap x y with\n  | .ok r => let (u, xy) := r; let (x, y) := xy; .ok (x, y)\n  | .err e => .err e\n" ++ regionsTwo "t" "a" "swap2 ra rb" ++ "#eval t") [".ok (2, 1)"] },
    { name := "a linked list through &mut: recursion on reborrows of the tails, and a cursor", run := fun _ =>
        okLibs ("import Region\n" ++ regionsList ++ "#eval listMain (List.cons 1 (List.cons 2 List.nil))")
          [".ok (.cons 2 (.cons 3 (.cons 7 .nil)))"] },
    { name := "returning one of two &mut borrows needs 'a : 'b (Mut.weaken)", run := fun _ => do
        okLibs ("import Region\n" ++ regionsPick ++ "def setPick {ρa ρb : Region} (0 h : Outlives ρa ρb) (c : Bool) (x : Uniq ρa Nat) (y : Uniq ρb Nat) : Result (Uniq ρa Nat × Uniq ρb Nat) :=\n  match pick h c x y with\n  | .ok m => .ok (Mut.finish (Mut.set m 10))\n  | .err e => .err e\n" ++
          regionsTwo "t1" "a" "setPick hb .true ra rb" ++ regionsTwo "t2" "a" "setPick hb .false ra rb" ++ "#eval t1\n#eval t2")
          [".ok (10, 2)", ".ok (1, 10)"]
        failsLibs ("import Region\n" ++ regionsPick (bound := false)) "mismatch"
        -- the bound pointing the wrong way: b is borrowed first, so only 'b : 'a is known
        failsLibs ("import Region\n" ++ regionsPick ++ "def setPick {ρa ρb : Region} (0 h : Outlives ρa ρb) (c : Bool) (x : Uniq ρa Nat) (y : Uniq ρb Nat) : Result (Uniq ρa Nat × Uniq ρb Nat) :=\n  match pick h c x y with\n  | .ok m => .ok (Mut.finish (Mut.set m 10))\n  | .err e => .err e\n" ++ regionsTwo "t" "b" "setPick ha .true ra rb") "mismatch" },
    { name := "a borrow is shortened, never lengthened, and a local's &mut can't be returned (E0515)", run := fun _ => do
        failsLibs ("import Region\ndef bad {σ : Region} (v : Uniq σ Nat) : Result (Unit × Uniq σ Nat) :=\n" ++
          "  Uniq.reborrow v (fun ρ h v r => .ok ((), Mut.finish (Mut.weaken h (Mut.ofUniq r))))") "mismatch"
        failsLibs ("import Region\ndef bad {ρ : Region} (v : Uniq ρ Nat) : Result (Mut ρ Nat (Uniq ρ Nat)) :=\n" ++
          "  match Uniq.borrow ρ 5 (fun ρl hl l rl => .ok (Mut.ofUniq rl, rl)) with\n" ++
          "  | .ok p => let (m, n) := p; .ok m\n  | .err e => .err e") "escapes the scope" },
    { name := "two borrows of different regions are not interchangeable", run := fun _ =>
        failsLibs ("import Region\ndef same {ρ : Region} (x y : Uniq ρ Nat) : Result (Uniq ρ Nat × Uniq ρ Nat) := .ok (x, y)\n" ++
          regionsTwo "t" "a" "same ra rb") "mismatch" },
    { name := "KNOWN GAP (accepted today; wishful: linear-case): duplicating a &mut, reading the lender under its outer name, packing a handle with its region", run := fun _ => do
        -- E0499 by duplicating the handle: handles are ω, not linear
        okLibs ("import Region\n" ++ regionsSwap ++ "def dup : Result (Unit × Nat) := Uniq.borrow Region.static 1 (fun ρ h a r =>\n" ++
          "  match swap r r with\n  | .ok q => let (u, r1r2) := q; let (r1, r2) := r1r2; .ok ((), r1)\n  | .err e => .err e)\n#eval dup") [".ok ((), 1)"]
        -- E0502: the `Lent` token only shadows the lender's name; named `tok`, `v` is visible
        okLibs ("import Region\ndef lender (v : List Nat) : Result (Nat × List Nat) := Uniq.borrow Region.static v (fun ρ h tok r =>\n" ++
          "  .ok (List.length v, Uniq.set r List.nil))\n#eval lender (List.cons 1 List.nil)") [".ok (1, .nil)"]
        -- a handle leaves its scope packed with its region, and is written through afterwards
        okLibs ("import Region\ndef esc (v : List Nat) : Result (((0 r : Region) × Uniq r (List Nat)) × List Nat) :=\n" ++
          "  Uniq.borrow Region.static v (fun ρ h tok r => .ok ((ρ, r), r))\n" ++
          "def use (v : List Nat) : Result (List Nat) := match esc v with\n" ++
          "  | .ok p => let (packed, v) := p; let (ρ, r) := packed; .ok (Uniq.set r List.nil).val\n  | .err e => .err e\n" ++
          "#eval use (List.cons 1 List.nil)") [".ok .nil"] },
    { name := "handles can't be forged outside lib/Region.wiz (private constructors, 13b)", run := fun _ => do
        failsLibs "import Region\ndef forge {ρ : Region} : Shr ρ Nat := Shr.mk 5" "'Shr.mk' is private to module Region"
        failsLibs "import Region\ndef forge {ρ : Region} (s : List Nat) : Uniq ρ (List Nat) := Uniq.mk s" "private"
        failsLibs "import Region\ndef forge {ρ : Region} : Lent ρ Nat := .mk ()" "Lent"
        failsLibs "import Region\ndef forge {ρ : Region} : Shr ρ Nat := (5, ())" "Shr"
        failsLibs ("import Region\nstructure MyShr (ρ : Region) (A : Type) where\n  val : A\n" ++
          "def forge {ρ : Region} : Shr ρ Nat := MyShr.mk 5") "mismatch"
        -- nor through an equation with a look-alike (the kernel compares by shape; `rfl`
        -- compares in the elaborator's view)
        failsLibs ("import Region\nstructure MyShr (ρ : Region) (A : Type) where\n  val : A\n" ++
          "def forge {ρ : Region} (x : Nat) : Shr ρ Nat := cast rfl (MyShr.mk x : MyShr ρ Nat)") "not definitionally equal" },
    { name := "with --unbox-structs a handle is its value at run time; a scope is its body run in place (22i)", run := fun _ => do
        let s ← libsState ("import Region\n" ++ regionsPush ++
          "def get {ρ : Region} (x : Shr ρ Nat) : Nat := x.val\n" ++
          "def scoped (xs : List Nat) : Result (Unit × List Nat) := Uniq.borrow Region.static xs (fun ρ h v r => push1 r)\n" ++
          "def direct (xs : List Nat) : Result (Unit × List Nat) := .ok ((), List.cons 1 xs)\n" ++
          "def nested (a b : List Nat) : Result (List Nat × List Nat) :=\n" ++
          "  match Uniq.borrow Region.static a (fun ρa ha a ra =>\n" ++
          "    match Uniq.borrow ρa b (fun ρb hb b rb =>\n" ++
          "      match push1 rb with\n      | .ok q => .ok (ra, q.2)\n      | .err e => .err e) with\n" ++
          "    | .ok q => .ok (q.2, q.1)\n    | .err e => .err e) with\n" ++
          "  | .ok p => .ok (p.2, p.1)\n  | .err e => .err e\n" ++
          "def t1 : Result (Unit × List Nat) := scoped List.nil\n" ++
          "def t0 : Result (Unit × List Nat) := direct List.nil\n" ++
          "def t2 : Result (List Nat × List Nat) := nested List.nil List.nil\n#run t1\n#eval t1\n#run t2\n" ++
          "#run Shr.borrow Region.static 4 (fun ρ h x => .ok (get x))") (unbox := true)
        let msgs := s.messages.toList.map (·.text)
        checkEq [".ok ((), .cons 1 .nil)", ".ok ((), .cons 1 .nil)", ".ok (.nil, .cons 1 .nil)", ".ok 4"] msgs
        -- `x.val` is `x`: no projection
        let getIR ← libsIR s "get"
        check (getIR.all fun d => (d.splitOn "proj").length == 1) s!"a projection:\n{"\n".intercalate getIR}"
        -- no closure for the scopes' bodies, and nothing lifted
        for n in ["scoped", "nested"] do
          let ir ← libsIR s n
          check (ir.length == 1 && ir.all fun d => (d.splitOn "pap").length == 1 && (d.splitOn "ap x").length == 1)
            s!"{n}: a closure:\n{"\n".intercalate ir}"
        -- a borrow costs no allocation: the same objects as without it
        checkEq (← libsAllocs s "t0") (← libsAllocs s "t1") }
  ]

builtin_initialize registerGroup regionsGroup

end Tests.Elab
