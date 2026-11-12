import Wiz
import Tests.Harness
import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

/-!
# Feral: the surface language (lib/Feral.wiz), docs/stages/22-numbers.md, 22j

* every program of `drafts/feral/surface` lowers to Wiz that checks, and its `#eval`s give
  what its hand-lowered counterpart in `drafts/feral/lowered` gives;
* every program of `drafts/feral/rejected/surface` is rejected **both ways**: by the front
  end's region-carrying checker, at the Feral source line with the rustc error class its
  header names, and by the kernel on the lowering of the same program (`#unchecked
  feral`). A disagreement between the two verdicts is a failure.
-/

namespace Tests.Feral

/-- `lib/` plus the runtime stand-ins of `drafts/feral/lib`. -/
def loader : IO (Name → Option String) := do
  let lib ← Tests.Elab.libLoader
  let core ← IO.FS.readFile "drafts/feral/lib/FeralCore.wiz"
  pure fun n => if n == "FeralCore" then some core else lib n

def frontend (src : String) : IO (CommandState ZeroOneMany) := do
  pure (runFrontend (R := ZeroOneMany) src { trustedModule := Tests.libModule, loader := ← loader })

def errorsOf (s : CommandState ZeroOneMany) (src : String) : List String :=
  (s.messages.filter (·.severity == .error)).toList.map (·.render src)

def infosOf (s : CommandState ZeroOneMany) : List String :=
  (s.messages.filter (·.severity == .info)).toList.map (·.text)

def has (s frag : String) : Bool := (s.splitOn frag).length > 1

/-- A surface program is accepted (the front end and then the kernel on what it lowers
to), and every `#eval` of it is one of the results of the hand-lowered program. -/
def accepted (name : String) : IO Unit := do
  let src ← IO.FS.readFile s!"drafts/feral/surface/{name}.wiz"
  let s ← frontend src
  let errs := errorsOf s src
  unless errs.isEmpty do throw (IO.userError s!"the surface program is not accepted:\n{"\n".intercalate errs}")
  let got := infosOf s
  check (!got.isEmpty) "the surface program evaluates nothing"
  let hand ← IO.FS.readFile s!"drafts/feral/lowered/{name}.wiz"
  let h ← frontend hand
  let herrs := errorsOf h hand
  unless herrs.isEmpty do throw (IO.userError s!"the hand-lowered program does not check:\n{"\n".intercalate herrs}")
  let want := infosOf h
  for g in got do
    unless want.contains g do
      throw (IO.userError s!"the surface program gives {g}, which the hand-lowered one does not ({want})")

/-- The `-- expect: FRAGMENT at LINE` line of a rejected program. -/
def expectation (src : String) : IO (String × Nat) := do
  let some l := (src.splitOn "\n").find? (has · "-- expect: ") | throw (IO.userError "no `-- expect:` line")
  match ((l.splitOn "-- expect: ")[1]!).splitOn " at " with
  | [frag, line] => pure (frag, line.trimAscii.toString.toNat!)
  | _ => throw (IO.userError s!"malformed expectation: {l}")

/-- A rejected program, both ways. -/
def rejected (name : String) : IO Unit := do
  let src ← IO.FS.readFile s!"drafts/feral/rejected/surface/{name}.wiz"
  let (frag, line) ← expectation src
  -- the front end's verdict, at the Feral source
  let s ← frontend src
  let errs := errorsOf s src
  check (!errs.isEmpty) "the front end accepts a program that must be rejected"
  check (errs.all (!has · "generated source")) s!"the front end missed it (the kernel rejected the lowering):\n{errs}"
  let first := errs.head!
  check (has first frag) s!"the error does not name `{frag}`:\n{first}"
  check (first.startsWith s!"{line}:") s!"the error is not at line {line}:\n{first}"
  -- the kernel's verdict, on the lowering of the same program
  let un := src.replace "\nferal\n" "\n#unchecked feral\n"
  check (un != src) "no `feral` block to lower unchecked"
  let u ← frontend un
  let uerrs := errorsOf u un
  check ((infosOf u).any (has · frag)) s!"#unchecked does not report the front end's verdict ({frag}): {infosOf u}"
  check (uerrs.any (has · "the generated source was rejected"))
    s!"the two verdicts differ: the front end rejects the program, the kernel accepts its lowering ({uerrs})"
  -- and the hand-written lowering of drafts/feral/rejected is still rejected
  let hand ← IO.FS.readFile s!"drafts/feral/rejected/{name}.wiz"
  let h ← frontend hand
  check (!(errorsOf h hand).isEmpty) "the hand-lowered program is accepted"

def firstError (src : String) : IO String := do
  let s ← frontend src
  match errorsOf s src with
  | e :: _ => pure e
  | [] => throw (IO.userError "accepted, but an error was expected")

def pre : String := "import FeralCore\nimport Feral\n"

def surfaceNames : List String :=
  ["01_swap", "02_push", "03_get_mut", "04_reverse", "05_bst", "06_count", "07_disjoint", "08_first_mut",
   "09_bsearch", "10_regions", "11_list", "12_pick"]

def rejectedNames : List String :=
  ["E0499_two_mut", "E0502_use_while_mut", "E0515_return_local", "E0515_return_mut", "E0597_not_long_enough",
   "E0597_store_short", "lifetime_bound_missing", "lifetime_bound_missing_mut", "outlives_wrong_way"]

def group : Group where
  name := "feral"
  exercise := "lib/Feral.wiz (the Feral surface language)"
  cases :=
    surfaceNames.map (fun n => { name := s!"surface/{n} lowers, checks, and behaves like lowered/{n}", run := fun _ => accepted n }) ++
    rejectedNames.map (fun n => { name := s!"rejected/{n}: rejected by the front end and by the kernel", run := fun _ => rejected n }) ++ [
    { name := "every program of drafts/feral/surface and rejected/surface is tested", run := fun _ => do
        let listed (dir : String) : IO (List String) := do
          let es ← System.FilePath.readDir dir
          pure ((es.toList.filter (·.path.extension == some "wiz")).map (·.path.fileStem.getD "")).mergeSort
        checkEq (toString surfaceNames.mergeSort) (toString (← listed "drafts/feral/surface"))
        checkEq (toString rejectedNames.mergeSort) (toString (← listed "drafts/feral/rejected/surface")) },
    { name := "hand-written Wiz against lib/Region.wiz: a forged handle and a lengthened borrow are rejected", run := fun _ => do
        for n in ["forge_handle", "lengthen_borrow"] do
          let src ← IO.FS.readFile s!"drafts/feral/rejected/{n}.wiz"
          check (!(errorsOf (← frontend src) src).isEmpty) s!"{n} is accepted" },
    { name := "examples/resources.wiz: Feral's swap on heap cells, verified with the x-tactics through lib/HeapBorrow.wiz", run := fun _ => do
        let src ← IO.FS.readFile "examples/resources.wiz"
        let s ← frontend src
        checkEq "[]" (toString (errorsOf s src))
        checkEq ("[.ok (2, 1), .some ((), .cons .none (.cons (.some (20, ())) (.cons (.some (10, ())) " ++
          "(.cons (.some (30, ())) .nil))))]") (toString (infosOf s))
        -- the heap specification of the identity is not one of swap's
        let bad := src ++ "\ndef bad (p q : Nat) (a b : U64) :\n" ++
          "    Triple ((p ↦ a) ⋆ (q ↦ b)) (swapCells p q) (fun _ => (p ↦ a) ⋆ (q ↦ b)) := by\n" ++
          "  xgo\n"
        let e ← firstError bad
        check (((e.splitOn ":")[0]!).toNat! > 69) s!"the error is not in the added definition: {e}" },
    { name := "#lower shows the generated Wiz, item by item", run := fun _ => do
        let src := pre ++ "#lower feral\n  fn swap {'a 'b} (x : &'a mut U64) (y : &'b mut U64) : Unit := {\n" ++
          "    let t := *x;\n    *x := *y;\n    *y := t\n  }\nend\n"
        let s ← frontend src
        checkEq "[]" (toString (errorsOf s src))
        checkEq ("[def swap {ρa ρb : Region} (x : (Uniq ρa U64)) (y : (Uniq ρb U64)) : Result (Unit × ((Uniq ρa U64) × (Uniq ρb U64))) :=\n" ++
          "  let t := x.val;\n  let x := (Uniq.set x y.val);\n  let y := (Uniq.set y t);\n  Result.ok ((), (x, y))\n]") (toString (infosOf s)) },
    { name := "errors point into the block: the line and column of the offending expression", run := fun _ => do
        let e ← firstError (pre ++ "feral\n  fn f (x : U64) : U64 := {\n    let y := x;\n    y := 3;\n    y\n  }\nend\n")
        check (e.startsWith "6:5: " && has e "E0384") e
        let e ← firstError (pre ++ "feral\n  fn f (x : U64) : Bool :=\n    x + 1\nend\n")
        check (e.startsWith "5:5: " && has e "type mismatch: expected Bool, found U64") e
        let e ← firstError (pre ++ "feral\n  fn f (x : U64) : U64 := g x\nend\n")
        check (has e "unknown identifier `g`") e },
    { name := "the lender is unusable while a named borrow of it lives (E0499, E0502, E0506)", run := fun _ => do
        let body (stmts : String) := pre ++ "feral\n  fn f () : U64 := {\n    let mut v := Vec.new;\n    let r := &mut v;\n" ++ stmts ++ "    r.push 2;\n    0\n  }\nend\n"
        let e ← firstError (body "    v.push 1;\n")
        check (e.startsWith "7:" && has e "E0499") e
        let e ← firstError (body "    let n := v.len;\n")
        check (e.startsWith "7:" && has e "E0502") e
        let e ← firstError (body "    v := Vec.new;\n")
        check (e.startsWith "7:" && has e "E0506") e
        -- and after the borrow's last use the lender is back
        let ok := pre ++ "feral\n  fn f () : U64 := {\n    let mut v := Vec.new;\n    let r := &mut v;\n    r.push 2;\n    v.push 1;\n    v.len\n  }\nend\n" ++
          "#eval Result.map U64.toNat f\n"
        let s ← frontend ok
        checkEq "[]" (toString (errorsOf s ok))
        checkEq "[.ok 2]" (toString (infosOf s)) },
    { name := "a shared borrow: the lender can be read, not mutated, while it lives (E0502)", run := fun _ => do
        let body (stmts : String) := pre ++ "feral\n  fn f () : U64 := {\n    let mut a : U64 := 1;\n    let r := &a;\n" ++ stmts ++ "    *r + a\n  }\nend\n"
        let ok := body "" ++ "#eval Result.map U64.toNat f\n"
        let s ← frontend ok
        checkEq "[]" (toString (errorsOf s ok))
        checkEq "[.ok 2]" (toString (infosOf s))
        let e ← firstError (body "    let w := &mut a;\n")
        check (e.startsWith "7:" && has e "E0502") e },
    { name := "KNOWN GAP: one local mutably borrowed twice in a call is rejected by the front end only", run := fun _ => do
        -- The front end reports E0499. Lowered anyway (#unchecked), the program uses one
        -- handle twice, which the kernel accepts today: handles are ω values, aliasing is
        -- enforced by the shape of the lowering (LOWERING.md, L21; wishful: linear-case).
        -- Closed by stage 2 of /workspace/wiz-notes/linear-case-design.md (linear constructor
        -- fields, handles at quantity 1): this case must then start failing; flip it. Note D8
        -- there: with exact linearity the error alternatives must hand the handle back, so
        -- the types of lib/Region.wiz's scopes (and what L5 emits for `.err`) will change.
        let src := pre ++ "feral\n  fn swap {'a 'b} (x : &'a mut U64) (y : &'b mut U64) : Unit := {\n    let t := *x;\n    *x := *y;\n    *y := t\n  }\n" ++
          "  fn bad () : U64 := {\n    let mut a : U64 := 1;\n    swap (&mut a) (&mut a);\n    a\n  }\nend\n"
        let e ← firstError src
        check (e.startsWith "11:" && has e "E0499") e
        let un := src.replace "\nferal\n" "\n#unchecked feral\n"
        let u ← frontend un
        checkEq "[]" (toString (errorsOf u un))
        check ((infosOf u).any (has · "E0499")) "no verdict from the front end" },
    { name := "command macros: errors, info and generated source at a node of the input (Syntax.errorAt …)", run := fun _ => do
        let src := "import Prelude\nsyntax (name := three) \"three!\" ident ident ident : command\n" ++
          "def threeMacro : CommandMacro := fun stx => MacroM.pure (.cons (Syntax.errorAt (.cons 2 .nil) \"second\")\n" ++
          "  (.cons (Syntax.infoAt (.cons 3 .nil) \"third\") (.cons (Syntax.sourceAt (.cons 1 .nil) \"def one : Nat := 1\\ndef uno : Nat := one\") .nil)))\n" ++
          "attribute [macro command.three] threeMacro\nthree! a\n  b\n  c\n#eval uno\n"
        let s ← frontend src
        checkEq "[7:3: error: second, 8:3: info: third, 9:1: info: 1]" (toString (s.messages.toList.map (·.render src)))
        -- generated source that does not check is reported at the node, with the text
        let bad := src.replace "def one : Nat := 1" "def one : Nat := zzz"
        let b ← frontend bad
        check ((errorsOf b bad).any (fun e => e.startsWith "6:8: " && has e "the generated source was rejected")) (toString (errorsOf b bad)) }
  ]

def groups : List Group :=
  group ::
  []

end Tests.Feral
