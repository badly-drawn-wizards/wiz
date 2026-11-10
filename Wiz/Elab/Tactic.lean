import Wiz.Elab.ProcMacro
import Wiz.Elab.Zonk

/-!
# Tactics: the host side

A tactic is a Wiz function `Syntax → TacticM Unit`, where (in the prelude)

    inductive Tac where | done | fail (msg : String) | getGoals (k : List Nat → Tac) | …
    def TacticM (A : Type) : Type := (A → Tac) → Tac

So running a tactic produces a `Tac` value: a **request** to the elaborator together
with a continuation for the answer (a free monad, in continuation-passing style).
The elaborator interprets the requests one by one (`runTac`, in `Elab/Term.lean`,
since `exact` needs the term elaborator) and applies the continuation to the
answer, encoded as a runtime value. Tactic code itself stays pure.

**Goals** are numbered: `TacState.goals` holds every goal made so far, each a hole
(a metavariable applied to its context's variables) with a context and a type.
`TacState.open` is the current goal list, which tactics read and replace.

**Terms** are reflected as the prelude's `Expr`: variables (de Bruijn indices in the
goal's context), constants, closed sorts, Π (with binder info and quantity), λ,
application, and numerals. Every other kernel form becomes an `opaque` handle into
`TacState.handles`, remembering how many variables were in scope where it was made;
when it is used deeper inside binders, it is lifted. Nominal inductive types (`μ`
with a display hint) are reflected as their names applied to their arguments, so
tactics see `Vec A n`.
-/

namespace Wiz.Elab

variable {R : Type} [QRig R] [DecidableEq R] [QuantitySyntax R]

-- The constructor numbers of the prelude's `Tac`.
namespace TacTag
def done := 0
def result := 1
def fail := 2
def trace := 3
def fresh := 4
def getGoals := 5
def setGoals := 6
def goalType := 7
def goalExpr := 8
def goalHyps := 9
def intro := 10
def exact := 11
def elabInfer := 12
def assign := 13
def newGoal := 14
def normalize := 15
def instantiate := 16
def isDefEq := 17
def inferType := 18
def evalTactic := 19
def catch_ := 20
-- (HD8) reflection, for macros (`Elab/Reflect.lean`)
def getInductive := 21
def getType := 22
-- the tactic framework's requests (a block of their own in the prelude's `Tac`)
def ppGoal := 23
def ppExpr := 24
end TacTag

structure Goal (R : Type) where
  ctx : LocalCtx R
  ty : VTy R
  /-- the hole: a metavariable applied to the bound variables of `ctx` -/
  tm : Term R

structure TacState (R : Type) where
  goals : Array (Goal R) := #[]
  «open» : List Nat := []
  /-- opaque terms, with the number of variables in scope where they were reflected -/
  handles : Array (Term R × Nat) := #[]

/-! ## Encoding answers -/

def encodeNat (n : Nat) : RVal := .nat n
def encodeBool (b : Bool) : RVal := mkCon (if b then 1 else 0) []
def encodeList (xs : List RVal) : RVal := xs.foldr (fun x t => mkCon 1 [x, t]) (mkCon 0 [])
def encodePair (a b : RVal) : RVal := .obj 0 #[a, b]

/-- The elements of a runtime `List`. -/
partial def decodeList (v : RVal) : Option (List RVal) :=
  match v.tag? with
  | some 0 => some []
  | some 1 => do return v.conField 0 :: (← decodeList (v.conField 1))
  | _ => none

def decodeBool (v : RVal) : Option Bool := v.tag?.map (· == 1)

/-! ## Reflection -/

/-- **Exercise 6.4a.** Reflect a term (with `depth` variables in scope) as an `Expr`
value (constructors, in order: `var i`, `const n`, `sort u`, `pi x implicit q dom body`,
`lam x body`, `app f a`, `lit n`, `opaque id`; use `mkCon`, `encodeString`,
`encodeBool`). Levels are dropped from constants (`reify` makes fresh ones), a sort
is reflected only if its level is a numeral, and a `μ`/`ν` with a display hint
`(T, us, args)` becomes `T` applied to `args`. Anything else is `opaque`: push
`(t, depth)` onto the handles and use its index. -/
partial def reflect (t : Term R) (depth : Nat) : StateM (Array (Term R × Nat)) RVal := do
  --<sol
  match t with
  | .var i => pure (mkCon 0 [.nat i])
  | .const n _ => pure (mkCon 1 [encodeString n])
  | .sort l => match l.toNat? with
    | some n => pure (mkCon 2 [.nat n])
    | none => mkOpaque
  | .pi x bi q A B _ =>
    pure (mkCon 3 [encodeString x, encodeBool (bi == .implicit), ← reflect q depth, ← reflect A depth,
      ← reflect B (depth + 1)])
  | .lam x b => pure (mkCon 4 [encodeString x, ← reflect b (depth + 1)])
  | .app f a => pure (mkCon 5 [← reflect f depth, ← reflect a depth])
  | .natLit n => pure (mkCon 6 [.nat n])
  | .mu _ _ _ _ .szInf (some (T, _, args)) | .nu _ _ _ _ .szInf (some (T, _, args)) =>
    args.foldlM (fun acc a => do pure (mkCon 5 [acc, ← reflect a depth])) (mkCon 1 [encodeString T])
  | _ => mkOpaque
where
  mkOpaque : StateM (Array (Term R × Nat)) RVal := do
    let hs ← get
    set (hs.push (t, depth))
    pure (mkCon 7 [.nat hs.size])
  --|ex
  --| sorry
  --sol>

/-- **Exercise 6.4b.** The inverse of `reflect`, at `depth` variables in scope. A
constant gets fresh level metavariables for its universe parameters (it must exist).
An `opaque` handle made at depth `d` is lifted by `depth - d` (or strengthened, if
`depth < d`, failing if that is impossible). Binders take the rig's default quantity
only through `q`, which is reflected like any other term. -/
partial def reify (handles : Array (Term R × Nat)) (v : RVal) (depth : Nat) : ElabM R (Term R) := do
  --<sol
  let str (v : RVal) : ElabM R String := match v.toString? with
    | some s => pure s
    | none => throwAt {} "tactic: malformed string"
  let nat (v : RVal) : ElabM R Nat := match v.toNat? with
    | some n => pure n
    | none => throwAt {} "tactic: malformed number"
  match v.tag? with
  | some 0 => return .var (← nat (v.conField 0))
  | some 1 =>
    let n ← str (v.conField 0)
    let some d := (← getGlobals).find? n | throwAt {} s!"tactic: unknown constant {n}"
    return .const n (← d.levelParams.mapM fun _ => freshLevelMeta)
  | some 2 => return .sort (Level.ofNat (← nat (v.conField 0)))
  | some 3 =>
    let bi : BinderInfo := if decodeBool (v.conField 1) == some true then .implicit else .default
    return .pi (← str (v.conField 0)) bi (← reify handles (v.conField 2) depth)
      (← reify handles (v.conField 3) depth) (← reify handles (v.conField 4) (depth + 1)) none
  | some 4 => return .lam (← str (v.conField 0)) (← reify handles (v.conField 1) (depth + 1))
  | some 5 => return .app (← reify handles (v.conField 0) depth) (← reify handles (v.conField 1) depth)
  | some 6 => return .natLit (← nat (v.conField 0))
  | some 7 =>
    let some (t, d) := handles[← nat (v.conField 0)]? | throwAt {} "tactic: unknown handle"
    if depth ≥ d then return t.lift (depth - d)
    let some t' := (List.range (d - depth)).foldlM (fun t _ => t.strengthen? 0) t
      | throwAt {} "tactic: a term was used outside the binders it refers to"
    return t'
  | _ => throwAt {} "tactic: malformed Expr"
  --|ex
  --| sorry
  --sol>

/-! ## Goals -/

/-- The kernel context for a goal, for inferring the types of complete terms. -/
def Goal.kernelCtx (gl : Goal R) (g : Globals R) : Ctx R :=
  { globals := g, env := gl.ctx.env, names := gl.ctx.names,
    qtys := gl.ctx.names.map fun _ => QPoly.const QuantitySyntax.explicitDefault,
    types := gl.ctx.types, lvl := gl.ctx.lvl, erased := true }

/-- Is the goal's hole still unsolved? -/
def Goal.isOpen (gl : Goal R) : ElabM R Bool := do
  let t ← zonk gl.ctx.lvl gl.tm
  pure !(t.mvars.isEmpty)

/-- Show a goal: its hypotheses, then `⊢ type`. -/
def Goal.show (gl : Goal R) : ElabM R String := do
  let mut lines : Array String := #[]
  let ctx := gl.ctx
  for i in [0:ctx.lvl] do
    let j := ctx.lvl - 1 - i
    -- the type of the `j`th local lives in the context below it
    let k := j + 1
    let sub : LocalCtx R :=
      { ctx with env := ctx.env.drop k, names := ctx.names.drop k, types := ctx.types.drop k,
                 bound := ctx.bound.drop k, lvl := ctx.lvl - k }
    lines := lines.push s!"{ctx.names[j]!} : {showTerm sub (← zonk sub.lvl (quote (← getGlobals) sub.lvl ctx.types[j]!))}"
  lines := lines.push s!"⊢ {showTerm ctx (← zonk ctx.lvl (quote (← getGlobals) ctx.lvl gl.ty))}"
  pure ("\n".intercalate lines.toList)

end Wiz.Elab
