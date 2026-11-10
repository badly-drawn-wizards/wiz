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
def introFresh := 25
def rename := 26
def change := 27
def whnf := 28
def unfold := 29
def rewrite := 30
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

/-! ## Names for introduced variables

A tactic that introduces a variable without being given a name takes the binder's
(`intro` on `(n : Nat) → …` gives `n`). The name is then made **fresh**: either
accessible, with the first free numeric suffix (`n`, `n1`, `n2`, …), or
**inaccessible**, marked with `✝` (`n✝`, `n✝1`, …), which is not an identifier
character: the user cannot refer to it by accident, and a proof cannot come to depend
on a generated name. `rename_i` gives inaccessible names a real one. -/

/-- The mark of an inaccessible name. -/
def inaccessibleMark : String := "✝"

def Name.isInaccessible (x : Name) : Bool := (x.splitOn inaccessibleMark).length > 1

/-- The name for a variable introduced from a binder `binder`, given the names in scope:
`hint` if it is not empty, else the binder's name, else `h` for a proof and `x` for
anything else; then made fresh (see above). -/
def introName (taken : List Name) (hint binder : Name) (isProof inaccessible : Bool) : Name :=
  let binder := (binder.splitOn inaccessibleMark).headD ""
  let base := if !hint.isEmpty then hint
    else if !binder.isEmpty && binder != "_" then binder
    else if isProof then "h" else "x"
  let base := if inaccessible then base ++ inaccessibleMark else base
  if !taken.contains base then base else
  match (List.range (taken.length + 1)).find? fun i => !taken.contains s!"{base}{i + 1}" with
  | some i => s!"{base}{i + 1}"
  | none => base

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

/-! ## Unfolding (stage 6f)

`normalize` evaluates and quotes, but definitions are glued (`Val.unfold` keeps the
name), so it never shows what a definition unfolds to. Two requests do:

* `unfold n e` replaces every application of the constant `n` in `e` by its unfolding,
  **once**: the definition's body with the arguments in place and the `match` on them
  computed, but the definitions it mentions still folded.
* `whnf e` unfolds the head of `e` until it is not a definition (a constructor, a
  binder, a variable, …).

A structurally recursive definition is an eliminator, so what unfolding leaves for its
recursive calls is a raw `ind … L n`, which nobody wrote. `foldRec` finds these stuck
eliminators and folds each back into `f a₁ … aₙ` when that unifies with it (for the `f`s
that were unfolded): the user sees `MList L n` again. The result is only ever a
*candidate*: the elaborator checks it against what it replaces by conversion
(`change`), and the kernel checks the finished proof. -/

private def stripLams : Term R → Nat × Term R
  | .lam _ b => let (n, t) := stripLams b; (n + 1, t)
  | t => (0, t)

/-- `ctx` under `k` more binders (of types the caller doesn't know or need). -/
def bindAnon (ctx : LocalCtx R) : Nat → LocalCtx R
  | 0 => ctx
  | k + 1 => bindAnon (ctx.bind "x" (.unit .zero)) k

/-- `t` as an application of the definition `n`, if `n ?a₁ … ?aₖ` (`k` its number of
`fun`s) unifies with it and that solves every `?aᵢ`. -/
def foldAs? (ctx : LocalCtx R) (n : Name) (t : Term R) : ElabM R (Option (Term R)) := do
  let some d := (← getGlobals).find? n | return none
  let some v := d.value | return none
  let arity := (stripLams v).1
  if arity == 0 then return none
  try
    let us ← d.levelParams.mapM fun _ => freshLevelMeta
    let mut cand : Term R := .const n us
    for _ in [0:arity] do cand := .app cand (← freshMeta ctx "fold")
    let cv ← evalIn ctx cand
    let tv ← force (← evalIn ctx t)
    -- `n ?a₁ … ?aₖ` is itself stuck, on the hole it recurses on: `?aᵢ` followed by the
    -- eliminator and the rest. That is no pattern for the unifier, so first solve the
    -- hole with what `t`'s eliminator is stuck on (once per nested `match`)
    for _ in [0:arity] do
      match ← force cv, tv with
      | .neutral (.mvar a) sp, .neutral h' sp' =>
        let some j := sp.findIdx? (fun e => !(e matches .app _)) | break
        let rest := sp.size - j
        if sp'.size < rest then throwAt {} "no match"
        unify ctx.lvl (.neutral (.mvar a) (sp.extract 0 j)) (.neutral h' (sp'.extract 0 (sp'.size - rest)))
      | _, _ => break
    unify ctx.lvl cv tv
    let t' ← zonk ctx.lvl cand
    if t'.mvars.isEmpty then return some t'
    throwAt {} "not determined"
  catch _ => return none

/-- Fold the stuck eliminators in `t` back into applications of the definitions `names`
(see above). An eliminator applied to more arguments than the definition takes, or to
fewer, is tried at each prefix of its arguments. -/
partial def foldRec (ctx : LocalCtx R) (names : List Name) (t : Term R) : ElabM R (Term R) := do
  if names.isEmpty then return t
  if (Term.spine t).1 matches .ind .. then
    for n in names do
      if let some t' ← foldAs? ctx n t then return t'
  t.mapChildrenM pure fun k c => foldRec (bindAnon ctx k) names c

/-- Is `n` an eliminator of an inductive type (`T.rec`, `T.casesOn`, …)? A definition by
cases or by structural recursion is `fun x => T.rec … x`: unfolding it means unfolding the recursor too (which
is where the `match` computes), and nobody wants a recursive call folded into `T.rec`. -/
def isRecursor (g : Globals R) (n : Name) : Bool :=
  match (n.splitOn ".").reverse with
  | e :: rest => ["rec", "recN", "casesOn", "casesOnN", "scasesOn", "scasesOnN"].contains e &&
      !rest.isEmpty && g.contains (".".intercalate rest.reverse ++ ".desc")
  | _ => false

/-- Unfold the recursors at the head of a value. -/
partial def forceRecursors (v : Val R) : ElabM R (Val R) := do
  match ← forceMeta v with
  | .unfold n us sp w => if isRecursor (← getGlobals) n then forceRecursors w.get else pure (.unfold n us sp w)
  | v => pure v

/-- Unfold the head of a value until it is not a definition; also the definitions
unfolded on the way, innermost last. -/
partial def forceNames (v : Val R) (names : List Name := []) : ElabM R (Val R × List Name) := do
  match ← forceMeta v with
  | .unfold n _ _ v =>
    forceNames v.get (if names.contains n || isRecursor (← getGlobals) n then names else names ++ [n])
  | .lazyInd _ _ _ _ _ _ _ _ _ v => forceNames v.get names
  | v => pure (v, names)

/-- The weak head normal form of `t`, with recursive calls folded back. -/
def whnfTerm (ctx : LocalCtx R) (t : Term R) : ElabM R (Term R) := do
  let (v, names) ← forceNames (← evalIn ctx t)
  foldRec ctx names.reverse (← zonk ctx.lvl (quote (← getGlobals) ctx.lvl v))

/-- `t` with every application of the definition `n` unfolded once (innermost first). -/
partial def unfoldIn (ctx : LocalCtx R) (n : Name) (t : Term R) : ElabM R (Term R) := do
  let inside (t : Term R) := t.mapChildrenM pure fun k c => unfoldIn (bindAnon ctx k) n c
  match t with
  | .app .. | .const .. =>
    -- the whole application at once: `f a` in `f a b` is not an occurrence of its own
    let (h, args) := Term.spine t
    let args ← args.mapM (unfoldIn ctx n)
    match h with
    | .const m _ =>
      let t' := args.foldl .app h
      if m != n then return t'
      match ← forceMeta (← evalIn ctx t') with
      | .unfold _ _ _ v =>
        foldRec ctx [n] (← zonk ctx.lvl (quote (← getGlobals) ctx.lvl (← forceRecursors v.get)))
      | _ => pure t'
    | h => return args.foldl .app (← inside h)
  | t => inside t

/-! ## Rewriting with an equation

`rewrite h` for `h : a = b` replaces the occurrences of `a` in the goal `G[a]` by `b`:
the new goal is `G[b]`, and the old one is solved by a cast along `G[b] = G[a]`, which
`transp` gets from `h` (as `Eq.substBack` in the prelude does). Occurrences are found
syntactically, on the normal forms the elaborator prints; the kernel checks the cast. -/

/-- `t` (under `depth` binders more than `a`) with the occurrences of `a` replaced by
the variable `depth`, the other variables making room for it; and whether there were any. -/
partial def abstractOcc (a : Term R) (t : Term R) (depth : Nat := 0) : StateM Bool (Term R) := do
  if t == a.lift depth then
    set true
    return .var depth
  match t with
  | .var i => pure (.var (if i ≥ depth then i + 1 else i))
  | t => t.mapChildrenM pure fun k c => abstractOcc a c (depth + k)

end Wiz.Elab
