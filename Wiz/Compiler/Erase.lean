import Wiz.Core.Check

/-!
# Erasure

Stage 5 starts compilation. A kernel-checked term is turned into an **untyped**
program (`ETerm`) by erasing everything with no runtime content:

* types (anything whose type is a `Sort`), proofs (anything whose type is a `Prop`),
  sizes, quantities, and universe levels all become `◾` (`ETerm.erased`);
* arguments to, and `let`s of, quantity `0` become `◾`. QTT guarantees an erased
  variable is never needed at runtime, so this is the payoff of stage 1.

Binders are kept (an erased argument is passed as `◾`), so de Bruijn indices don't
change. A later pass can drop them.

**Data representation.** The payload of a value of `μ D i` is nested pairs
`(tag, f₁, …, fₙ, e, ())`. At runtime it is **flat**: one object `⟨tag f₁ … fₙ⟩`, with
the constructor's tag as the object's tag (or `⟨0 f₁ … fₙ⟩` if the description doesn't
start with a choice of tag), and `◾` in the places of erased fields. Numbers of the
registered `nat` type stay numbers. A constructor applied to its fields becomes the
object directly; case analysis reads the fields directly (`resolveViews`). Code that
handles payloads generically (`ind` with hypotheses) converts with the primitives
`pack` and `unpack`, which walk the description.

The generic eliminators (`ind`, `Desc.elim`, the `map` behind coiteration) become
runtime **primitives** that walk the description, which is itself an ordinary runtime
value. A description whose first argument is a tag, `Desc.arg (Enum ls) F`, is marked:
`⟨4 ◾ F⟩` instead of `⟨1 ◾ F⟩`, so that `pack` knows to use the tag. For a number,
`ind` and the conversions get the description wrapped as `⟨5 D⟩`.

Erasure is **type-directed**, so it is bidirectional like the kernel: `eraseCheck`
knows the expected type, `eraseInfer` computes it with the kernel's `infer`.
-/

namespace Wiz

/-- Runtime primitives: the generic eliminators, interpreted by walking descriptions. -/
inductive Prim where
  /-- `ind D m i x` -/
  | ind
  /-- `delim mret marg mrec mhrec D` -/
  | delim
  /-- `coit D step i s` -/
  | coit
  /-- `scofix f i a` -/
  | scofix
  /-- `out x` -/
  | out
  /-- reached an absurd case -/
  | unreachable
  /-- `0` for an observed coinductive value, `1` for a `coit`, `2` for an `scofix`, `3`
  for a lazy cell already observed (the backend's `out` is written with it) -/
  | lazyTag
  /-- `lazySet x p`: `p`, after overwriting the lazy cell `x` with its payload `p`, so
  that `out` is memoised (the backend's `out`; the interpreter just returns `p`) -/
  | lazySet
  /-- `pack D x`: a payload of nested pairs as a flat object (see below) -/
  | pack
  /-- `unpack D v`: a flat object as its payload of nested pairs -/
  | unpack
  /-- `view D x`: the payload of `x`, seen through projections (removed by `resolveViews`) -/
  | view (absorbed nat : Bool)
  /-- the tag of an object, as a 0-field object -/
  | tag
  /-- the tag (`0` zero, `1` successor) and the field of a number -/
  | natTag
  | natPred
  | natSucc
  /-- `fieldAt v n`: field `n` (a runtime number) of an object -/
  | fieldAt
  /-- `mkObj t fs`: an object with the tag of `t` and the fields listed by `fs`
  (nested pairs ending in `◾`) -/
  | mkObj
  deriving Repr, BEq, Inhabited

inductive ETerm where
  | erased
  | var (ix : Nat)
  | global (name : Name)
  | lam (x : Name) (body : ETerm)
  | app (f a : ETerm)
  | letE (x : Name) (val body : ETerm)
  /-- an object with a tag and fields: pairs are `obj 0 #[a, b]`, tags `obj i #[]` -/
  | obj (tag : Nat) (fields : Array ETerm)
  | proj (i : Nat) (t : ETerm)
  /-- branch on the tag of an object -/
  | case (scrut : ETerm) (branches : Array ETerm)
  /-- `fix x. body`: general recursion (termination was checked by the kernel) -/
  | fix (x : Name) (body : ETerm)
  | prim (op : Prim) (args : Array ETerm)
  /-- a numeral, a native number at runtime -/
  | natLit (n : Nat)
  deriving Repr, Inhabited

namespace ETerm

/-- Shift free variables (`≥ cut`) up by `k`. -/
partial def lift (k : Nat) (cut : Nat := 0) : ETerm → ETerm
  | var i => if i ≥ cut then var (i + k) else var i
  | lam x b => lam x (lift k (cut + 1) b)
  | app f a => app (lift k cut f) (lift k cut a)
  | letE x v b => letE x (lift k cut v) (lift k (cut + 1) b)
  | obj t fs => obj t (fs.map (lift k cut))
  | proj i t => proj i (lift k cut t)
  | case s bs => case (lift k cut s) (bs.map (lift k cut))
  | fix x b => fix x (lift k (cut + 1) b)
  | prim op as => prim op (as.map (lift k cut))
  | t => t

def apps (f : ETerm) (as : List ETerm) : ETerm := as.foldl app f

partial def toString : ETerm → String
  | erased => "◾"
  | var i => s!"#{i}"
  | global n => n
  | lam x b => s!"(λ{x}. {toString b})"
  | app f a => s!"({toString f} {toString a})"
  | letE x v b => s!"(let {x} := {toString v}; {toString b})"
  | obj t fs => s!"⟨{t}{String.join (fs.toList.map (" " ++ toString ·))}⟩"
  | proj i t => s!"{toString t}.{i}"
  | case s bs => s!"(case {toString s} [{", ".intercalate (bs.toList.map toString)}])"
  | fix x b => s!"(fix {x}. {toString b})"
  | prim op as => s!"({reprStr op}{String.join (as.toList.map (" " ++ toString ·))})"
  | natLit n => s!"{n}"

instance : ToString ETerm := ⟨toString⟩

end ETerm

variable {R : Type} [QRig R] [DecidableEq R] [ToString R] [QuantitySyntax R]

/-- Values of this type have no runtime content: types, proofs, sizes, quantities, phantom
tails. -/
def erasable (ctx : Ctx R) (ty : VTy R) : Bool :=
  match whnf ty with
  | .sort _ | .size | .sizeLt _ | .qty => true
  -- a phantom tail `(0 phantom✝ : D) → … → Unit` (only `fun _ => ()` inhabits it)
  | .pi x .. => x == phantomName || isProp ctx.globals ctx.tys ty
  | _ => isProp ctx.globals ctx.tys ty

private def isZeroQ (q : Val R) : Bool := q.toPoly? == some []

/-- A call of a generated `T.casesOn`, unfolded and beta-reduced: as a function, its
arguments (the branches) would all be computed before the call; unfolded, they sit in
the branches of a `case` and only the one taken runs. -/
def unfoldCases? (g : Globals R) (t : Term R) : Option (Term R) := do
  let (.const n us, args) := t.spine | none
  unless n.endsWith ".casesOn" do none
  let d ← g.find? n
  let v ← d.value
  -- the arguments are annotated with their types, so that the kernel can still infer
  -- the places they end up in (the motive applied, a branch under a cast)
  let rec beta : Term R → Term R → List (Term R) → Option (Term R)
    | .lam _ b, .pi _ _ _ A B _, a :: as =>
      let a' := if a matches .var _ | .const .. | .ann .. then a else .ann a A
      beta (b.instantiateAt 0 a') (B.instantiateAt 0 a') as
    | _, _, _ :: _ => none
    | b, _, [] => some b
  -- only when every binder gets an argument
  let rec arity : Term R → Nat
    | .lam _ b => arity b + 1
    | _ => 0
  let v := v.instLevels d.levelParams us
  let k := arity v
  if args.length < k then none
  let b ← beta v (d.type.instLevels d.levelParams us) (args.take k)
  pure ((args.drop k).foldl .app b)

/-- Is `ty` (a `μ`) the registered `nat` type? Its values are numbers at runtime. -/
def isNatTy (g : Globals R) (ty : Val R) : Bool :=
  match whnf ty with
  | .mu _ _ _ _ _ (some (T, _, _)) => g.builtins.lookup "nat" == some T
  | _ => false

/-- Does a description start with a choice of tag, `Desc.arg (Enum ls) F`? Then the
tag is the flat object's tag. -/
def startsWithTag (D : Val R) : Bool :=
  match whnf D with
  | .darg _ S _ => (whnf S matches .enum _)
  | _ => false

private def stripAnn : Term R → Term R
  | .ann t _ => stripAnn t
  | t => t

/-- The fields of a literal payload: the term `x` and its erasure `x'` walked along the
description `d` (one field per `arg`, `rec` and `hrec`, up to the `ret`). -/
partial def flatFields (g : Globals R) (ctx : Ctx R) (d : Val R) (x : Term R) (x' : ETerm) :
    Option (Array ETerm) :=
  match whnf d with
  | .dret _ => some #[]
  | .darg _ _ F => match stripAnn x, x' with
    | .pair a r, .obj 0 #[a', r'] => (flatFields g ctx (vApp g F (ctx.eval a)) r r').map (#[a'] ++ ·)
    | _, _ => none
  | .drec _ _ D' | .dhrec _ _ _ D' => match stripAnn x, x' with
    | .pair _ r, .obj 0 #[a', r'] => (flatFields g ctx D' r r').map (#[a'] ++ ·)
    | _, _ => none
  | _ => none

/-- A literal payload as a flat object: its tag and fields. -/
def flatCon (g : Globals R) (ctx : Ctx R) (D : Val R) (x : Term R) (x' : ETerm) : Option (Nat × Array ETerm) :=
  if startsWithTag D then
    match whnf D, stripAnn x, x' with
    | .darg _ _ F, .pair a r, .obj 0 #[.obj k #[], r'] => (flatFields g ctx (vApp g F (ctx.eval a)) r r').map (k, ·)
    | _, _, _ => none
  else (flatFields g ctx D x x').map (0, ·)

/-- A use of a value's payload: `view D x` as an argument (see `resolveViews`). -/
def viewOf (g : Globals R) (D : Val R) (xty : Val R) (D' x' : ETerm) : ETerm :=
  let nat := isNatTy g xty
  .prim (.view (startsWithTag D) nat) #[if nat then .obj 5 #[D'] else D', x']

mutual

/-- The free variables of a term (as indices at its top). -/
partial def Wiz.IR.freeIdx' (t : Term R) (depth : Nat := 0) (acc : Std.HashSet Nat := {}) : Std.HashSet Nat :=
  match t with
  | .var i => if i ≥ depth then acc.insert (i - depth) else acc
  | t => Id.run do
    let mut acc := acc
    let ((), acc') := (t.forChildren (m := StateM (Std.HashSet Nat)) (fun _ => pure ())
      (fun d c => modify fun a => Wiz.IR.freeIdx' c (depth + d) a)).run acc
    acc := acc'
    pure acc

/-- The type of a term that is already known to be well typed, without checking it
again: along an elimination spine only (heads, applications, projections, annotations,
`ecase`, `ind`), else by the kernel's `infer`. Erasure asks for the type of every
subterm, so a full `infer` at each would re-check each subterm once per enclosing node:
quadratic in the nesting depth of the deep `casesOn` trees that `match` produces. -/
partial def quickType (ctx : Ctx R) (t : Term R) : TCM (VTy R) := do
  let g := ctx.globals
  match t with
  | .var ix => pure ctx.types[ix]!
  | .const n us => match g.find? n with
    | some d => pure (Wiz.eval g [] (d.type.instLevels d.levelParams us))
    | none => throw (.unboundGlobal n)
  | .app f a => match whnf (← quickType ctx f) with
    | .pi _ _ _ _ cod _ => pure (Closure.inst g cod (ctx.eval a))
    | _ => return (← infer ctx t).1
  | .fst p => match whnf (← quickType ctx p) with
    | .sigma _ _ A _ _ => pure A
    | _ => return (← infer ctx t).1
  | .snd p => match whnf (← quickType ctx p) with
    | .sigma _ _ _ B _ => pure (Closure.inst g B (vFst (ctx.eval p)))
    | _ => return (← infer ctx t).1
  | .ann _ ty => pure (ctx.eval ty)
  | .ecase _ m s _ => pure (Closure.inst g (.mk ctx.env m) (ctx.eval s))
  | .ind _ _ _ _ P _ i x => pure (vApp g (vApp g (ctx.eval P) (ctx.eval i)) (ctx.eval x))
  | _ => return (← infer ctx t).1

/-- **Exercise 5.1a.** Erase `t`, checking it against `ty`.

* if `ty` is `erasable`, the result is `◾`;
* `lam` against a Π: erase the body under the binder;
* `pair` against a Σ: an object `obj 0 #[a, b]`, with `a` erased if the Σ's quantity
  is `0`;
* `con x` against `μ D i`: erase the payload `x` against `⟦D⟧ (μ D) i`, then make it
  flat: `flatCon` gives the tag and fields of a literal payload (`obj k fs`; for the
  `nat` type, `natLit 0` or the successor applied to the field); otherwise
  `prim .pack #[D', x']` (with `D'` wrapped as `obj 5 #[D']` for `nat`);
* `cocon x` against `ν`: just the erased payload;
* `dret`/`darg`/`drec`/`dhrec` against `Desc I`: descriptions are runtime data, as
  `obj 0 #[i]`, `obj 1 #[◾, D]` (`obj 4 #[◾, D]` if `S` is an `Enum`), `obj 2 #[j, D]`
  and `obj 3 #[◾, j, D]`;
* `tt` is `◾`; `letE` keeps the binder (with `◾` for a `0` let);
* everything else: `eraseInfer`. -/
partial def eraseCheck (ctx : Ctx R) (t : Term R) (ty : VTy R) : TCM ETerm := do
  if erasable ctx ty then return .erased
  sorry

/-- **Exercise 5.1b.** Erase `t`, computing its type with the kernel's `infer`.

* variables, globals, applications (an argument to a `0`-quantity Π is `◾`);
* `fst`/`snd` are `proj 0`/`proj 1`; `split` binds the projections with `let`s;
* `ecase` on a tag is `case`; `cast` is its argument; `ann` is its term;
* the eliminators `ind`, `Desc.elim`, `out`, `coit`, `scofix` become primitives;
  `sfix` becomes a `fix`, and `scase` applies its method to the payload. -/
partial def eraseInfer (ctx : Ctx R) (t : Term R) : TCM (ETerm × VTy R) := do
  let ty ← quickType ctx t
  if erasable ctx ty then return (.erased, ty)
  if let .natLit n := t then return (.natLit n, ty)
  sorry

/-- Erase a term in inference mode, keeping only the program. -/
partial def eraseE (ctx : Ctx R) (t : Term R) : TCM ETerm := return (← eraseInfer ctx t).1

/-- Erase an application spine `h a₁ … aₙ` at once, returning its type: erasing `f a`
by erasing `f` recursively would re-infer every prefix (quadratic in long chains such
as string literals). -/
partial def eraseSpine (ctx : Ctx R) (t : Term R) : TCM (ETerm × VTy R) := do
  let (h, args) := t.spine
  let (h', hty) ← eraseInfer ctx h
  let mut acc := h'
  let mut fty := hty
  for a in args do
    match whnf fty with
    | .pi _ _ q dom cod _ =>
      let a' ← if isZeroQ q then pure .erased else eraseCheck ctx a dom
      acc := .app acc a'
      fty := Closure.inst ctx.globals cod (ctx.eval a)
    | _ => throw (.other "erasure: application of a non-function")
  pure (acc, fty)

end

/-! ### Resolving views

Redexes `(λ x. b) a` become `let x := a; b`. Case analysis gets a value's payload as `view D x`. Its projections are resolved
against the flat object: with `x` bound to `y`, the payload's `.0` is the tag of `y`
(`prim .tag`, or a `case` on `y` itself), and `.1.….1.0` (`j` times `.1`) is field
`j - 1`. Without a tag in front (`absorbed = false`) it is field `j`; for a number, the
tag and field are `natTag` and `natPred`. A view used any other way is converted with
`unpack`. -/

/-- A variable bound to (a suffix of) a payload: `j` levels into the view of the flat
value at level `y`; `D` is the description, valid at level `dLvl`. -/
structure Virt where
  y : Nat
  j : Nat
  absorbed : Bool
  nat : Bool
  D : ETerm
  dLvl : Nat

/-- The field that `.0` of a view reaches, at depth `d`. -/
def Virt.field (v : Virt) (d : Nat) : ETerm :=
  let y := ETerm.var (d - 1 - v.y)
  if v.absorbed then
    if v.j == 0 then .prim (if v.nat then .natTag else .tag) #[y]
    else if v.nat then .prim .natPred #[y] else .proj (v.j - 1) y
  else .proj v.j y

/-- The view as an ordinary payload, at depth `d`. -/
def Virt.materialize (v : Virt) (d : Nat) : ETerm :=
  (List.range v.j).foldl (fun t _ => .proj 1 t) (.prim .unpack #[v.D.lift (d - v.dLvl), .var (d - 1 - v.y)])

private def isView : ETerm → Bool
  | .prim (.view ..) _ => true
  | _ => false

mutual

private partial def rwV (d : Nat) (env : List (Option Virt)) : ETerm → Sum Virt ETerm
  | .var i => match env[i]? with
    | some (some v) => .inl v
    | _ => .inr (.var i)
  | .proj k t => match rwV d env t with
    | .inl v => if k == 1 then .inl { v with j := v.j + 1 } else .inr (v.field d)
    | .inr t' => .inr (.proj k t')
  | t => .inr (rw d env t)

private partial def rw (d : Nat) (env : List (Option Virt)) (t : ETerm) : ETerm :=
  match t with
  | .var i => match env[i]? with
    | some (some v) => v.materialize d
    | _ => .var i
  | .proj .. => match rwV d env t with
    | .inl v => v.materialize d
    | .inr t' => t'
  | .letE x (.prim (.view ab nat) #[D, e]) b =>
    -- let y := e; let x := ◾; b   (b lives under x and y: lift past y)
    let v : Virt := { y := d, j := 0, absorbed := ab, nat, D := rw d env D, dLvl := d }
    .letE "y" (rw d env e) (.letE x .erased (rw (d + 2) (some v :: none :: env) (b.lift 1 1)))
  | .letE x val b => match rwV d env val with
    | .inl v => .letE x .erased (rw (d + 1) (some v :: env) b)
    | .inr val' => .letE x val' (rw (d + 1) (none :: env) b)
  | .app .. =>
    let (h, args) := spine t []
    let viewy (a : ETerm) : Bool := isView a || (rwV d env a matches .inl _)
    match h with
    -- `(λ x… . b) a…` is `let x := a; …` (in a strict language), and doesn't need a closure
    | .lam .. => rw d env (toLets h args 0)
    -- `(case s [b…]) a…` with a view among simple arguments: `case s [b a…, …]`
    | .case s bs =>
      if args.all simple && args.any viewy then rw d env (.case s (bs.map (ETerm.apps · args)))
      else args.foldl (fun f a => .app f (rw d env a)) (rw d env h)
    | _ => args.foldl (fun f a => .app f (rw d env a)) (rw d env h)
  | .case s bs =>
    let s' := match rwV d env s with
      | .inl v => v.materialize d
      | .inr s' => s'
    -- `case` reads the tag of an object itself
    let s' := match s' with
      | .prim .tag #[y] => y
      | s' => s'
    .case s' (bs.map (rw d env))
  | .lam x b => .lam x (rw (d + 1) (none :: env) b)
  | .fix x b => .fix x (rw (d + 1) (none :: env) b)
  | .obj tg fs => .obj tg (fs.map (rw d env))
  | .prim (.view _ _) #[D, e] => .prim .unpack #[rw d env D, rw d env e]
  | .prim op as => .prim op (as.map (rw d env))
  | t => t
where
  spine : ETerm → List ETerm → ETerm × List ETerm
    | .app f a, acc => spine f (a :: acc)
    | t, acc => (t, acc)
  simple : ETerm → Bool
    | .var _ | .erased => true
    | .proj _ t => simple t
    | _ => false
  toLets : ETerm → List ETerm → Nat → ETerm
    | .lam x b, a :: as, k => .letE x (a.lift k) (toLets b as (k + 1))
    | b, as, k => ETerm.apps b (as.map (·.lift k))

end

/-- Resolve the views of a closed erased term. -/
def resolveViews (e : ETerm) : ETerm := rw 0 [] e

/-- Erase a closed term against its type, with views resolved. -/
def eraseTop (ctx : Ctx R) (t : Term R) (ty : VTy R) : TCM ETerm :=
  return resolveViews (← eraseCheck ctx t ty)

/-- Erase a global definition. -/
def eraseDecl (g : Globals R) (d : Decl R) : TCM ETerm := do
  -- the compiler's version (direct recursion), if the elaborator made one
  let some v := d.impl <|> d.value | return .prim .unreachable #[]
  let ctx : Ctx R := { globals := g }
  -- universe polymorphism has no runtime content, but `Sort 0` would make motives
  -- propositions (and everything erasable): erase the `Type` instance
  let us := d.levelParams.map fun _ => Level.succ .zero
  eraseTop ctx (v.instLevels d.levelParams us) (ctx.eval (d.type.instLevels d.levelParams us))

end Wiz
