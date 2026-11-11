import Wiz.Core.Pretty
import Wiz.Elab.Basic

/-!
# Tagged terms, for the infoview

`Term.prettyTagged` prints a term exactly as `Term.pretty` does, but as **tagged text**:
every printed subterm is wrapped in a tag naming it, so an infoview can highlight the
subterm under the mouse and ask about it (`wiz/subtermInfo`). A tag holds an index into
the array of subterms the printer returns; the language server turns those into refs of
the document's session table.

Each subterm remembers its context: the names and (where known) types of the variables in
scope, innermost first, so its type can be inferred later. A `fun` binder's type isn't in
the term, so under a `fun` it is unknown.
-/

namespace Wiz

inductive TT where
  | text (s : String)
  | append (xs : Array TT)
  | tag (id : Nat) (t : TT)
  deriving Inhabited, Repr

partial def TT.flatten : TT → String
  | .text s => s
  | .append xs => String.join (xs.toList.map TT.flatten)
  | .tag _ t => t.flatten

/-- A printed subterm: what it is, and the variables in scope (innermost first; the type
of each lives in the context of the ones after it). -/
structure Subterm (R : Type) where
  kind : String
  name : Option Name := none
  names : List Name
  types : List (Option (Term R))
  term : Term R

instance {R : Type} : Inhabited (Subterm R) := ⟨{ kind := "", names := [], types := [], term := .var 0 }⟩

variable {R : Type} [QuantitySyntax R] [BEq R]

namespace Tagged

abbrev M (R : Type) := StateM (Array (Subterm R))

def txt (s : String) : TT := .text s
def cat (xs : List TT) : TT := .append xs.toArray
def paren (b : Bool) (t : TT) : TT := if b then cat [txt "(", t, txt ")"] else t

def freshen (names : List Name) (x : Name) : Name :=
  if x == "_" then x else go (names.length + 1) x
where
  go : Nat → Name → Name
    | 0, y => y
    | n + 1, y => if names.contains y then go n (y ++ "'") else y

def isDefaultQ (bi : BinderInfo) : Term R → Bool
  | .qlit r => r == if bi == .implicit then QuantitySyntax.implicitDefault else QuantitySyntax.explicitDefault
  | _ => false

def kindOf : Term R → String
  | .var _ => "var" | .const .. => "const" | .sort _ => "sort" | .app .. => "app"
  | .lam .. => "lam" | .pi .. => "pi" | .letE .. | .split .. => "let" | .sigma .. => "sigma"
  | .pair .. => "pair" | .fst _ | .snd _ => "proj" | .eq .. | .eqTy .. | .refl .. | .reflTy _ => "eq"
  | .natLit _ | .qlit _ => "lit" | .mu .. | .nu .. | .con _ => "data"
  | _ => "other"

partial def go (names : List Name) (tys : List (Option (Term R))) (prec : Nat) (t : Term R) : M R TT := do
  let body ← printNode
  let id := (← get).size
  let name := match t with
    | .var ix => some (names[ix]?.getD s!"#{ix}")
    | .const n _ => some n
    | _ => none
  modify (·.push { kind := kindOf t, name, names, types := tys, term := t })
  pure (.tag id body)
where
  sub (p : Nat) (u : Term R) : M R TT := go names tys p u
  app (f : TT) (args : List (Term R)) : M R TT := do
    let as ← args.mapM (sub 1023)
    pure (paren (prec > 1022) (cat (f :: as.flatMap fun a => [txt " ", a])))
  qtyPrefix (bi : BinderInfo) : Term R → M R TT
    | .qlit r =>
      let dflt := if bi == .implicit then QuantitySyntax.implicitDefault else QuantitySyntax.explicitDefault
      pure (txt (if r == dflt then "" else QuantitySyntax.display r ++ " "))
    | q => do pure (cat [txt "%", ← sub 1024 q, txt " "])
  tuple : Term R → Array (Term R) → Array (Term R)
    | .pair a b, acc => tuple b (acc.push a)
    | t, acc => acc.push t
  spine : Term R → Array (Term R) → Term R × Array (Term R)
    | .app f a, acc => spine f (#[a] ++ acc)
    | t, acc => (t, acc)
  sep (xs : List TT) (s : String) : TT :=
    cat (xs.zipIdx.flatMap fun (x, i) => if i == 0 then [x] else [txt s, x])
  printNode : M R TT := do
    match t with
    | .var ix => pure (txt (names[ix]?.getD s!"#{ix}"))
    | .const n _ => pure (txt n)
    | .mvar m => pure (txt s!"?m{m}")
    | .qty => pure (txt "Qty")
    | .size => pure (txt "Size")
    | .sizeLt s => pure (paren (prec > 1022) (cat [txt "Size< ", ← sub 1024 s]))
    | .szInf => pure (txt "∞")
    | .szSuc s => pure (cat [txt "↑", ← sub 1024 s])
    | .sfix _ _ _ _ P f s i x => app (txt "sfix") [P, f, s, i, x]
    | .cocon x => app (txt "cocon") [x]
    | .scase _ _ _ _ P m s i x => app (txt "scase") [P, m, s, i, x]
    | .scofix _ _ _ A f s i a => app (txt "scofix") [A, f, s, i, a]
    | .qlit r => pure (txt (QuantitySyntax.display r))
    | .sort l => pure (paren (prec > 1022 && !atomicSort l) (txt (showSort l)))
    | .pi x bi q dom cod _ =>
      if bi == .default && isDefaultQ .default q && !cod.hasVar 0 then
        pure (paren (prec > 25) (cat [← sub 26 dom, txt " → ", ← go ("_" :: names) (some dom :: tys) 25 cod]))
      else
        let x' := freshen names (if x == "_" then "x" else x)
        let (o, c) := match bi with
          | .implicit => ("{", "}")
          | .instImplicit => ("[", "]")
          | .default => ("(", ")")
        pure (paren (prec > 25) (cat [txt o, ← qtyPrefix bi q, txt s!"{x'} : ", ← sub 0 dom, txt s!"{c} → ",
          ← go (x' :: names) (some dom :: tys) 25 cod]))
    | .lam .. =>
      let rec lams (names : List Name) (tys : List (Option (Term R))) : Term R → Array Name → Array Name × List Name × List (Option (Term R)) × Term R
        | .lam x b, acc =>
          let x' := freshen names (if x == "_" && b.hasVar 0 then "x" else x)
          lams (x' :: names) (none :: tys) b (acc.push x')
        | t, acc => (acc, names, tys, t)
      let (xs, names', tys', body) := lams names tys t #[]
      pure (paren (prec > 0) (cat [txt s!"fun {" ".intercalate xs.toList} => ", ← go names' tys' 0 body]))
    | .app .. =>
      let (f, args) := spine t #[]
      let as ← args.toList.mapM (sub 1023)
      let hd ← sub 1024 f
      pure (paren (prec > 1022) (cat (hd :: as.flatMap fun a => [txt " ", a])))
    | .letE x q ty val body =>
      let x' := freshen names x
      pure (paren (prec > 0) (cat [txt "let ", ← qtyPrefix .default q, txt s!"{x'} : ", ← sub 0 ty, txt " := ",
        ← sub 0 val, txt "; ", ← go (x' :: names) (some ty :: tys) 0 body]))
    | .ann tm ty => pure (cat [txt "(", ← sub 0 tm, txt " : ", ← sub 0 ty, txt ")"])
    | .sigma x q a b _ =>
      if isDefaultQ .default q && !b.hasVar 0 then
        pure (paren (prec > 35) (cat [← sub 36 a, txt " × ", ← go ("_" :: names) (some a :: tys) 35 b]))
      else
        let x' := freshen names x
        pure (paren (prec > 35) (cat [txt "(", ← qtyPrefix .default q, txt s!"{x'} : ", ← sub 0 a, txt ") × ",
          ← go (x' :: names) (some a :: tys) 35 b]))
    | .pair .. =>
      let parts ← (tuple t #[]).toList.mapM (sub 0)
      pure (cat [txt "(", sep parts ", ", txt ")"])
    | .fst u => pure (cat [← sub 1024 u, txt ".1"])
    | .snd u => pure (cat [← sub 1024 u, txt ".2"])
    | .split q s _ _ x y b =>
      let x' := freshen names x
      let y' := freshen (x' :: names) y
      pure (paren (prec > 0) (cat [txt "let ", ← qtyPrefix .default q, txt s!"({x'}, {y'}) := ", ← sub 0 s, txt "; ",
        ← go (y' :: x' :: names) (none :: none :: tys) 0 b]))
    | .unit l => pure (txt (match l.toNat? with
      | some 0 => "True"
      | some 1 => "Unit"
      | _ => s!"Unit.\{{l}}"))
    | .tt => pure (txt "()")
    | .empty l => pure (txt (match l.toNat? with
      | some 0 => "False"
      | some 1 => "Empty"
      | _ => s!"Empty.\{{l}}"))
    | .absurd _ u => pure (paren (prec > 1022) (cat [txt "absurd ", ← sub 1023 u]))
    | .eq _ a b | .eqTy a b => pure (paren (prec > 50) (cat [← sub 51 a, txt " = ", ← sub 51 b]))
    | .refl _ a | .reflTy a => pure (paren (prec > 1022) (cat [txt "refl ", ← sub 1023 a]))
    | .cast _ _ e u => pure (paren (prec > 1022) (cat [txt "cast ", ← sub 1023 e, txt " ", ← sub 1023 u]))
    | .enum ls => pure (txt s!"Enum [{", ".intercalate ls}]")
    | .tag ls i => pure (txt s!"'{ls[i]?.getD s!"#{i}"}")
    | .ecase _ _ u bs =>
      let bs ← bs.mapM (sub 0)
      pure (paren (prec > 1022) (cat [txt "ecase ", ← sub 1023 u, txt " [", sep bs ", ", txt "]"]))
    | .desc _ I => pure (paren (prec > 1022) (cat [txt "Desc ", ← sub 1023 I]))
    | .dret i => app (txt "Desc.ret") [i]
    | .darg q S D => app (txt "Desc.arg") [q, S, D]
    | .drec q j D => app (txt "Desc.rec") [q, j, D]
    | .dhrec q H j D => app (txt "Desc.hrec") [q, H, j, D]
    | .delim _ P a b c h D => app (txt "Desc.elim") [P, a, b, c, h, D]
    | .mu _ _ _ _ s (some (n, _, as)) | .nu _ _ _ _ s (some (n, _, as)) =>
      let head ← if s matches .szInf then pure (txt n) else pure (cat [txt s!"{n}^", ← sub 1024 s])
      if as.isEmpty then pure head else app head as
    | .mu _ _ D i s none =>
      app (← if s matches .szInf then pure (txt "μ") else pure (cat [txt "μ^", ← sub 1024 s])) [D, i]
    | .con (.pair (.tag ls i) rest) | .con (.pair (.up (.tag ls i)) rest) =>
      let fields := (tuple rest #[]).toList
      let fields := fields.take (fields.length - 2)
      let c := txt s!".{ls[i]?.getD s!"#{i}"}"
      if fields.isEmpty then pure c else app c fields
    | .con x => app (txt "con") [x]
    | .ind _ _ _ _ P m i x => app (txt "ind") [P, m, i, x]
    | .nu _ _ D i s none =>
      app (← if s matches .szInf then pure (txt "ν") else pure (cat [txt "ν^", ← sub 1024 s])) [D, i]
    | .out x => app (txt "out") [x]
    | .coit _ _ _ S st i s => app (txt "coit") [S, st, i, s]
    | .natLit n => pure (txt (toString n))
    | .ulift _ _ A => app (txt "ULift") [A]
    | .up a | .down a | .prf _ a => sub prec a
    | .natOp op args => app (txt s!"<{op}>") args.toList
    | .transp _ _ P p _ e =>
      pure (paren (prec > 1022) (cat [txt "transp ", ← sub 1023 P, txt " ", ← sub 1023 p, txt " ", ← sub 1023 e]))

end Tagged

/-- Print `t` (with `names` and their types in scope, innermost first) as tagged text,
appending its subterms to the state. Flattened, it is `t.pretty names`. -/
def Term.prettyTagged (names : List Name) (tys : List (Option (Term R))) (t : Term R) :
    StateM (Array (Subterm R)) TT :=
  Tagged.go names tys 0 t

/-! ## Goals -/

/-- The context of a goal's target: names and types, innermost first. -/
def GoalView.scope (g : GoalView R) : List Name × List (Option (Term R)) :=
  (g.hyps.toList.reverse.map (·.1), g.hyps.toList.reverse.map (some ·.2.1))

/-- A hypothesis and a goal, tagged. -/
structure TaggedGoal where
  hyps : Array (Name × TT × Option TT)
  target : TT
  userName : Option Name

def GoalView.tagged (g : GoalView R) : StateM (Array (Subterm R)) TaggedGoal := do
  let mut hyps := #[]
  let mut names : List Name := []
  let mut tys : List (Option (Term R)) := []
  for (x, ty, v) in g.hyps do
    let t ← ty.prettyTagged names tys
    let v ← v.mapM (·.prettyTagged names tys)
    hyps := hyps.push (x, t, v)
    names := x :: names
    tys := some ty :: tys
  pure { hyps, target := ← g.target.prettyTagged names tys, userName := g.userName }

end Wiz
