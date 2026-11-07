import Wiz.Query

/-!
# The shared cache

The query engine's memo table, on disk: a command's **effect** (the declarations it
adds, its messages, and its registrations) is stored in `$WIZ_CACHE/<key>.wizc`, where
the key is the chained content hash of the command and everything before it (and a
version salt). Elaboration is deterministic, so a shared directory is a shared cache:
two machines elaborating the same text compute the same keys and the same effects.

Commands that change the grammar or the macros (`syntax`, `macro_rules`, `notation`,
attributes, `import`, user-defined commands) aren't cached; they are cheap to rerun.
Declarations read from the cache were checked by the kernel when they were stored, so
they are trusted.

The format is S-expressions; quantities are written with the rig's literal syntax.
-/

namespace Wiz.Cache

variable {R : Type} [QRig R] [DecidableEq R] [ToString R] [QuantitySyntax R]

inductive Sx where
  | a (s : String)
  | l (xs : Array Sx)
  deriving Inhabited

partial def Sx.render : Sx → String
  | .a s => if !s.isEmpty && s.toList.all (fun c => c.isAlphanum || "._-+*'→✝".toList.contains c) then s else s.quote
  | .l xs => "(" ++ " ".intercalate (xs.toList.map Sx.render) ++ ")"

/-- Parse an S-expression (atoms are bare words or Lean-style string literals). -/
partial def Sx.parse (s : String) : Option Sx :=
  match go s.toList with
  | some (x, rest) => if rest.all (·.isWhitespace) then some x else none
  | none => none
where
  go (cs : List Char) : Option (Sx × List Char) := do
    let cs := cs.dropWhile (·.isWhitespace)
    match cs with
    | '(' :: rest =>
      let rec items (cs : List Char) (acc : Array Sx) : Option (Array Sx × List Char) :=
        match cs.dropWhile (·.isWhitespace) with
        | ')' :: rest => some (acc, rest)
        | [] => none
        | cs => do let (x, rest) ← go cs; items rest (acc.push x)
      let (xs, rest) ← items rest #[]
      return (.l xs, rest)
    | '"' :: rest =>
      let rec str (cs : List Char) (acc : List Char) : Option (String × List Char) :=
        match cs with
        | '\\' :: 'n' :: cs => str cs ('\n' :: acc)
        | '\\' :: 't' :: cs => str cs ('\t' :: acc)
        | '\\' :: 'x' :: h₁ :: h₂ :: cs =>
          let hex (c : Char) : Nat := if c.isDigit then c.toNat - 48 else c.toLower.toNat - 87
          str cs (Char.ofNat (16 * hex h₁ + hex h₂) :: acc)
        | '\\' :: 'u' :: '{' :: cs =>
          let ds := cs.takeWhile (· != '}')
          let hex (c : Char) : Nat := if c.isDigit then c.toNat - 48 else c.toLower.toNat - 87
          str (cs.drop (ds.length + 1)) (Char.ofNat (ds.foldl (fun n c => 16 * n + hex c) 0) :: acc)
        | '\\' :: c :: cs => str cs (c :: acc)
        | '"' :: cs => some (String.ofList acc.reverse, cs)
        | c :: cs => str cs (c :: acc)
        | [] => none
      let (s, rest) ← str rest []
      return (.a s, rest)
    | [] => none
    | cs =>
      let w := cs.takeWhile fun c => !c.isWhitespace && c != '(' && c != ')'
      if w.isEmpty then none else return (.a (String.ofList w), cs.drop w.length)

def node (tag : String) (xs : List Sx) : Sx := .l (#[.a tag] ++ xs.toArray)
def nat (n : Nat) : Sx := .a (toString n)
def str (s : String) : Sx := .a s
def list (xs : List Sx) : Sx := .l xs.toArray

partial def level : Level → Sx
  | .zero => .a "0"
  | .succ l => node "S" [level l]
  | .max a b => node "max" [level a, level b]
  | .imax a b => node "imax" [level a, level b]
  | .param n => node "p" [str n]
  | .mvar m => node "m" [nat m]

def bi : BinderInfo → Sx
  | .default => .a "d" | .implicit => .a "i" | .instImplicit => .a "I"

partial def term : Term R → Sx
  | .var i => node "var" [nat i]
  | .const n us => node "const" [str n, list (us.map level)]
  | .sort l => node "sort" [level l]
  | .pi x b q A B => node "pi" [str x, bi b, term q, term A, term B]
  | .lam x b => node "lam" [str x, term b]
  | .app f a => node "app" [term f, term a]
  | .letE x q t v b => node "let" [str x, term q, term t, term v, term b]
  | .ann t ty => node "ann" [term t, term ty]
  | .mvar m => node "mvar" [nat m]
  | .sigma x q a b => node "sigma" [str x, term q, term a, term b]
  | .pair a b => node "pair" [term a, term b]
  | .fst t => node "fst" [term t]
  | .snd t => node "snd" [term t]
  | .split q s z m x y b => node "split" [term q, term s, str z, term m, str x, str y, term b]
  | .unit l => node "unit" [level l]
  | .tt => .a "tt"
  | .empty l => node "empty" [level l]
  | .absurd m t => node "absurd" [term m, term t]
  | .eq A a b => node "eq" [term A, term a, term b]
  | .eqTy A B => node "eqTy" [term A, term B]
  | .refl A a => node "refl" [term A, term a]
  | .reflTy X => node "reflTy" [term X]
  | .cast A B e t => node "cast" [term A, term B, term e, term t]
  | .transp A a P p b e => node "transp" [term A, term a, term P, term p, term b, term e]
  | .qty => .a "qty"
  | .qlit r => node "q" [str (QuantitySyntax.display r)]
  | .enum ls => node "enum" [list (ls.map str)]
  | .tag ls i => node "tag" [list (ls.map str), nat i]
  | .ecase z m s bs => node "ecase" [str z, term m, term s, list (bs.map term)]
  | .desc l I => node "desc" [level l, term I]
  | .dret i => node "dret" [term i]
  | .darg q S D => node "darg" [term q, term S, term D]
  | .drec q j D => node "drec" [term q, term j, term D]
  | .dhrec q H j D => node "dhrec" [term q, term H, term j, term D]
  | .delim v P a b c h D => node "delim" [level v, term P, term a, term b, term c, term h, term D]
  | .mu l I D i s h => node "mu" [level l, term I, term D, term i, term s, hint h]
  | .con x => node "con" [term x]
  | .ind l I D v P m i x => node "ind" [level l, term I, term D, level v, term P, term m, term i, term x]
  | .nu l I D i s h => node "nu" [level l, term I, term D, term i, term s, hint h]
  | .out x => node "out" [term x]
  | .size => .a "size"
  | .szInf => .a "inf"
  | .szSuc s => node "szSuc" [term s]
  | .sizeLt s => node "sizeLt" [term s]
  | .sfix l I D v P f s i x => node "sfix" [level l, term I, term D, level v, term P, term f, term s, term i, term x]
  | .scase l I D v P m s i x => node "scase" [level l, term I, term D, level v, term P, term m, term s, term i, term x]
  | .cocon x => node "cocon" [term x]
  | .scofix l I D A f s i a => node "scofix" [level l, term I, term D, term A, term f, term s, term i, term a]
  | .coit l I D S st i s => node "coit" [level l, term I, term D, term S, term st, term i, term s]
  | .natLit n => node "nat" [nat n]
  | .natOp op as => node "natOp" [str op, list (as.toList.map term)]
where
  hint : Option (Name × List Level × List (Term R)) → Sx
    | none => .a "none"
    | some (n, us, as) => node "hint" [str n, list (us.map level), list (as.map term)]

/-! ## Decoding -/

def atom? : Sx → Option String
  | .a s => some s
  | _ => none
def items? : Sx → Option (Array Sx)
  | .l xs => some xs
  | _ => none

partial def dlevel : Sx → Option Level
  | .a "0" => some .zero
  | .l #[.a "S", l] => (dlevel l).map .succ
  | .l #[.a "max", a, b] => return .max (← dlevel a) (← dlevel b)
  | .l #[.a "imax", a, b] => return .imax (← dlevel a) (← dlevel b)
  | .l #[.a "p", .a n] => some (.param n)
  | .l #[.a "m", .a n] => n.toNat?.map .mvar
  | _ => none

def dbi : Sx → Option BinderInfo
  | .a "d" => some .default | .a "i" => some .implicit | .a "I" => some .instImplicit | _ => none

partial def dterm : Sx → Option (Term R)
  | .a "tt" => some .tt
  | .a "qty" => some .qty
  | .a "size" => some .size
  | .a "inf" => some .szInf
  | .l xs => do
    let tag ← atom? (xs[0]?.getD (.a ""))
    let x (i : Nat) : Sx := xs[i]?.getD (.a "")
    let t (i : Nat) : Option (Term R) := dterm (x i)
    let s (i : Nat) : Option String := atom? (x i)
    let n (i : Nat) : Option Nat := (s i).bind String.toNat?
    let lv (i : Nat) : Option Level := dlevel (x i)
    let ts (i : Nat) : Option (List (Term R)) := do (← items? (x i)).toList.mapM dterm
    let ss (i : Nat) : Option (List String) := do (← items? (x i)).toList.mapM atom?
    let hint (i : Nat) : Option (Option (Name × List Level × List (Term R))) :=
      match x i with
      | .a "none" => some none
      | .l #[.a "hint", .a nm, us, as] => do
        some (some (nm, ← (← items? us).toList.mapM dlevel, ← (← items? as).toList.mapM dterm))
      | _ => none
    match tag with
    | "var" => return .var (← n 1)
    | "const" => return .const (← s 1) (← (← items? (x 2)).toList.mapM dlevel)
    | "sort" => return .sort (← lv 1)
    | "pi" => return .pi (← s 1) (← dbi (x 2)) (← t 3) (← t 4) (← t 5)
    | "lam" => return .lam (← s 1) (← t 2)
    | "app" => return .app (← t 1) (← t 2)
    | "let" => return .letE (← s 1) (← t 2) (← t 3) (← t 4) (← t 5)
    | "ann" => return .ann (← t 1) (← t 2)
    | "mvar" => return .mvar (← n 1)
    | "sigma" => return .sigma (← s 1) (← t 2) (← t 3) (← t 4)
    | "pair" => return .pair (← t 1) (← t 2)
    | "fst" => return .fst (← t 1)
    | "snd" => return .snd (← t 1)
    | "split" => return .split (← t 1) (← t 2) (← s 3) (← t 4) (← s 5) (← s 6) (← t 7)
    | "unit" => return .unit (← lv 1)
    | "empty" => return .empty (← lv 1)
    | "absurd" => return .absurd (← t 1) (← t 2)
    | "eq" => return .eq (← t 1) (← t 2) (← t 3)
    | "eqTy" => return .eqTy (← t 1) (← t 2)
    | "refl" => return .refl (← t 1) (← t 2)
    | "reflTy" => return .reflTy (← t 1)
    | "cast" => return .cast (← t 1) (← t 2) (← t 3) (← t 4)
    | "transp" => return .transp (← t 1) (← t 2) (← t 3) (← t 4) (← t 5) (← t 6)
    | "q" => return .qlit (← QuantitySyntax.ofLiteral (← s 1))
    | "enum" => return .enum (← ss 1)
    | "tag" => return .tag (← ss 1) (← n 2)
    | "ecase" => return .ecase (← s 1) (← t 2) (← t 3) (← ts 4)
    | "desc" => return .desc (← lv 1) (← t 2)
    | "dret" => return .dret (← t 1)
    | "darg" => return .darg (← t 1) (← t 2) (← t 3)
    | "drec" => return .drec (← t 1) (← t 2) (← t 3)
    | "dhrec" => return .dhrec (← t 1) (← t 2) (← t 3) (← t 4)
    | "delim" => return .delim (← lv 1) (← t 2) (← t 3) (← t 4) (← t 5) (← t 6) (← t 7)
    | "mu" => return .mu (← lv 1) (← t 2) (← t 3) (← t 4) (← t 5) (← hint 6)
    | "con" => return .con (← t 1)
    | "ind" => return .ind (← lv 1) (← t 2) (← t 3) (← lv 4) (← t 5) (← t 6) (← t 7) (← t 8)
    | "nu" => return .nu (← lv 1) (← t 2) (← t 3) (← t 4) (← t 5) (← hint 6)
    | "out" => return .out (← t 1)
    | "szSuc" => return .szSuc (← t 1)
    | "sizeLt" => return .sizeLt (← t 1)
    | "sfix" => return .sfix (← lv 1) (← t 2) (← t 3) (← lv 4) (← t 5) (← t 6) (← t 7) (← t 8) (← t 9)
    | "scase" => return .scase (← lv 1) (← t 2) (← t 3) (← lv 4) (← t 5) (← t 6) (← t 7) (← t 8) (← t 9)
    | "cocon" => return .cocon (← t 1)
    | "scofix" => return .scofix (← lv 1) (← t 2) (← t 3) (← t 4) (← t 5) (← t 6) (← t 7) (← t 8)
    | "coit" => return .coit (← lv 1) (← t 2) (← t 3) (← t 4) (← t 5) (← t 6) (← t 7)
    | "nat" => return .natLit (← n 1)
    | "natOp" => return .natOp (← s 1) (← ts 2).toArray
    | _ => none
  | _ => none

/-! ## Command effects -/

/-- What a command added to the state. -/
structure Effect (R : Type) where
  decls : Array (Decl R) := #[]
  messages : Array Msg := #[]
  builtins : List (Name × Name) := []
  classes : List ClassInfo := []
  instances : Array InstanceInfo := #[]
  coinductives : List (Name × List (Name × Bool)) := []
  foreignTypes : List (Name × String) := []
  cCode : Array String := #[]
  hovers : Array (SourceInfo × Name × String) := #[]
  sites : Array (Name × SourceInfo × String) := #[]

/-- The command kinds whose effect is just the fields of `Effect`. -/
def cacheable : List Name :=
  ["command.def", "command.axiom", "command.defEqns", "command.inductive", "command.structure",
   "command.class", "command.instance", "command.coinductive", "command.builtin", "command.extern",
   "command.glue", "command.foreignType", "command.check", "command.reduce", "command.eval",
   "command.erase", "command.run", "command.ir"]

def effectOf (s s' : CommandState R) : Effect R :=
  let newNames := s'.globals.order.extract s.globals.order.size s'.globals.order.size
  { decls := newNames.filterMap s'.globals.find?
    messages := s'.messages.extract s.messages.size s'.messages.size
    builtins := s'.builtins.take (s'.builtins.length - s.builtins.length)
    classes := s'.classes.take (s'.classes.length - s.classes.length)
    instances := s'.instances.extract s.instances.size s'.instances.size
    coinductives := s'.coinductives.drop s.coinductives.length
    foreignTypes := s'.foreignTypes.take (s'.foreignTypes.length - s.foreignTypes.length)
    cCode := s'.cCode.extract s.cCode.size s'.cCode.size
    hovers := s'.hovers.extract s.hovers.size s'.hovers.size
    sites := newNames.filterMap fun n => (s'.declSites.get? n).map fun (i, m) => (n, i, m) }

/-- Replay an effect. -/
def Effect.apply (e : Effect R) (s : CommandState R) : CommandState R :=
  let globals := e.decls.foldl (·.insert ·) s.globals
  let globals := { globals with builtins := e.builtins ++ globals.builtins }
  { s with globals, messages := s.messages ++ e.messages, builtins := e.builtins ++ s.builtins,
           classes := e.classes ++ s.classes, instances := s.instances ++ e.instances,
           coinductives := s.coinductives ++ e.coinductives, foreignTypes := e.foreignTypes ++ s.foreignTypes,
           cCode := s.cCode ++ e.cCode, hovers := s.hovers ++ e.hovers,
           declSites := e.sites.foldl (fun m (n, i, md) => m.insert n (i, md)) s.declSites }

def info (i : SourceInfo) : Sx := list [nat i.start, nat i.stop]
def dinfo (x : Sx) : Option SourceInfo := do
  let #[a, b] ← items? x | none
  pure { start := ← (← atom? a).toNat?, stop := ← (← atom? b).toNat? }

def Effect.toSx (e : Effect R) : Sx :=
  let decl (d : Decl R) : Sx := list [str d.name, list (d.levelParams.map str), term d.type,
    (match d.value with | some v => term v | none => .a "none"), .a (toString d.inline)]
  let msg (m : Msg) : Sx := list [info m.info, .a (if m.severity == .error then "error" else "info"), str m.text]
  list [list (e.decls.toList.map decl), list (e.messages.toList.map msg),
    list (e.builtins.map fun (k, n) => list [str k, str n]),
    list (e.classes.map fun c => list [str c.name, list (c.outParams.map (.a ∘ toString)), list (c.fields.map str)]),
    list (e.instances.toList.map fun i => list [str i.name, str i.cls, nat i.priority]),
    list (e.coinductives.map fun (n, obs) => list [str n, list (obs.map fun (o, b) => list [str o, .a (toString b)])]),
    list (e.foreignTypes.map fun (n, f) => list [str n, str f]),
    list (e.cCode.toList.map str),
    list (e.hovers.toList.map fun (i, n, t) => list [info i, str n, str t]),
    list (e.sites.toList.map fun (n, i, m) => list [str n, info i, str m])]

def Effect.ofSx? (x : Sx) : Option (Effect R) := do
  let #[ds, ms, bs, cs, is, cos, fts, cc, hs, ss] ← items? x | none
  let decl (x : Sx) : Option (Decl R) := do
    let #[n, ps, ty, v, inl] ← items? x | none
    pure { name := ← atom? n, levelParams := ← (← items? ps).toList.mapM atom?, type := ← dterm ty,
           value := ← (match v with | .a "none" => some none | v => (dterm v).map some),
           inline := (← atom? inl) == "true" }
  let msg (x : Sx) : Option Msg := do
    let #[i, sev, t] ← items? x | none
    pure { info := ← dinfo i, severity := if (← atom? sev) == "error" then .error else .info, text := ← atom? t }
  let pair (x : Sx) : Option (String × String) := do
    let #[a, b] ← items? x | none
    pure (← atom? a, ← atom? b)
  pure {
    decls := (← (← items? ds).mapM decl)
    messages := (← (← items? ms).mapM msg)
    builtins := (← (← items? bs).toList.mapM pair)
    classes := (← (← items? cs).toList.mapM fun c => do
      let #[n, os, fs] ← items? c | none
      pure { name := ← atom? n, outParams := ← (← items? os).toList.mapM fun o => do pure ((← atom? o) == "true"),
             fields := ← (← items? fs).toList.mapM atom? })
    instances := (← (← items? is).mapM fun i => do
      let #[n, c, p] ← items? i | none
      pure { name := ← atom? n, cls := ← atom? c, priority := ← (← atom? p).toNat? })
    coinductives := (← (← items? cos).toList.mapM fun c => do
      let #[n, obs] ← items? c | none
      pure (← atom? n, ← (← items? obs).toList.mapM fun o => do
        let #[a, b] ← items? o | none
        pure (← atom? a, (← atom? b) == "true")))
    foreignTypes := (← (← items? fts).toList.mapM pair)
    cCode := (← (← items? cc).mapM atom?)
    hovers := (← (← items? hs).mapM fun h => do
      let #[i, n, t] ← items? h | none
      pure (← dinfo i, ← atom? n, ← atom? t))
    sites := (← (← items? ss).mapM fun x => do
      let #[n, i, m] ← items? x | none
      pure (← atom? n, ← dinfo i, ← atom? m)) }

/-- The cache's version: change it whenever the format or the elaborator's output changes. -/
def salt : UInt64 := hash "wiz-cache-1"

/-- Elaborate `input` (like `Query.elaborate`), reading and writing `dir`. Returns the
final state and how many commands came from the disk cache. -/
partial def elaborateCached (dir : System.FilePath) (input : String) (init : CommandState R) (key₀ : UInt64) :
    IO (CommandState R × Nat) := do
  IO.FS.createDirAll dir
  let chars := input.toList.toArray
  let mut pos := 0
  let mut s := init
  let mut key := mixHash salt key₀
  let _ : Inhabited (CommandState R) := ⟨init⟩
  let mut hits := 0
  while skipWs chars pos < chars.size do
    match parseCommand chars s.tables pos with
    | .error _ =>
      -- report the parse error (and everything after it) without the cache
      s := runFrontend.go input chars pos s
      break
    | .ok (cmd, stop) =>
      let text := String.ofList (chars.extract pos stop).toList
      key := mixHash key (hash text)
      if cmd.isOfKind "command.import" then
        -- a module: elaborate it through the cache too (its keys continue this chain)
        let m := ((cmd.getArg 1).getId?).getD "_"
        if !s.imported.contains m then
          match s.loader m with
          | none => s := { s with messages := s.messages.push { info := cmd.info, severity := .error, text := s!"unknown module {m}" } }
          | some src =>
            let (inner, h) ← elaborateCached dir src { s with imported := m :: s.imported, messages := #[], module := m } key
            hits := hits + h
            let errs := inner.messages.filter (·.severity == .error)
            let msg : Msg := { info := cmd.info, severity := .error,
                               text := s!"module {m} has errors: {errs.toList.map (·.render src)}" }
            s := { inner with messages := if errs.isEmpty then s.messages else s.messages.push msg,
                              module := s.module, hovers := s.hovers }
        pos := stop
        continue
      let file := dir / s!"{key}.wizc"
      let cached : Option (Effect R) ←
        if cacheable.contains cmd.kind && (← file.pathExists) then
          pure ((Sx.parse (← IO.FS.readFile file)).bind Effect.ofSx?)
        else pure none
      match cached with
      | some e =>
        s := e.apply s
        hits := hits + 1
      | none =>
        let s' := Query.elaborate.elabOne input chars pos stop s
        if cacheable.contains cmd.kind then
          IO.FS.writeFile file (effectOf s s').toSx.render
        s := s'
      pos := stop
  pure (s, hits)

end Wiz.Cache
