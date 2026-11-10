import Wiz.Compiler.IR
import Wiz.Compiler.Run
import WizRuntime

/-!
# C code generation

Each IR function becomes a C function on `wiz_val`s, plus a *boxed* version taking an
array, which closures point to. Variables become locals, `case` a `switch` on the
tag, join points labelled blocks entered with `goto` (their parameters are locals
assigned before the jump), and `dup`/`drop` calls to the runtime (`runtime/wiz.c`,
which is pasted at the top of the output; `Wiz.C.runtime`, in `runtime/WizRuntime.lean`).
-/

namespace Wiz.C

open IR

/-- A C identifier for a Wiz name: letters and digits stay, anything else is `_xx`. -/
def mangle (n : Name) : String :=
  "w_" ++ String.join (n.toList.map fun c =>
    if c.isAlphanum then c.toString
    else "_" ++ (Nat.toDigits 16 c.toNat).asString ++ "_")

def var (x : Var) : String := s!"x{x}"

/-- The C wrapper of a foreign function. -/
def externWrapper (key : Name) : String := "wiz_ext" ++ (mangle key).drop 1

/-- The variables a body binds (to declare them up front). -/
partial def bound (b : Body) (acc : Array Var := #[]) : Array Var :=
  match b with
  | .vdecl x _ b => bound b (acc.push x)
  | .case _ alts => alts.foldl (fun acc a => bound a acc) acc
  | .jdecl _ ps body k => bound k (bound body (acc ++ ps))
  | .dup _ b | .drop _ b => bound b acc
  | _ => acc

def args (xs : Array Var) : String := ", ".intercalate (xs.toList.map var)

def expr (arities : Std.HashMap Name Nat) (x : Var) : Expr → String
  | .erased => s!"{var x} = WIZ_BOX(0);"
  | .lit n =>
    if n < 2 ^ 62 then s!"{var x} = WIZ_BOX({n}UL);" else s!"{var x} = wiz_nat_lit(\"{n}\");"
  | .ctor t as =>
    if as.isEmpty then s!"{var x} = WIZ_BOX({t});"
    else
      let sets := as.toList.zipIdx.map fun (a, i) => s!" WIZ_SET({var x}, {i}, {var a});"
      s!"{var x} = wiz_ctor_new({t}, {as.size});" ++ String.join sets
  | .proj i y => s!"{var x} = wiz_proj({var y}, {i});"
  | .fap f as => s!"{var x} = {mangle f}({args as});"
  | .pap f as =>
    let arr := if as.isEmpty then "NULL" else s!"(wiz_val[]){lb}{args as}{rb}"
    s!"{var x} = wiz_clo_new({mangle f}_boxed, {(arities.get? f).getD 0}, {as.size}, {arr});"
  | .ap f as => s!"{var x} = wiz_apply({var f}, {as.size}, (wiz_val[]){lb}{args as}{rb});"
  | .reset y => s!"{var x} = wiz_reset({var y});"
  | .reuse tok t as =>
    let sets := as.toList.zipIdx.map fun (a, i) => s!" WIZ_SET({var x}, {i}, {var a});"
    s!"{var x} = wiz_reuse({var tok}, {t}, {as.size});" ++ String.join sets
  | .prim op as =>
    let fn := match op with
      | "nat.succ" => "wiz_nat_succ" | "nat.pred" => "wiz_nat_pred"
      | "nat.add" => "wiz_nat_add" | "nat.sub" => "wiz_nat_sub" | "nat.mul" => "wiz_nat_mul"
      | "nat.beq" => "wiz_nat_beq" | "nat.blt" => "wiz_nat_blt" | "lazyTag" => "wiz_lazy_tag" | "lazySet" => "wiz_lazy_set" | "memo" => "wiz_memo"
      | "tag" => "wiz_tag_of" | "natTag" => "wiz_nat_tag" | "fieldAt" => "wiz_field_at" | "mkObj" => "wiz_mk_obj"
      | "dropMoved" => "wiz_drop_moved"
      | op => if op.startsWith "nat." then "wiz_nat_" ++ (op.drop 4).toString
        else if (RVal.ExternSig.ofKey? op).isSome then externWrapper op else "wiz_unknown_prim"
    s!"{var x} = {fn}({args as});"
where
  lb := "{"
  rb := "}"

/-- The foreign functions a program uses. -/
partial def externs (decls : Array IR.Decl) : Array Name :=
  let rec go : Body → Array Name → Array Name
    | .vdecl _ (.prim op _) b, acc => go b (if (RVal.ExternSig.ofKey? op).isSome && !acc.contains op then acc.push op else acc)
    | .vdecl _ _ b, acc | .dup _ b, acc | .drop _ b, acc => go b acc
    | .case _ alts, acc => alts.foldl (fun acc a => go a acc) acc
    | .jdecl _ _ jb k, acc => go k (go jb acc)
    | _, acc => acc
  (decls.foldl (fun acc d => go d.body acc) #[]).qsort (· < ·)

def ctype : Char → String
  | 'n' | 'u' => "uint64_t"
  | 'f' => "double"
  | 's' => "const char *"
  | 'b' => "int"
  | 'p' => "void *"
  | 'w' => "wiz_val"
  | _ => "void"

open RVal (FKind)

/-- The C type of a kind (a struct's own type name). -/
def ftype : FKind → String
  | .k c => ctype c
  | .struct c _ _ => c

/-- (9i) The C definition of a struct whose layout is declared in Wiz without a header:
`struct t { … };` for a name `struct t`, else a `typedef`. Fields: `uint64_t` for `Nat`
and `UInt64`, `double`, `int` for `Bool`, `const char *`, `void *` for foreign pointers,
and the C types of nested structs. -/
def structDefinition (ctype : String) (fields : List (String × FKind)) : String :=
  let fs := fields.filter (fun (_, k) => k != .k 'e') |>.map fun (f, k) => s!"  {ftype k} {f};\n"
  if ctype.startsWith "struct " then s!"{ctype} \{\n{String.join fs}};\n"
  else s!"typedef struct \{\n{String.join fs}} {ctype};\n"

/-- The Wiz value of a structure's field `i` of `n`, borrowed from `v`: a structure is
nested pairs whose last pair is unboxed (`Erase.lean`, 22i), so one field is the value
itself. -/
def fieldPath (v : String) (i n : Nat) : String :=
  if n ≤ 1 then v else
  let rec seconds : Nat → String → String
    | 0, e => e
    | k + 1, e => seconds k s!"wiz_field_ref({e}, 1)"
  if i + 1 == n then seconds i v else s!"wiz_field_ref({seconds i v}, 0)"

/-- (9i) Marshalling helpers for the structs a program passes by value: `wiz_sin_N(&c, v)`
fills `c` from the (borrowed) Wiz value `v`, `wiz_sfree_N(&c)` frees what that allocated
(strings), `wiz_sout_N(c)` makes a Wiz value. Nested structs get their own helpers,
defined first. Returns the helpers and the number of each struct (by its key). -/
partial def structHelpers (ks : List FKind) : String × List (String × Nat) := Id.run do
  let mut out := ""
  let mut seen : List (String × Nat) := []
  let rec collect : FKind → List FKind
    | .struct c h fs => fs.flatMap (collect ·.2) ++ [.struct c h fs]
    | _ => []
  for k in ks.flatMap collect do
    let .struct c _ fs := k | continue
    if seen.any (·.1 == k.toKey) then continue
    let id := seen.length
    let num (k : FKind) : Nat := ((seen.find? (·.1 == k.toKey)).map (·.2)).getD 0
    let n := fs.length
    let mut sin := ""
    let mut sfree := ""
    let mut sout := ""
    for (f, fk) in fs, i in [0:n] do
      let path := fieldPath "v" i n
      let lhs := s!"c->{f}"
      match fk with
      | .k 'n' => sin := sin ++ s!"  {lb} wiz_val t = {path}; wiz_inc(t); {lhs} = wiz_in_nat(t); {rb}\n"
                  sout := sout ++ s!"  fs[{i}] = wiz_out_nat((uint64_t)c.{f});\n"
      | .k 'u' => sin := sin ++ s!"  {lb} wiz_val t = {path}; wiz_inc(t); {lhs} = wiz_in_u64(t); {rb}\n"
                  sout := sout ++ s!"  fs[{i}] = wiz_out_u64((uint64_t)c.{f});\n"
      | .k 'f' => sin := sin ++ s!"  {lb} wiz_val t = {path}; wiz_inc(t); {lhs} = wiz_in_f64(t); {rb}\n"
                  sout := sout ++ s!"  fs[{i}] = wiz_out_f64((double)c.{f});\n"
      | .k 'b' => sin := sin ++ s!"  {lb} wiz_val t = {path}; wiz_inc(t); {lhs} = wiz_in_bool(t); {rb}\n"
                  sout := sout ++ s!"  fs[{i}] = wiz_out_bool(c.{f} != 0);\n"
      | .k 's' => sin := sin ++ s!"  {lb} wiz_val t = {path}; wiz_inc(t); {lhs} = wiz_in_string(t); {rb}\n"
                  sfree := sfree ++ s!"  free((void *){lhs});\n"
                  sout := sout ++ s!"  fs[{i}] = wiz_out_string(c.{f} ? c.{f} : \"\");\n"
      -- a foreign pointer in a struct: borrowed while the call runs; one that comes back
      -- is not owned (no finalizer)
      | .k 'p' => sin := sin ++ s!"  {lhs} = wiz_in_ptr({path});\n"
                  sout := sout ++ s!"  fs[{i}] = wiz_out_ptr((void *)c.{f}, NULL);\n"
      -- a byte array of fixed size (`char f[N]`): copied, zero-padded or cut to size
      | .k 'y' => sin := sin ++ s!"  {lb} wiz_bytes *b = (wiz_bytes *){path}; size_t m = b->len < sizeof {lhs} ? b->len : sizeof {lhs};\n" ++
                    s!"    memset({lhs}, 0, sizeof {lhs}); if (m) memcpy({lhs}, b->data, m); {rb}\n"
                  sout := sout ++ s!"  {lb} wiz_bytes *b = (wiz_bytes *)wiz_bytes_empty(); b->len = b->cap = sizeof c.{f};\n" ++
                    s!"    b->data = (unsigned char *)malloc(b->len); memcpy(b->data, c.{f}, b->len); fs[{i}] = (wiz_val)b; {rb}\n"
      | .struct .. =>
        sin := sin ++ s!"  wiz_sin_{num fk}(&{lhs}, {path});\n"
        sfree := sfree ++ s!"  wiz_sfree_{num fk}(&{lhs});\n"
        sout := sout ++ s!"  fs[{i}] = wiz_sout_{num fk}(c.{f});\n"
      | _ => sout := sout ++ s!"  fs[{i}] = WIZ_BOX(0);\n"
    let build := if n ≤ 1 then "  return fs[0];\n" else
      s!"  wiz_val r = fs[{n - 1}];\n  for (int i = {n - 2}; i >= 0; i--) {lb} wiz_val p = wiz_ctor_new(0, 2); WIZ_SET(p, 0, fs[i]); WIZ_SET(p, 1, r); r = p; {rb}\n  return r;\n"
    out := out ++
      s!"static void wiz_sin_{id}({c} *c, wiz_val v) {lb}\n  memset(c, 0, sizeof *c);\n{sin}{rb}\n" ++
      s!"static void wiz_sfree_{id}({c} *c) {lb}\n  (void)c;\n{sfree}{rb}\n" ++
      s!"static wiz_val wiz_sout_{id}({c} c) {lb}\n  wiz_val fs[{max n 1}];\n{sout}{build}{rb}\n"
    seen := seen ++ [(k.toKey, id)]
  pure (out, seen)
where
  lb := "{"
  rb := "}"

/-- The headers of a struct kind (and of its nested structs). -/
partial def structHeaders : FKind → List String
  | .struct _ h fs => (if h == "" then [] else [h]) ++ fs.flatMap (structHeaders ·.2)
  | _ => []

/-- C glue for the foreign functions: their headers (or prototypes), and a marshalling
wrapper for each (`WIZ_API`, so the LLVM backend can call them). Headers already
included by `before` (the program's own C code) aren't included again. -/
def glue (keys : Array Name) (before : String := "") : String := Id.run do
  let mut includes : Array String := #[]
  let mut out := ""
  let sigs := keys.toList.filterMap fun key => (RVal.ExternSig.ofKey? key).map (key, ·)
  for (_, sig) in sigs do
    for h in (if sig.header == "" then [] else [sig.header]) ++ (sig.result :: sig.params).flatMap structHeaders do
      unless includes.contains h || (before.splitOn s!"#include <{h}>").length > 1 do includes := includes.push h
  let (helpers, nums) := structHelpers (sigs.flatMap fun (_, sig) => sig.result :: sig.params)
  let num (k : FKind) : Nat := ((nums.find? (·.1 == k.toKey)).map (·.2)).getD 0
  out := out ++ helpers
  for (key, sig) in sigs do
    if sig.header == "" && !sig.cname.startsWith "wiz_" then
      let ps := sig.params.filter (fun k => k != .k 'v' && k != .k 'e') |>.flatMap fun k =>
        if k == .k 'y' then ["const void *", "size_t"] else [ftype k]
      out := out ++ s!"extern {ftype sig.result} {sig.cname}({if ps.isEmpty then "void" else ", ".intercalate ps});\n"
    let n := sig.params.length
    let params := (List.range n).map (s!"wiz_val a{·}") ++ (if sig.io then ["wiz_val w"] else [])
    let mut body := ""
    let mut cargs : Array String := #[]
    for k in sig.params, i in [0:n] do
      match k with
      | .k 'n' => body := body ++ s!"  uint64_t c{i} = wiz_in_nat(a{i});\n"; cargs := cargs.push s!"c{i}"
      | .k 'u' => body := body ++ s!"  uint64_t c{i} = wiz_in_u64(a{i});\n"; cargs := cargs.push s!"c{i}"
      | .k 'f' => body := body ++ s!"  double c{i} = wiz_in_f64(a{i});\n"; cargs := cargs.push s!"c{i}"
      | .k 's' => body := body ++ s!"  char *c{i} = wiz_in_string(a{i});\n"; cargs := cargs.push s!"c{i}"
      | .k 'b' => body := body ++ s!"  int c{i} = wiz_in_bool(a{i});\n"; cargs := cargs.push s!"c{i}"
      | .k 'p' => body := body ++ s!"  void *c{i} = wiz_in_ptr(a{i});\n"; cargs := cargs.push s!"c{i}"
      -- (9i) a byte buffer: its data and length, borrowed for the call
      | .k 'y' => cargs := cargs.push s!"(const void *)((wiz_bytes *)a{i})->data" |>.push s!"(size_t)((wiz_bytes *)a{i})->len"
      | .k 'w' => cargs := cargs.push s!"a{i}"
      | .k 'e' => pure ()
      -- (9i) a struct by value: filled from the Wiz structure, which is released after the call
      | .struct c .. => body := body ++ s!"  {c} c{i}; wiz_sin_{num k}(&c{i}, a{i});\n"; cargs := cargs.push s!"c{i}"
      | _ => body := body ++ s!"  wiz_dec(a{i});\n"
    let call := s!"{sig.cname}({", ".intercalate cargs.toList})"
    body := body ++ match sig.result with
      | .k 'n' => s!"  wiz_val r = wiz_out_nat({call});\n"
      | .k 'u' => s!"  wiz_val r = wiz_out_u64({call});\n"
      | .k 'f' => s!"  wiz_val r = wiz_out_f64({call});\n"
      | .k 's' => s!"  wiz_val r = wiz_out_string({call});\n"
      | .k 'b' => s!"  wiz_val r = wiz_out_bool({call});\n"
      | .k 'p' =>
        let fin := if sig.fin == "" then "NULL" else s!"(void (*)(void *)){sig.fin}"
        s!"  wiz_val r = wiz_out_ptr((void *){call}, {fin});\n"
      | .k 'w' => s!"  wiz_val r = {call};\n"
      | .struct .. => s!"  wiz_val r = wiz_sout_{num sig.result}({call});\n"
      | _ => s!"  {call};\n  wiz_val r = WIZ_BOX(0);\n"
    for k in sig.params, i in [0:n] do
      if k == .k 's' then body := body ++ s!"  free(c{i});\n"
      -- a foreign pointer or a buffer is borrowed for the call: release it after
      if k == .k 'p' || k == .k 'y' then body := body ++ s!"  wiz_dec(a{i});\n"
      if let .struct .. := k then body := body ++ s!"  wiz_sfree_{num k}(&c{i});\n  wiz_dec(a{i});\n"
    body := body ++ (if sig.io then "  return wiz_io_result(r, w);\n" else "  return r;\n")
    out := out ++ s!"WIZ_API wiz_val {externWrapper key}({", ".intercalate params}) {lb}\n{body}{rb}\n"
  pure (String.join (includes.toList.map (s!"#include <{·}>\n")) ++ out)
where
  lb := "{"
  rb := "}"

/-- **Exercise 8.2.** Emit the C statements of a body (see the module docstring). A
join point's body goes after the code that jumps to it, under the label `jN:`; a
jump assigns the parameters (through temporaries, since arguments may overlap them)
and `goto`s the label. -/
partial def body (arities : Std.HashMap Name Nat) (joins : Std.HashMap JoinId (Array Var)) (b : Body)
    (ind : String := "  ") : String :=
  --<sol
  match b with
  | .vdecl x e rest => s!"{ind}{expr arities x e}\n{body arities joins rest ind}"
  | .case x alts =>
    let cases := alts.toList.zipIdx.map fun (a, i) =>
      s!"{ind}case {i}: {lb}\n{body arities joins a (ind ++ "  ")}{ind}{rb}\n"
    s!"{ind}switch (wiz_tag({var x})) {lb}\n{String.join cases}{ind}default: wiz_unreachable(); return 0;\n{ind}{rb}\n"
  | .ret x => s!"{ind}return {var x};\n"
  | .jdecl j ps jb k =>
    let joins := joins.insert j ps
    s!"{body arities joins k ind}{ind}j{j}: {lb}\n{body arities joins jb (ind ++ "  ")}{ind}{rb}\n"
  | .jmp j as =>
    let ps := (joins.get? j).getD #[]
    let tmps := as.toList.zipIdx.map fun (a, i) => s!"wiz_val t{i} = {var a}; "
    let sets := ps.toList.zipIdx.map fun (p, i) => s!"{var p} = t{i}; "
    s!"{ind}{lb} {String.join tmps}{String.join sets}goto j{j}; {rb}\n"
  | .dup x rest => s!"{ind}wiz_inc({var x});\n{body arities joins rest ind}"
  | .drop x rest => s!"{ind}wiz_dec({var x});\n{body arities joins rest ind}"
  | .unreachable => s!"{ind}wiz_unreachable(); return 0;\n"
where
  lb := "{"
  rb := "}"
  --|ex
  --| sorry
  --sol>

def signature (d : IR.Decl) : String :=
  let ps := if d.params.isEmpty then "void" else ", ".intercalate (d.params.toList.map (s!"wiz_val {var ·}"))
  s!"static wiz_val {mangle d.name}({ps})"

def decl (arities : Std.HashMap Name Nat) (d : IR.Decl) : String :=
  -- (a reuse token may be bound in several branches: declare it once)
  let locals := ((bound d.body).filter (!d.params.contains ·)).toList.eraseDups.toArray
  let decls := if locals.isEmpty then "" else s!"  wiz_val {", ".intercalate (locals.toList.map var)};\n"
  let boxedArgs := ", ".intercalate ((List.range d.params.size).map (s!"a[{·}]"))
  -- (a hoisted constant is built once, made immortal, and shared; threads may race to
  -- build it: the first to publish wins, a loser's copy stays immortal and unused)
  if d.name.startsWith "wiz.const." && d.params.isEmpty then
    s!"static wiz_val {mangle d.name}_build(void) {lb}\n{decls}{body arities {} d.body}{rb}\n" ++
    s!"{signature d} {lb} static wiz_val c = 0; wiz_val v = __atomic_load_n(&c, __ATOMIC_ACQUIRE); " ++
    s!"if (!v) {lb} wiz_val z = 0; v = {mangle d.name}_build(); wiz_immortal(v); " ++
    s!"if (!__atomic_compare_exchange_n(&c, &z, v, 0, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE)) v = z; {rb} " ++
    s!"wiz_inc(v); return v; {rb}\n" ++
    s!"static wiz_val {mangle d.name}_boxed(wiz_val *a) {lb} return {mangle d.name}(); {rb}\n"
  else
  s!"{signature d} {lb}\n{decls}{body arities {} d.body}{rb}\n" ++
  s!"static wiz_val {mangle d.name}_boxed(wiz_val *a) {lb} return {mangle d.name}({boxedArgs}); {rb}\n"
where
  lb := "{"
  rb := "}"

/-- A whole C program: the runtime, the foreign glue, the functions, and a `main` that
prints the result of the Wiz `main` (or, for `main : IO A`, runs it) and checks for
leaks. -/
def program (decls : Array IR.Decl) (io : Bool := false) (extra : String := "") : String :=
  let arities := decls.foldl (fun m d => m.insert d.name d.params.size) {}
  let protos := decls.toList.map fun d =>
    s!"{signature d};\nstatic wiz_val {mangle d.name}_boxed(wiz_val *a);\n"
  let finish := if io then "1" else "0"
  runtime ++ "\n/* ---- foreign functions ---- */\n\n" ++ extra ++ "\n" ++ glue (externs decls) extra ++
    "\n/* ---- generated ---- */\n\n" ++ String.join protos ++ "\n" ++
    String.join (decls.toList.map (decl arities ·)) ++
    s!"\nint main(int argc, char **argv) \{ wiz_set_args(argc, argv); return wiz_run_main({mangle "wiz.entry"}, {finish}); }\n"

end Wiz.C
