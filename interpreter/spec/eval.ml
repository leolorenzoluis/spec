open Values
open Types
open Instance
open Ast
open Source


(* Errors *)

module Link = Error.Make ()
module Trap = Error.Make ()
module Crash = Error.Make ()

exception Link = Link.Error
exception Trap = Trap.Error
exception Crash = Crash.Error (* failure that cannot happen in valid code *)

let memory_error at = function
  | Memory.Bounds -> "out of bounds memory access"
  | Memory.SizeOverflow -> "memory size overflow"
  | Memory.SizeLimit -> "memory size limit reached"
  | Memory.Type -> Crash.error at "type mismatch at memory access"
  | exn -> raise exn

let numeric_error at = function
  | Numeric_error.IntegerOverflow -> "integer overflow"
  | Numeric_error.IntegerDivideByZero -> "integer divide by zero"
  | Numeric_error.InvalidConversionToInteger -> "invalid conversion to integer"
  | Eval_numeric.TypeError (i, v, t) ->
    Crash.error at
      ("type error, expected " ^ Types.string_of_value_type t ^ " as operand " ^
       string_of_int i ^ ", got " ^ Types.string_of_value_type (type_of v))
  | exn -> raise exn


(* Administrative Expressions & Configurations *)

(*
 * Execution is defined by how instructions transform a program configuration.
 * Configurations are given as tuples (vv, es, vs):
 *
 * vv : value stack - the operand stack (local to the current block)
 * es : instr list  - the remaining instructions (in the current block)
 * vs : value list - the locals (in the current function)
 *
 * The global store is left implicit and accessed through the instance.
 *)

type 'a stack = 'a list

type admin_seq = value stack * admin_instr list
and admin_instr = admin_instr' phrase
and admin_instr' =
  | Plain of instr'
  | Trapped of string
  | Break of int32 * value stack
  | Label of stack_type * admin_instr list * admin_seq
  | Local of instance * value ref list * admin_seq
  | Invoke of closure

let plain e = Plain e.it @@ e.at

let lookup category list x =
  try Lib.List32.nth list x.it with Failure _ ->
    Crash.error x.at ("undefined " ^ category ^ " " ^ Int32.to_string x.it)

let type_ (inst : instance) x = lookup "type" inst.module_.it.types x
let func (inst : instance) x = lookup "function" inst.funcs x
let table (inst : instance) x = lookup "table" inst.tables x
let memory (inst : instance) x = lookup "memory" inst.memories x
let global (inst : instance) x = lookup "global" inst.globals x
let local (vrs : value ref list) x = lookup "local" vrs x

let elem inst x i at =
  match Table.load (table inst x) i with
  | Table.Uninitialized ->
    Trap.error at ("uninitialized element " ^ Int32.to_string i)
  | f -> f
  | exception Table.Bounds ->
    Trap.error at ("undefined element " ^ Int32.to_string i)

let func_elem inst x i at =
  match elem inst x i at with
  | Func f -> f
  | _ -> Crash.error at ("type mismatch for element " ^ Int32.to_string i)

let func_type_of t =
  match t with
  | AstFunc (inst, f) -> lookup "type" (!inst).module_.it.types f.it.ftype
  | HostFunc (t, _) -> t

let take n (vs : 'a stack) at =
  try Lib.List.take n vs with Failure _ -> Crash.error at "stack underflow"

let drop n (vs : 'a stack) at =
  try Lib.List.drop n vs with Failure _ -> Crash.error at "stack underflow"


(* Evaluation *)

(*
 * Conventions:
 *   e  : instr
 *   v  : value
 *   es : instr list
 *   vs : value stack
 *   vrs : value ref list
 *)

let i32 v at =
  match v with
  | I32 i -> i
  | _ -> Crash.error at "type error: i32 value expected"

let rec step_instr k inst vrs (vs, e : value stack * admin_instr) : admin_seq =
  match e.it with
  | Plain e' ->
    (match e', vs with
    | Unreachable, _ ->
      vs, [Trapped "unreachable executed" @@ e.at]

    | Nop, vs ->
      vs, []

    | Block (ts, es'), vs ->
      vs, [Label (ts, [], ([], List.map plain es')) @@ e.at]

    | Loop (ts, es'), vs ->
      vs, [Label (ts, [e], ([], List.map plain es')) @@ e.at]

    | If (ts, es1, es2), I32 0l :: vs' ->
      vs', [Plain (Block (ts, es2)) @@ e.at]

    | If (ts, es1, es2), I32 i :: vs' ->
      vs', [Plain (Block (ts, es1)) @@ e.at]

    | Br x, vs ->
      [], [Break (x.it, vs) @@ e.at]

    | BrIf x, I32 0l :: vs' ->
      vs', []

    | BrIf x, I32 i :: vs' ->
      vs', [Plain (Br x) @@ e.at]

    | BrTable (xs, x), I32 i :: vs' when I32.ge_u i (Lib.List32.length xs) ->
      vs', [Plain (Br x) @@ e.at]

    | BrTable (xs, x), I32 i :: vs' ->
      vs', [Plain (Br (Lib.List32.nth xs i)) @@ e.at]

    | Return, vs ->
      vs, [Plain (Br ((Int32.of_int (k - 1)) @@ e.at)) @@ e.at]

    | Call x, vs ->
      vs, [Invoke (func inst x) @@ e.at]

    | CallIndirect x, I32 i :: vs ->
      let clos = func_elem inst (0l @@ e.at) i e.at in
      if type_ inst x <> func_type_of clos then
        Trap.error e.at "indirect call signature mismatch";
      vs, [Invoke clos @@ e.at]

    | Drop, v :: vs' ->
      vs', []

    | Select, I32 0l :: v2 :: v1 :: vs' ->
      v2 :: vs', []

    | Select, I32 i :: v2 :: v1 :: vs' ->
      v1 :: vs', []

    | GetLocal x, vs ->
      !(local vrs x) :: vs, []

    | SetLocal x, v :: vs' ->
      local vrs x := v;
      vs', []

    | TeeLocal x, v :: vs' ->
      local vrs x := v;
      v :: vs', []

    | GetGlobal x, vs ->
      !(global inst x) :: vs, []

    | SetGlobal x, v :: vs' ->
      global inst x := v;
      vs', []

    | Load {offset; ty; sz; _}, I32 i :: vs' ->
      let mem = memory inst (0l @@ e.at) in
      let addr = I64_convert.extend_u_i32 i in
      (try
        let v =
          match sz with
          | None -> Memory.load mem addr offset ty
          | Some (sz, ext) -> Memory.load_packed sz ext mem addr offset ty
        in v :: vs', []
      with exn -> vs', [Trapped (memory_error e.at exn) @@ e.at])

    | Store {offset; sz; _}, v :: I32 i :: vs' ->
      let mem = memory inst (0l @@ e.at) in
      let addr = I64_convert.extend_u_i32 i in
      (try
        (match sz with
        | None -> Memory.store mem addr offset v
        | Some sz -> Memory.store_packed sz mem addr offset v
        );
        vs', []
      with exn -> vs', [Trapped (memory_error e.at exn) @@ e.at]);

    | CurrentMemory, vs ->
      let mem = memory inst (0l @@ e.at) in
      I32 (Memory.size mem) :: vs, []

    | GrowMemory, I32 delta :: vs' ->
      let mem = memory inst (0l @@ e.at) in
      let old_size = Memory.size mem in
      let result =
        try Memory.grow mem delta; old_size
        with Memory.SizeOverflow | Memory.SizeLimit | Memory.OutOfMemory -> -1l
      in I32 result :: vs', []

    | Const v, vs ->
      v.it :: vs, []

    | Test testop, v :: vs' ->
      (try value_of_bool (Eval_numeric.eval_testop testop v) :: vs', []
      with exn -> vs', [Trapped (numeric_error e.at exn) @@ e.at])

    | Compare relop, v2 :: v1 :: vs' ->
      (try value_of_bool (Eval_numeric.eval_relop relop v1 v2) :: vs', []
      with exn -> vs', [Trapped (numeric_error e.at exn) @@ e.at])

    | Unary unop, v :: vs' ->
      (try Eval_numeric.eval_unop unop v :: vs', []
      with exn -> vs', [Trapped (numeric_error e.at exn) @@ e.at])

    | Binary binop, v2 :: v1 :: vs' ->
      (try Eval_numeric.eval_binop binop v1 v2 :: vs', []
      with exn -> vs', [Trapped (numeric_error e.at exn) @@ e.at])

    | Convert cvtop, v :: vs' ->
      (try Eval_numeric.eval_cvtop cvtop v :: vs', []
      with exn -> vs', [Trapped (numeric_error e.at exn) @@ e.at])

    | _ ->
      Crash.error e.at "missing or ill-typed operand on stack"
    )

  | Trapped msg ->
    assert false

  | Break (k, vs) ->
    Crash.error e.at "undefined label"

  | Label (ts, es0, (vs', [])) ->
    vs' @ vs, []

  | Label (ts, es0, (vs', {it = Trapped msg; at} :: es')) ->
    vs, [Trapped msg @@ at]

  | Label (ts, es0, (vs', {it = Break (0l, vs0); at} :: es')) ->
    take (List.length ts) vs0 e.at @ vs', es0

  | Label (ts, es0, (vs', {it = Break (k, vs0); at} :: es')) ->
    vs, [Break (Int32.sub k 1l, vs0) @@ at]

  | Label (ts, es0, seq) ->
    vs, [Label (ts, es0, step_seq (k + 1) inst vrs seq) @@ e.at]

  | Local (inst', vrs', (vs', [])) ->
    vs' @ vs, []

  | Local (inst', vrs', (vs', {it = Trapped msg; at} :: es')) ->
    vs, [Trapped msg @@ at]

  | Local (inst', vrs', seq) ->
    vs, [Local (inst', vrs', step_seq 0 inst' vrs' seq) @@ e.at]

  | Invoke clos ->
    let FuncType (ins, out) = func_type_of clos in
    let n = List.length ins in
    let args, vs' = take n vs e.at, drop n vs e.at in
    (match clos with
    | AstFunc (inst', f) ->
      let vrs' =
        List.map ref (List.rev args @ List.map default_value f.it.locals) in
      vs', [Local (!inst', vrs', ([], [Plain (Block (out, f.it.body)) @@ f.at])) @@ e.at]

    | HostFunc (t, f) ->
      try List.rev (f (List.rev args)) @ vs', []
      with Crash (_, msg) -> Crash.error e.at msg
    )

and step_seq k inst vrs (vs, es : admin_seq) : admin_seq =
  match es with
  | [] ->
    assert false

  | {it = Trapped msg; at} :: es' ->
    [], [Trapped msg @@ at]

  | e :: es' ->
    let vs', es'' = step_instr k inst vrs (vs, e) in
    vs', es'' @ es'

let rec eval_seq inst (vs, es : admin_seq) : value stack =
  match es with
  | [] ->
    vs

  | {it = Trapped msg; at} :: es' ->
    Trap.error at msg

  | es ->
    eval_seq inst (step_seq 0 inst [] (vs, es))


(* Functions & Constants *)

let eval_func (clos : closure) (vs : value list) at : value list =
  let FuncType (ins, out) = func_type_of clos in
  if List.length vs <> List.length ins then
    Crash.error at "wrong number of arguments";
  List.rev (eval_seq (instance (empty_module @@ at)) (vs, [Invoke clos @@ at]))

let eval_const inst const =
  List.hd (eval_seq inst ([], List.map plain const.it))


(* Modules *)

let create_closure (m : module_) (f : func) =
  AstFunc (ref (instance m), f)

let create_table (tab : table) =
  let {ttype = TableType (lim, t)} = tab.it in
  Table.create t lim

let create_memory (mem : memory) =
  let {mtype = MemoryType lim} = mem.it in
  Memory.create lim

let create_global (glob : global) =
  let {gtype = GlobalType (t, _); _} = glob.it in
  ref (default_value t)

let init_closure (inst : instance) (clos : closure) =
  match clos with
  | AstFunc (inst_ref, _) -> inst_ref := inst
  | _ -> assert false

let init_table (inst : instance) (seg : table_segment) =
  let {index; offset = e; init} = seg.it in
  let tab = table inst index in
  let offset = i32 (eval_const inst e) e.at in
  try Table.blit tab offset (List.map (fun x -> Func (func inst x)) init)
  with Table.Bounds -> Link.error seg.at "elements segment does not fit table"

let init_memory (inst : instance) (seg : memory_segment) =
  let {index; offset = e; init} = seg.it in
  let mem = memory inst index in
  let offset = i32 (eval_const inst e) e.at in
  let offset64 = Int64.(logand (of_int32 offset) 0xffffffffL) in
  try Memory.blit mem offset64 init
  with Memory.Bounds -> Link.error seg.at "data segment does not fit memory"

let init_global (inst : instance) (ref : value ref) (glob : global) =
  let {value = e; _} = glob.it in
  ref := eval_const inst e

let check_limits actual expected at =
  if I32.lt_u actual.min expected.min then
    Link.error at "actual size smaller than declared";
  if
    match actual.max, expected.max with
    | _, None -> false
    | None, Some _ -> true
    | Some i, Some j -> I32.gt_u i j
  then Link.error at "maximum size larger than declared"

let add_import (ext : extern) (im : import) (inst : instance) : instance =
  let {ikind; _} = im.it in
  match ext, ikind.it with
  | ExternalFunc clos, FuncImport x when func_type_of clos = type_ inst x ->
    {inst with funcs = clos :: inst.funcs}
  | ExternalTable tab, TableImport (TableType (lim, t))
    when Table.elem_type tab = t ->
    check_limits (Table.limits tab) lim ikind.at;
    {inst with tables = tab :: inst.tables}
  | ExternalMemory mem, MemoryImport (MemoryType lim) ->
    check_limits (Memory.limits mem) lim ikind.at;
    {inst with memories = mem :: inst.memories}
  | ExternalGlobal v, GlobalImport (GlobalType (t, _)) when type_of v = t ->
    {inst with globals = ref v :: inst.globals}
  | _ ->
    Link.error ikind.at "type mismatch"

let add_export (inst : instance) (ex : export) (map : extern ExportMap.t)
  : extern ExportMap.t =
  let {name; ekind; item} = ex.it in
  let ext =
    match ekind.it with
    | FuncExport -> ExternalFunc (func inst item)
    | TableExport -> ExternalTable (table inst item)
    | MemoryExport -> ExternalMemory (memory inst item)
    | GlobalExport -> ExternalGlobal !(global inst item)
  in ExportMap.add name ext map

let init (m : module_) (exts : extern list) : instance =
  let
    { imports; tables; memories; globals; funcs;
      exports; elems; data; start; _
    } = m.it
  in
  if List.length exts <> List.length imports then
    Link.error m.at "wrong number of imports provided for initialisation";
  let fs = List.map (create_closure m) funcs in
  let gs = List.map create_global globals in
  let inst =
    List.fold_right2 add_import exts imports
      { (instance m) with
        funcs = fs;
        tables = List.map create_table tables;
        memories = List.map create_memory memories;
        globals = gs;
      }
  in
  List.iter2 (init_global inst) gs globals;
  List.iter (init_closure inst) fs;
  List.iter (init_table inst) elems;
  List.iter (init_memory inst) data;
  Lib.Option.app (fun x -> ignore (eval_func (func inst x) [] x.at)) start;
  {inst with exports = List.fold_right (add_export inst) exports inst.exports}

let invoke (clos : closure) (vs : value list) : value list =
  (try eval_func clos vs no_region
  with Stack_overflow -> Trap.error no_region "call stack exhausted")
