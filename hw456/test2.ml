#use "topfind";;
#thread;;
#require "threads";;
open Mutex;;
#require "batteries";;
#mod_use "./S.ml";;
#mod_use "./T.ml";;
#mod_use "./G.ml";;
open T
(***********************************)
(* abstract syntax definition of S *)
(***********************************)

type program = block
and block = decls * stmts
and decls = decl list
and decl  = typ * id 
and typ   = TINT | TARR of int
and stmts = stmt list 
and id    = string
and stmt  = ASSIGN of lv * exp       (* lv = exp *)
          | IF of exp * stmt * stmt 
          | WHILE of exp * stmt
          | DOWHILE of stmt * exp
          | READ of id
          | PRINT of exp 
          | BLOCK of block
and lv   = ID of id | ARR of id * exp
and exp  =  NUM of int
          | LV of lv
          | ADD of exp * exp
          | SUB of exp * exp
          | MUL of exp * exp
          | DIV of exp * exp
          | MINUS of exp         
          | NOT of exp
          | LT of exp * exp 
          | LE of exp * exp 
          | GT of exp * exp 
          | GE of exp * exp 
          | EQ of exp * exp 
          | AND of exp * exp
          | OR  of exp * exp;;

(*************************************)
(*        interpreter for S          *)
(*************************************)

exception RuntimeErr of string;;

type loc = VAR of string | ADDR of base * offset
and base = int
and offset = int;;
type value = INT of int | ARRAY of base * size
and size = int;;

let str_of_loc l = 
  match l with
  | VAR x -> x
  | ADDR (x,n) -> "(l"^(string_of_int x)^","^(string_of_int n)^")";;

let new_loc = ref 1;;
module Memory = struct
  type t = (loc, value) BatMap.t
  let empty = BatMap.empty
  let bind l v m = BatMap.add l v m
  let lookup l m = try BatMap.find l m 
                   with _ -> INT 0 (* default value for unbound locations *)
  let alloc x size m = 
    if size <= 0 then raise (RuntimeErr "alloc with non-positive size")
    else begin
    new_loc := !new_loc + 1;
    let rec helper offset m = 
      if offset = size then m
      else helper (offset+1) (bind (ADDR (!new_loc,offset)) (INT 0) m) in
      bind (VAR x) (ARRAY (!new_loc, size)) (helper 0 m)
    end
end
;;
type mem = Memory.t;;

let list_fold f l a = List.fold_left (fun a e -> f e a) a l;;

let rec run_block :block -> mem -> mem
=fun (decls,stmts) m ->
  let m' = run_decls decls m in
  let m'' = run_stmts stmts m' in
    m''

and run_decls : decls -> mem -> mem
=fun decls m -> list_fold run_decl decls m

and run_decl : decl -> mem -> mem
=fun (typ,x) m -> 
  match typ with
  | TINT -> Memory.bind (VAR x) (INT 0) m
  | TARR n -> Memory.alloc x n m

and run_stmts : stmts -> mem -> mem
=fun stmts m -> list_fold run_stmt stmts m

and run_stmt : stmt -> mem -> mem
=fun stmt m ->
  match stmt with
  | ASSIGN (lv, e) -> Memory.bind (eval_lv lv m) (eval e m) m
  | IF (e,stmt1,stmt2) ->
    ( match eval e m with
    | INT 0 -> run_stmt stmt2 m
    | INT _ -> run_stmt stmt1 m
    | _ -> raise (RuntimeErr "if: condition must be integer"))
  | WHILE (e,stmt) ->
    let rec helper m =
      match eval e m with
      | INT 0 -> m
      | INT _ -> helper (run_stmt stmt m) 
      | _ -> raise (RuntimeErr "while: condition must be integer") in
      helper m
  | DOWHILE (stmt, exp) -> run_stmts [stmt; WHILE (exp, stmt)] m
  | READ x -> Memory.bind (VAR x) (INT (read_int ())) m
  | PRINT e -> 
    (match eval e m with
    | INT n -> print_endline (string_of_int n); m
    | _ -> raise (RuntimeErr "print: arg must be integer"))
  | BLOCK b -> run_block b m

and eval_int : exp -> mem -> int 
=fun e m ->
  match eval e m with
  | INT n -> n
  | _ -> raise (RuntimeErr "Operands must evaluate to integer")

and eval : exp -> mem -> value
=fun e m ->
  match e with
  | NUM n -> INT n
  | LV lv -> Memory.lookup (eval_lv lv m) m
  | ADD (e1,e2) -> INT ((eval_int e1 m) + (eval_int e2 m))
  | SUB (e1,e2) -> INT ((eval_int e1 m) - (eval_int e2 m))
  | MUL (e1,e2) -> INT ((eval_int e1 m) * (eval_int e2 m))
  | DIV (e1,e2) -> 
    begin 
      let divisor = eval_int e2 m in 
        if divisor = 0 then raise (RuntimeErr "Divide by zero")
        else INT ((eval_int e1 m) / divisor)
    end 
  | MINUS e -> INT (-(eval_int e m))
  | NOT e -> 
    (match eval_int e m with
    | 0 -> INT 1
    | _ -> INT 0)
  | LT (e1,e2) -> if eval_int e1 m <  eval_int e2 m then INT 1 else INT 0
  | LE (e1,e2) -> if eval_int e1 m <= eval_int e2 m then INT 1 else INT 0
  | GT (e1,e2) -> if eval_int e1 m >  eval_int e2 m then INT 1 else INT 0
  | GE (e1,e2) -> if eval_int e1 m >= eval_int e2 m then INT 1 else INT 0
  | EQ (e1,e2) -> if eval_int e1 m =  eval_int e2 m then INT 1 else INT 0
  | AND (e1,e2) -> 
    (match eval_int e1 m, eval_int e2 m with
    |0,_ 
    |_,0 -> INT 0
    |_,_ -> INT 1)
  | OR (e1,e2) ->
    (match eval_int e1 m, eval_int e2 m with
    |0,0 -> INT 0
    |_,_ -> INT 1)

and eval_lv : lv -> mem -> loc
=fun lv m ->
  match lv with
  | ID x -> VAR x
  | ARR (x,e) -> 
    (match Memory.lookup (VAR x) m with
    | ARRAY (base,size) -> 
      (match eval e m with
       | INT idx -> 
         if idx < 0 || idx >= size then raise (RuntimeErr ("Array out of bounds: offset: " ^
         string_of_int idx ^ " size: " ^ string_of_int size)) 
         else ADDR (base, idx)
       | _ -> raise (RuntimeErr ("index must be an integer")))
    | _ -> raise (RuntimeErr (x ^ " must be an array")))

        ;;
let execute : program -> unit
=fun pgm -> ignore (run_block pgm Memory.empty)    ;;      

(*************************************)
(* pretty printer for the S langauge *)
(*************************************)

let p x = print_string (x);;

let rec p_indent n = if n = 0 then () else (p " "; p_indent (n-1));;

let rec p_typ t =
  match t with
  | TINT  -> p "int"
  | TARR (n) -> p "int"; p"[";print_int n; p"]"

and p_lv lv = p (string_of_lv lv)
and p_exp e = p (string_of_exp e)

and string_of_lv lv = 
  match lv with
  | ID x -> x 
  | ARR (x, e) -> x ^ "[" ^ string_of_exp e ^ "]"

and string_of_exp e = 
  begin
  match e with
  | ADD (e1,e2) -> string_of_exp e1 ^ " + " ^ string_of_exp e2
  | SUB (e1,e2) -> string_of_exp e1 ^ " - " ^ string_of_exp e2
  | MUL (e1,e2) -> string_of_exp e1 ^ " * " ^ string_of_exp e2
  | DIV (e1,e2) -> string_of_exp e1 ^ " / " ^ string_of_exp e2
  | MINUS e -> "-" ^ string_of_exp e
  | LV lv -> string_of_lv lv
  | NUM i -> string_of_int i
  | LT (e1,e2) -> string_of_exp e1 ^ " < " ^ string_of_exp e2
  | LE (e1,e2) -> string_of_exp e1 ^ " <= " ^ string_of_exp e2
  | GT (e1,e2) -> string_of_exp e1 ^ " > " ^ string_of_exp e2
  | GE (e1,e2) -> string_of_exp e1 ^ " >= " ^ string_of_exp e2
  | EQ (e1,e2) -> string_of_exp e1 ^ " == " ^ string_of_exp e2
  | NOT e -> "!(" ^ string_of_exp e ^ ")"
  | AND (e1,e2) -> string_of_exp e1 ^ " && " ^ string_of_exp e2
  | OR (e1,e2) -> string_of_exp e1 ^ " || " ^ string_of_exp e2
  end
  
and p_decl : int -> decl -> unit
=fun indent (typ,var) -> 
  p_indent indent;
  p_typ typ; p " "; p var; p ";"

and p_stmt : int -> stmt -> unit
=fun indent stmt  -> 
  p_indent indent;
  begin
  match stmt with
  | ASSIGN (lv, exp) -> p_lv lv; p " = "; p_exp exp; p ";"
  | IF (bexp,stmt1,stmt2) -> p "if "; p_exp bexp; p ""; p_stmt indent stmt1; p "else"; p_stmt indent stmt2
  | WHILE (b, s) -> p "while "; p_exp b; p ""; p_stmt indent s
  | DOWHILE (s,b) -> p "do"; p_stmt (indent+1) s; p_indent indent; p "while"; p_exp b; p";"
  | PRINT e -> p "print "; p_exp e; p ""; p";"
  | READ x -> p "read "; p x; p ""; p";"
  | BLOCK b -> p_block indent b
  end;
  

and p_decls : int -> decls -> unit
=fun indent decls -> List.iter (fun decl -> p_decl indent decl; p "\n") decls

and p_stmts : int -> stmts -> unit
=fun indent stmts -> List.iter (fun stmt -> p_stmt indent stmt; p "\n") stmts

and p_block : int -> block -> unit
=fun indent (decls,stmts) ->
  p_indent indent; p "{\n";
  p_decls (indent + 1) decls;
  p_stmts (indent + 1) stmts;
  p_indent indent; p "}\n" 
;;
let pp : program -> unit
=fun b -> p_block 0 b;;


(* 프로그램 전체: decls * stmts *)
let my_prog =
  ( 
    (* decls: 변수 선언부 *)
    [ (TARR 10, "arr")   (* int[10] arr; *)
    ; (TINT,   "i")      (* int i; *)
    ; (TINT,   "j")      (* int j; *)
    ],

    (* stmts: 문장부 *)
    [ (* i = 0; *)
      ASSIGN (ID "i", NUM 0);

      (* j = 0; *)
      ASSIGN (ID "j", NUM 0);

      (* while (i < 10) { … } *)
      WHILE (
        (* 조건: i < 10 *)
        LT (LV (ID "i"), NUM 10),

        (* 본문: decls = [], stmts = [ arr[i]=i; i=i+1; j=j+1 ] *)
        BLOCK (
          [],  (* 이 블록 내부에 추가 선언은 없음 *)
          [ (* arr[i] = i; *)
            ASSIGN (
              ARR ("arr", LV (ID "i")),   (* 좌변: arr[i] *)
              LV   (ID "i")               (* 우변: i *)
            );
            (* i = i + 1; *)
            ASSIGN (
              ID "i",
              ADD (LV (ID "i"), NUM 1)
            );
            (* j = j + 1; *)
            ASSIGN (
              ID "j",
              ADD (LV (ID "j"), NUM 1)
            )
          ]
        )
      );

      (* print(i); *)
      PRINT (LV (ID "i"))
    ]
  );;
let _ = execute my_prog;;

exception Not_implemented;;

let tmp_index = ref 0;;
let label_index = ref 1;;
let new_temp() = tmp_index := !tmp_index + 1; ".t" ^ (string_of_int !tmp_index);;
let new_label() = label_index := !label_index + 1; !label_index;;

let rec trans_e: exp -> (T.var* T.program) = 
fun e -> 
  match e with
  | NUM n -> 
    let new_t = new_temp () in 
    (new_t, [(0 ,COPYC(new_t, n))])

  | LV lv ->
    (match lv with
    | ID x -> 
      let new_t = new_temp () in 
      (new_t, [(0 ,COPY(new_t, x))])

    | ARR (x, e)-> 
      let (t1, code) = trans_e e in 
      let new_t2 = new_temp () in 
      (new_t2, code@[(0, LOAD(new_t2, (x, t1)))])
    )

  (*Binary op*)
  | ADD(e1, e2) -> 
    let (t1, code1) = trans_e e1 in 
    let (t2, code2) = trans_e e2 in 
    let new_t3 = new_temp () in 
    (new_t3, code1@code2@[(0, ASSIGNV(new_t3, ADD, t1, t2))])
    
  | SUB(e1, e2) -> 
    let (t1, code1) = trans_e e1 in 
    let (t2, code2) = trans_e e2 in 
    let new_t3 = new_temp () in 
    (new_t3, code1@code2@[(0, ASSIGNV(new_t3, SUB, t1, t2))])

  | MUL(e1, e2) -> 
    let (t1, code1) = trans_e e1 in 
    let (t2, code2) = trans_e e2 in 
    let new_t3 = new_temp () in 
    (new_t3, code1@code2@[(0, ASSIGNV(new_t3, MUL, t1, t2))])

  | DIV(e1, e2) -> 
    let (t1, code1) = trans_e e1 in 
    let (t2, code2) = trans_e e2 in 
    let new_t3 = new_temp () in 
    (new_t3, code1@code2@[(0, ASSIGNV(new_t3, DIV, t1, t2))])

  | LT(e1, e2) -> 
    let (t1, code1) = trans_e e1 in 
    let (t2, code2) = trans_e e2 in 
    let new_t3 = new_temp () in 
    (new_t3, code1@code2@[(0, ASSIGNV(new_t3, LT, t1, t2))])

  | LE(e1, e2) -> 
    let (t1, code1) = trans_e e1 in 
    let (t2, code2) = trans_e e2 in 
    let new_t3 = new_temp () in 
    (new_t3, code1@code2@[(0, ASSIGNV(new_t3, LE, t1, t2))])

  | GT(e1, e2) -> 
    let (t1, code1) = trans_e e1 in 
    let (t2, code2) = trans_e e2 in 
    let new_t3 = new_temp () in 
    (new_t3, code1@code2@[(0, ASSIGNV(new_t3, GT, t1, t2))])

  | GE(e1, e2) -> 
    let (t1, code1) = trans_e e1 in 
    let (t2, code2) = trans_e e2 in 
    let new_t3 = new_temp () in 
    (new_t3, code1@code2@[(0, ASSIGNV(new_t3, GE, t1, t2))])

  | EQ(e1, e2) -> 
    let (t1, code1) = trans_e e1 in 
    let (t2, code2) = trans_e e2 in 
    let new_t3 = new_temp () in 
    (new_t3, code1@code2@[(0, ASSIGNV(new_t3, EQ, t1, t2))])

  | AND(e1, e2) -> 
    let (t1, code1) = trans_e e1 in 
    let (t2, code2) = trans_e e2 in 
    let new_t3 = new_temp () in 
    (new_t3, code1@code2@[(0, ASSIGNV(new_t3, AND, t1, t2))])

  | OR(e1, e2) -> 
    let (t1, code1) = trans_e e1 in 
    let (t2, code2) = trans_e e2 in 
    let new_t3 = new_temp () in 
    (new_t3, code1@code2@[(0, ASSIGNV(new_t3, OR, t1, t2))])

  | MINUS(e) -> 
    let (t1, code1) = trans_e e in 
    let new_t2 = new_temp () in 
    (new_t2, code1@[(0, ASSIGNU(new_t2, MINUS, t1))])

  | NOT(e) -> 
    let (t1, code1) = trans_e e in 
    let new_t2 = new_temp () in 
    (new_t2, code1@[(0, ASSIGNU(new_t2, NOT, t1))]);;

let trans_d: decl->T.program = 
fun (t, id) ->
  match t with
  | TINT -> [(0, COPYC(id, 0))]
  | TARR(n) ->[(0, ALLOC(id, n))];;

let rec trans_s: stmt -> T.program = 
fun s ->
  match s with 
  | ASSIGN(lv, e)->
    (match lv with
    | ID x -> 
      let (t1, code1) = trans_e e in 
      code1@[(0, COPY(x, t1))]

    | ARR(x,e1)->
      let (t1, code1) = trans_e e1 in 
      let (t2, code2) = trans_e e in 
      code1@code2@[(0, STORE((x, t1), t2))])

  | IF(e, stmt1, stmt2) -> 
    let (t1, code1) = trans_e e in 
    let code_t = trans_s stmt1 in 
    let code_f = trans_s stmt2 in 
    let l_t = new_label () in 
    let l_f = new_label () in 
    let l_x = new_label () in 
    code1@[(0, CJUMP(t1, l_t))]@[(0, UJUMP l_f)]@[(l_t, SKIP)]@code_t@[(0, UJUMP l_x)]@[(l_f, SKIP)]@code_f@[(0, UJUMP l_x)]@[(l_x, SKIP)]
    

  | WHILE(e, stmt) -> 
    let (t1, code1) = trans_e e in 
    let code_b = trans_s stmt in 
    let l_e = new_label () in 
    let l_x = new_label () in 
    [(l_e, SKIP)]@code1@[(0, CJUMPF(t1, l_x))]@code_b@[(0, UJUMP l_e)]@[(l_x, SKIP)]
    

  | DOWHILE(stmt, e) -> 
    (trans_s(stmt))@(trans_s(WHILE(e, stmt)))

  | READ x -> [(0, READ(x))]

  | PRINT e -> 
    let (t1, code1) = trans_e e in 
    code1@[(0, WRITE t1)]
  
  | BLOCK b -> 
    trans_b b 


and trans_b = fun (d_list, s_list)->
  let d_code = List.fold_left (fun acc d-> acc@(trans_d d)) [] d_list in 
  let s_code = List.fold_left (fun acc s-> acc@(trans_s s)) [] s_list in
  d_code@s_code
;;

let test_t = (trans_b my_prog)@[(0, HALT)];;

let _ = T.pp test_t;;