#use "topfind";;
#thread;;
#require "threads";;
open Mutex;;
#require "batteries";;
#require "base";; 
#mod_use "./S.ml";;
#mod_use "./T.ml";;
#mod_use "./G.ml";;
#mod_use "./Utils.ml";;
open Utils;;
open Base;;
open Batteries;;
open S ;;

type id = string;;

module type Node = sig
  type instr = 
  | I_alloc of id * int 
  | I_assign of lv * exp 
  | I_assume of exp 
  | I_skip
  | I_read of id 
  | I_print of exp 
  type t 
  val create_alloc : id -> int -> t  
  val create_assign : lv -> exp -> t 
  val create_assume : exp -> t 
  val create_skip : unit -> t 
  val create_read : id -> t 
  val create_print : exp -> t 
  val get_nodeid : t -> int 
  val get_instr : t -> instr 
  val to_string : t -> string
  val compare : t -> t -> int   
end;;

module Node : Node = struct
  type instr = 
  | I_alloc of id * int 
  | I_assign of lv * exp 
  | I_assume of exp 
  | I_skip
  | I_read of id 
  | I_print of exp 
  type t = int * instr
  let new_id : unit -> int =
    let id =  ref 0 in 
      fun _ -> (id := !id + 1; !id)
  let create_alloc x n = (new_id(), I_alloc (x, n))
  let create_assign x a = (new_id(), I_assign (x, a))
  let create_assume b = (new_id(), I_assume b)
  let create_skip () = (new_id(), I_skip)
  let create_read x = (new_id(), I_read x)
  let create_print e = (new_id(), I_print e)
  let get_nodeid (id, _) = id
  let get_instr (_, instr) = instr
  let compare = Stdlib.compare
  let to_string n = 
    match n with
    | (id, I_alloc (x, n)) -> string_of_int id ^ ": " ^ " " ^ x ^ " := alloc " ^ string_of_int n
    | (id, I_assign (lv, e)) -> string_of_int id ^ ": " ^ " " ^ string_of_lv lv ^ " := " ^ string_of_exp e
    | (id, I_assume b) -> string_of_int id ^ ": " ^ "assume"  ^ " " ^ string_of_exp b
    | (id, I_skip) -> string_of_int id ^ ": " ^ "skip"
    | (id, I_read x) -> string_of_int id ^ ": " ^ "read " ^ x 
    | (id, I_print e) -> string_of_int id ^ ": " ^ "print " ^ string_of_exp e
end;;

module NodeSet = Set.Make(Node);;
module NodeMap = Map.Make(Node);;

module type Cfg = sig 
  type t 
  val empty : t 
  val nodesof : t -> Node.t list 
  val succs : Node.t -> t -> NodeSet.t
  val preds : Node.t -> t -> NodeSet.t
  val add_node : Node.t -> t -> t
  val add_nodes : Node.t list -> t -> t
  val add_edge : Node.t -> Node.t -> t -> t
  val add_loophead : Node.t -> t -> t 
  val is_loophead : Node.t -> t -> bool 
  val get_entry : t -> Node.t 
  val get_exit : t -> Node.t
  val remove_node : Node.t -> t -> t 
  val remove_edge : Node.t -> Node.t -> t -> t 
  val remove_unnecessary_skips : t -> t 
  val print : t -> unit 
  val dot : t -> unit
end;;

module Cfg : Cfg = struct
  type t = { 
    nodes : NodeSet.t; 
    succs : NodeSet.t NodeMap.t; 
    preds : NodeSet.t NodeMap.t; 
    loopheads : NodeSet.t 
  }
  let empty = { 
    nodes = NodeSet.empty; 
    succs = NodeMap.empty; 
    preds = NodeMap.empty; 
    loopheads = NodeSet.empty 
  }

  let nodesof : t -> Node.t list 
  =fun t -> NodeSet.elements t.nodes

  let succs : Node.t -> t -> NodeSet.t
  =fun n g -> try NodeMap.find n g.succs with _ -> NodeSet.empty

  let preds : Node.t -> t -> NodeSet.t
  =fun n g -> try NodeMap.find n g.preds with _ -> NodeSet.empty

  let add_node : Node.t -> t -> t
  =fun n g -> { g with nodes = NodeSet.add n g.nodes }

  let add_nodes : Node.t list -> t -> t
  =fun ns g -> g |> (List.fold_right add_node ns)

  let add_edge : Node.t -> Node.t -> t -> t
  =fun n1 n2 g -> 
    g 
    |> add_nodes [n1;n2] 
    |> (fun g -> { g with succs = NodeMap.add n1 (NodeSet.add n2 (succs n1 g)) g.succs }) 
    |> (fun g -> { g with preds = NodeMap.add n2 (NodeSet.add n1 (preds n2 g)) g.preds }) 

  let add_loophead : Node.t -> t -> t 
  =fun n g -> {g with loopheads = NodeSet.add n g.loopheads }

  let is_loophead : Node.t -> t -> bool 
  =fun n g -> NodeSet.mem n g.loopheads     

  let get_entry : t -> Node.t 
  =fun g -> 
    let entries = 
      NodeSet.fold (fun n res -> 
        if NodeSet.is_empty (preds n g) then n::res else res 
      ) g.nodes [] in 
      assert (List.length entries = 1); 
      List.hd entries 

  let get_exit : t -> Node.t 
  =fun g -> 
    let exits = 
      NodeSet.fold (fun n res -> 
        if NodeSet.is_empty (succs n g) then n::res else res 
      ) g.nodes [] in 
      assert (List.length exits = 1); 
      List.hd exits 

  let remove_edge : Node.t -> Node.t -> t -> t 
  =fun n1 n2 g -> 
    g 
    |> (fun g -> { g with succs = NodeMap.add n1 (NodeSet.remove n2 (succs n1 g)) g.succs }) 
    |> (fun g -> { g with preds = NodeMap.add n2 (NodeSet.remove n1 (preds n2 g)) g.preds }) 

  let remove_succs : Node.t -> t -> t 
  =fun n g -> 
    g 
    |> NodeSet.fold (remove_edge n) (succs n g)

  let remove_preds : Node.t -> t -> t 
  =fun n g -> 
    g 
    |> NodeSet.fold (fun p -> remove_edge p n) (preds n g)

  let remove_node : Node.t -> t -> t 
  =fun n g -> 
    g 
    |> remove_succs n 
    |> remove_preds n 
    |> (fun g -> { g with nodes = NodeSet.remove n g.nodes })
    
  let remove_unnecessary_skips : t -> t 
  =fun g -> 
    let rec fixpoint g = 
      let g' = 
        list_fold (fun n g -> 
          match Node.get_instr n with 
          | Node.I_skip -> 
            if NodeSet.cardinal (preds n g) = 1 && 
               NodeSet.cardinal (succs n g) = 1 then 
              let pred = NodeSet.choose (preds n g) in 
              let succ = NodeSet.choose (succs n g) in 
                remove_node n g 
                |> remove_edge pred n 
                |> remove_edge n succ
                |> add_edge pred succ 
            else g
          | _ -> g) (nodesof g) g in 
        if g = g' then g 
        else fixpoint g' in 
    fixpoint g       

  let print g = 
    print_endline "** Nodes **";
    NodeSet.iter (fun n -> 
      print_endline (Node.to_string n)
    ) g.nodes;
    print_endline "** loopheads **";
    NodeSet.iter (fun n -> 
      print_endline (Node.to_string n)
    ) g.loopheads;
    print_endline "";
    print_endline "** Edges **";
    NodeMap.iter (fun n succs -> 
      NodeSet.iter (fun s ->
        print_endline (string_of_int (Node.get_nodeid n) ^ " -> " ^ string_of_int (Node.get_nodeid s))
      ) succs
    ) g.succs

  let dot g = 
    let oc = open_out "cfg.dot" in 
    Printf.fprintf oc "digraph G {";
    NodeSet.iter (fun n -> 
      Printf.fprintf oc "%s" (string_of_int (Node.get_nodeid n) ^ " ");
      Printf.fprintf oc "%s" ("[label=\"" ^ Node.to_string n ^ "\"]");
      Printf.fprintf oc "\n"
    ) g.nodes;
    NodeMap.iter (fun n succs -> 
      NodeSet.iter (fun s ->
        Printf.fprintf oc "%s\n" (string_of_int (Node.get_nodeid n) ^ " -> " ^ string_of_int (Node.get_nodeid s))
      ) succs
    ) g.succs;
    Printf.fprintf oc "}"
end;;

let run_node : Node.t -> Memory.t -> Memory.t option 
=fun node mem -> 
  match Node.get_instr node with 
  | I_alloc (x, n) -> Some (Memory.alloc x n mem)
  | I_assign (lv, exp) -> Some (Memory.bind (eval_lv lv mem) (eval exp mem) mem)
  | I_assume exp ->
    let _ = print_endline "========= DEBUG ASSUME =========" in 
    begin 
      match eval exp mem with 
      | INT 0 -> let _ = print_endline "========= DEBUG false =========" in None 
      | INT _ -> let _ = print_endline "========= DEBUG true =========" in Some mem 
      | _ -> raise (RuntimeErr "if: condition must be integer")
    end 
  | I_skip -> let _ = print_endline "========= DEBUG POINT =========" in Some mem 
  | I_read x -> Some (Memory.bind (VAR x) (INT (read_int ())) mem)
  | I_print exp -> 
    begin 
      let _ = print_endline "========= DEBUG PRINT =========" in 
      match eval exp mem with
      | INT n -> print_endline (string_of_int n); Some mem
      | _ -> raise (RuntimeErr "print: arg must be integer")
    end;;

let execute_cfg : Cfg.t -> Memory.t 
=fun cfg -> 
  let init_workset = [Cfg.get_entry cfg, Memory.empty] in 
  let rec iter workset = 
    match workset with 
    | [] -> raise (Failure "Interpreter.run: empty workset")
    | (node, mem)::workset' -> 
      if node = Cfg.get_exit cfg then mem 
      else 
        begin 
          match run_node node mem with 
          | None -> iter workset'
          | Some mem' -> 
            let next =  List.map (fun s -> (s, mem')) (NodeSet.elements (Cfg.succs node cfg)) in 
              iter (next@workset') 
        end in 
  let output = iter init_workset in 
    output;;


let n1 = Node.create_alloc ("a") (10);;
let n2 = Node.create_assign (ID "i") (NUM 1);;
let n3 = Node.create_assign (ID "s") (NUM 1);;
let n4 = Node.create_read ("n");;
let n5 =  Node.create_skip ();;
let n6 = Node.create_assume (LE(LV(ID "i"), LV(ID "n")));;
let n7 = Node.create_assume (NOT(LE(LV(ID "i"), LV(ID "n"))));;
let n8 = Node.create_assign (ID "s") (MUL(LV(ID "s"), LV(ID "i")));;
let n9 = Node.create_assign (ID "i") (ADD(LV(ID "i"), (NUM 1)));;
let n10 = Node.create_print (LV(ID "s"));;

(*마지막 instruction이 EXIT으로 바뀌기 때문에 dummy 필요*)
let n11 =  Node.create_skip ();;

let new_cfg = Cfg.empty;;
let new_cfg = 
let new_cfg = Cfg.add_node (n1) new_cfg in 
let new_cfg = Cfg.add_node (n2) new_cfg in 
let new_cfg = Cfg.add_node (n3) new_cfg in
let new_cfg = Cfg.add_node (n4) new_cfg in 
let new_cfg = Cfg.add_node (n5) new_cfg in 
let new_cfg = Cfg.add_node (n6) new_cfg in 
let new_cfg = Cfg.add_node (n7) new_cfg in 
let new_cfg = Cfg.add_node (n8) new_cfg in 
let new_cfg = Cfg.add_node (n9) new_cfg in
let new_cfg = Cfg.add_node (n10) new_cfg in 
let new_cfg = Cfg.add_node (n11) new_cfg in 
let new_cfg = Cfg.add_edge n1 n2 new_cfg in 
let new_cfg = Cfg.add_edge n2 n3 new_cfg in 
let new_cfg = Cfg.add_edge n3 n4 new_cfg in 
let new_cfg = Cfg.add_edge n4 n5 new_cfg in 
let new_cfg = Cfg.add_edge n5 n6 new_cfg in 
let new_cfg = Cfg.add_edge n5 n7 new_cfg in 
let new_cfg = Cfg.add_edge n6 n8 new_cfg in 
let new_cfg = Cfg.add_edge n8 n9 new_cfg in 
let new_cfg = Cfg.add_edge n7 n10 new_cfg in 
let new_cfg = Cfg.add_edge n10 n11 new_cfg in 
let new_cfg = Cfg.add_edge n9 n5 new_cfg in 
new_cfg;;

let new_cfg2 = Cfg.empty;;
let n1 = Node.create_assign (ID "to_print") (NUM 10);;
let n2 = Node.create_print (LV(ID "to_print"));;
let n3 =  Node.create_skip ();;

let new_cfg2 =
  let new_cfg2 =  Cfg.add_edge n1 n2 new_cfg2 in 
  let new_cfg2 =  Cfg.add_edge n2 n3 new_cfg2 in
  new_cfg2;; 


let merge_cfg (cfg1 : Cfg.t) (cfg2 : Cfg.t) (n1 : Node.t) (n2 : Node.t) : Cfg.t =

  let g =
    Cfg.add_nodes (Cfg.nodesof cfg2) cfg1
  in

  let g =
    List.fold_left
      (fun acc n ->
         NodeSet.fold
           (fun s acc' -> Cfg.add_edge n s acc')
           (Cfg.succs n cfg2)
           acc
      )
      g
      (Cfg.nodesof cfg2)
  in


  let g =
    List.fold_left
      (fun acc n ->
         if Cfg.is_loophead n cfg2
         then Cfg.add_loophead n acc
         else acc
      )
      g
      (Cfg.nodesof cfg2)
  in

  Cfg.add_edge n1 n2 g;;


let cfg_decl :decl-> Cfg.t =
fun (t, id) ->
  match t with
  | TINT -> 
    let new_cfg = Cfg.empty in 
    let new_node = Node.create_assign (ID id) (NUM 0) in
    let new_entry = Node.create_skip () in
    let new_exit = Node.create_skip () in
    let new_cfg = Cfg.add_node new_entry new_cfg in 
    let new_cfg = Cfg.add_node new_exit new_cfg in 
    let new_cfg = Cfg.add_node new_node new_cfg in 
    let new_cfg = Cfg.add_edge new_entry new_node new_cfg in 
    Cfg.add_edge new_node new_exit new_cfg

  | TARR(n) ->
    let new_cfg = Cfg.empty in 
    let new_node = Node.create_alloc (id) (n) in
    let new_entry = Node.create_skip () in
    let new_exit = Node.create_skip () in
    let new_cfg = Cfg.add_node new_entry new_cfg in 
    let new_cfg = Cfg.add_node new_exit new_cfg in 
    let new_cfg = Cfg.add_node new_node new_cfg in 
    let new_cfg = Cfg.add_edge new_entry new_node new_cfg in 
    Cfg.add_edge new_node new_exit new_cfg;;


let rec cfg_stmt: stmt -> Cfg.t = 
fun s -> 
  match s with
  | ASSIGN(lv, e) -> 
    (match lv with
    | ID x -> 
      let new_cfg = Cfg.empty in 
      let new_node = Node.create_assign (ID x) (e) in
      let new_entry = Node.create_skip () in
      let new_exit = Node.create_skip () in
      let new_cfg = Cfg.add_node new_node new_cfg in 
      let new_cfg = Cfg.add_node new_entry new_cfg in 
      let new_cfg = Cfg.add_node new_exit new_cfg in 
      let new_cfg = Cfg.add_edge new_entry new_node new_cfg in 
      Cfg.add_edge new_node new_exit new_cfg

    | ARR (x, e1) -> 
        let new_cfg = Cfg.empty in 
        let new_node = Node.create_assign (ARR (x, e1)) (e) in
        let new_entry = Node.create_skip () in
        let new_exit = Node.create_skip () in
        let new_cfg = Cfg.add_node new_node new_cfg in 
        let new_cfg = Cfg.add_node new_entry new_cfg in 
        let new_cfg = Cfg.add_node new_exit new_cfg in 
        let new_cfg = Cfg.add_edge new_entry new_node new_cfg in 
        Cfg.add_edge new_node new_exit new_cfg
    )
  | IF(e, stmt1, stmt2) -> 
    let new_cfg = Cfg.empty in 
    let new_entry = Node.create_skip () in
    let new_exit = Node.create_skip () in
    let new_cfg = Cfg.add_node new_entry new_cfg in 
    let n1 = Node.create_skip () in 
    let assume1 = Node.create_assume e in 
    let assume2 = Node.create_assume (NOT(e)) in 
    let cfg_S1 = cfg_stmt stmt1 in 
    let cfg_S2 = cfg_stmt stmt2 in 
    let n2 = Node.create_skip () in
    let new_cfg = Cfg.add_nodes [n1;assume1;assume2;n2] new_cfg in 
    let new_cfg = Cfg.add_edge new_entry n1 new_cfg in
    let new_cfg = Cfg.add_edge n1 assume1 new_cfg in
    let new_cfg = Cfg.add_edge n1 assume2 new_cfg in
     let _ = print_endline "========= DEBUG POINT1 =========" in
    let new_cfg = merge_cfg new_cfg cfg_S1 (assume1) (Cfg.get_entry cfg_S1) in
     let _ = print_endline "========= DEBUG POINT2 =========" in
    let new_cfg = merge_cfg new_cfg cfg_S2 (assume2) (Cfg.get_entry cfg_S2) in

     let _ = print_endline "========= DEBUG POINT3 =========" in
    let new_cfg = Cfg.add_edge (Cfg.get_exit cfg_S1) n2 new_cfg in

     let _ = print_endline "========= DEBUG POINT4 =========" in
    let new_cfg = Cfg.add_edge (Cfg.get_exit cfg_S2) n2 new_cfg in
    let new_cfg = Cfg.add_node new_exit new_cfg in 
    Cfg.add_edge n2 new_exit new_cfg

  | WHILE(e, stmt) -> 
    let new_cfg = Cfg.empty in 
    let new_entry = Node.create_skip () in
    let new_exit = Node.create_skip () in
    let new_cfg = Cfg.add_node new_entry new_cfg in 
    
    let n1 = Node.create_skip () in 
    let assume1 = Node.create_assume e in 
    let assume2 = Node.create_assume (NOT(e)) in 
    let cfg_S = cfg_stmt stmt in 
    let new_cfg = Cfg.add_nodes [n1;assume1;assume2] new_cfg in
    
    let new_cfg = Cfg.add_edge new_entry n1 new_cfg in
    let new_cfg = Cfg.add_edge n1 assume1 new_cfg in
    let new_cfg = Cfg.add_edge n1 assume2 new_cfg in
    let new_cfg = Cfg.add_loophead n1 new_cfg in 

     let _ = print_endline "========= DEBUG POINT5 =========" in
    let new_cfg = merge_cfg new_cfg cfg_S (assume1) (Cfg.get_entry cfg_S) in

     let _ = print_endline "========= DEBUG POINT6 =========" in
    let new_cfg = Cfg.add_edge (Cfg.get_exit cfg_S) n1 new_cfg in
    let new_cfg = Cfg.add_node new_exit new_cfg in 
    Cfg.add_edge assume2 new_exit new_cfg


  | DOWHILE(stmt, e) -> 
    let new_cfg = Cfg.empty in 
    let new_entry = Node.create_skip () in
    let new_exit = Node.create_skip () in
    let new_cfg = Cfg.add_node new_entry new_cfg in 

    let cfg_S = cfg_stmt stmt in 
    let cfg_while = cfg_stmt (WHILE(e, stmt)) in 

     let _ = print_endline "========= DEBUG POINT7 =========" in
    let new_cfg = merge_cfg new_cfg cfg_S (new_entry) (Cfg.get_entry cfg_S) in 

     let _ = print_endline "========= DEBUG POINT8 =========" in
    let new_cfg = merge_cfg new_cfg cfg_while (Cfg.get_exit cfg_S) (Cfg.get_entry cfg_while) in
    let new_cfg = Cfg.add_node new_exit new_cfg in 

     let _ = print_endline "========= DEBUG POINT9 =========" in
    Cfg.add_edge (Cfg.get_exit cfg_while) (new_exit) new_cfg  

  | READ x ->
      let new_cfg = Cfg.empty in 
      let new_node = Node.create_read x in
      let new_entry = Node.create_skip () in
      let new_exit = Node.create_skip () in
      let new_cfg = Cfg.add_node new_node new_cfg in 
      let new_cfg = Cfg.add_node new_entry new_cfg in 
      let new_cfg = Cfg.add_node new_exit new_cfg in 
      let new_cfg = Cfg.add_edge new_entry new_node new_cfg in 
      Cfg.add_edge new_node new_exit new_cfg
  
  | PRINT e ->
      let new_cfg = Cfg.empty in 
      let new_node = Node.create_print e in
      let new_entry = Node.create_skip () in
      let new_exit = Node.create_skip () in
      let new_cfg = Cfg.add_node new_node new_cfg in 
      let new_cfg = Cfg.add_node new_entry new_cfg in 
      let new_cfg = Cfg.add_node new_exit new_cfg in 
      let new_cfg = Cfg.add_edge new_entry new_node new_cfg in 
      Cfg.add_edge new_node new_exit new_cfg


  | BLOCK b ->
    let new_cfg = Cfg.empty in 
    let new_entry = Node.create_skip () in
    let new_exit = Node.create_skip () in
    let new_cfg = Cfg.add_node new_entry new_cfg in 

    let cfg_block = cfg_b b in 

     let _ = print_endline "========= DEBUG POINT10 =========" in
    let new_cfg = merge_cfg new_cfg cfg_block (new_entry) (Cfg.get_entry cfg_block) in 
    let new_cfg = Cfg.add_node new_exit new_cfg in 

     let _ = print_endline "========= DEBUG POINT11 =========" in
    Cfg.add_edge (Cfg.get_exit cfg_block) (new_exit) new_cfg 

and cfg_b (d_list, s_list) =
  let entry = Node.create_skip () in
  let exit = Node.create_skip () in
  let init_cfg = Cfg.add_node entry Cfg.empty in

  (* declarations *)
  let d_cfg = List.fold_left (fun acc decl ->
    let decl_cfg = cfg_decl decl in
     let _ = print_endline "========= DEBUG POINT12 =========" in
    merge_cfg acc decl_cfg (Cfg.get_exit acc) (Cfg.get_entry decl_cfg)
  ) init_cfg d_list in

  (* statements *)
  let s_cfg = List.fold_left (fun acc stmt ->
    let stmt_cfg = cfg_stmt stmt in
     let _ = print_endline "========= DEBUG POINT13 =========" in
    merge_cfg acc stmt_cfg (Cfg.get_exit acc) (Cfg.get_entry stmt_cfg)
  ) d_cfg s_list in

  let final_cfg = Cfg.add_node exit s_cfg in
   let _ = print_endline "========= DEBUG POINT14 =========" in
  Cfg.add_edge (Cfg.get_exit s_cfg) exit final_cfg
;;






(*
let entry = Cfg.get_entry new_cfg;;
let _ = Cfg.dot new_cfg;;
let _ = execute_cfg new_cfg;;
*)
(*====================================================*)

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

let tc1 = (
[
  (TINT, "i");
  (TARR 1000, "a");
]
,
[
  WHILE (
    LT (LV (ID "i"), NUM 1000),
      ASSIGN (ID "i",ADD (LV (ID "i"), NUM 1));
  );

  ASSIGN (
    ARR ("arr", LV (ID "i")),   (* 좌변: arr[i] *)
    NUM 1
  );
]
)

let test_cfg = cfg_b my_prog;;
let nodes = Cfg.print test_cfg;;
let _ = Cfg.dot (Cfg.remove_unnecessary_skips test_cfg);;

exception NotImplemented;;

module type Interval = sig
  type integer = PlusInf | MinusInf | Int of int 
  type t = Bot | Range of integer * integer 
  val bot : t
  val top : t 
  val one : t 
  val zero : t 
  val from_int : int -> t 
  val from_bounds : integer -> integer -> t
  val order : t -> t -> bool
  val join : t -> t -> t
  val meet : t -> t -> t
  val widen : t -> t -> t
  val narrow : t -> t -> t
  val add : t -> t -> t
  val mul : t -> t -> t
  val sub : t -> t -> t
  val div : t -> t -> t
  val eq : t -> t -> t
  val not : t -> t
  val le : t -> t -> t
  val lt : t -> t -> t 
  val ge : t -> t -> t 
  val gt : t -> t -> t 
  val band : t -> t -> t
  val bor : t -> t -> t
  val to_string : t -> string
end;;

module Interval : Interval = struct
  type integer = PlusInf | MinusInf | Int of int 
  type t = Bot | Range of integer * integer 
  let bot = Bot 
  let top = Range (MinusInf, PlusInf)  
  let one = Range (Int 1, Int 1)
  let zero = Range (Int 0, Int 0)
  let string_of_integer i = 
    match i with
    | PlusInf -> "+oo"
    | MinusInf -> "-oo"
    | Int n -> string_of_int n 
  let to_string i = 
    match i with 
    | Bot -> "Bot"
    | Range (i1, i2) -> "[" ^ string_of_integer i1 ^ ", " ^ string_of_integer i2 ^ "]"
  let from_int n = Range (Int n, Int n)
  let from_bounds i1 i2 = Range (i1, i2)
  let le_int (i1:integer) (i2:integer) = 
      match i1,i2 with
      | MinusInf, _ -> true
      | _, MinusInf -> false
      | _, PlusInf -> true
      | Int(n1), Int(n2) -> n1 <= n2
      | PlusInf, _ -> false

  let min (i1:integer) (i2:integer) =
    
  let order a b = 
    match a,b with
    | Bot,_ -> true
    | _,Bot -> false
    | Range(l1, u1), Range(l2, u2) -> (le_int l2 l1) && (le_int u1 u2)

  let join _ _ = raise NotImplemented
  let meet _ _ = raise NotImplemented
  let widen _ _ = raise NotImplemented
  let narrow _ _ = raise NotImplemented
  let add _ _ = raise NotImplemented
  let mul _ _ = raise NotImplemented
  let sub _ _ = raise NotImplemented
  let div _ _ = raise NotImplemented
  let eq _ _ = raise NotImplemented
  let le _ _ = raise NotImplemented
  let lt _ _ = raise NotImplemented
  let ge _ _ = raise NotImplemented
  let gt _ _ = raise NotImplemented
  let not _ = raise NotImplemented
  let band _ _ = raise NotImplemented
  let bor _ _ = raise NotImplemented
end;;

type allocsite = int;;
let string_of_allocsite l = "l" ^ string_of_int l;;

module AbsLoc = struct
  type t = Var of string | Allocsite of allocsite 
  let from_var x = Var x 
  let from_allocsite a = Allocsite a 
  let to_string a = 
    match a with 
    | Var x -> x 
    | Allocsite l -> string_of_allocsite l  
end;;

module AbsArray = struct
  type t = allocsite BatSet.t * Interval.t 
  let bot = (BatSet.empty, Interval.bot)
  let get_allocsites (a, _) = a
  let get_size (_, sz) = sz
  let create l n = (BatSet.singleton l, Interval.from_int n)
  let join (a1, sz1) (a2, sz2) = (BatSet.union a1 a2, Interval.join sz1 sz2)
  let widen (a1, sz1) (a2, sz2) = (BatSet.union a1 a2, Interval.widen sz1 sz2)
  let narrow (a1, sz1) (a2, sz2) = (BatSet.intersect a1 a2, Interval.narrow sz1 sz2)
  let order (a1, sz1) (a2, sz2) = BatSet.subset a1 a2 && Interval.order sz1 sz2
  let to_string : t -> string 
  =fun (a, sz) -> Printf.sprintf "(%s, %s)" (Utils.string_of_set string_of_allocsite a) (Interval.to_string sz)
end;;

module AbsVal = struct
  type t = Interval.t * AbsArray.t
  let bot = (Interval.bot, AbsArray.bot)
  let from_itv itv = (itv, AbsArray.bot)
  let from_absarr a = (Interval.bot, a)
  let get_interval (i, _) = i 
  let get_absarray (_, a) = a
  let join (i1, a1) (i2, a2) = (Interval.join i1 i2, AbsArray.join a1 a2)
  let meet_itv itv (i, a) = (Interval.meet itv i, a)
  let widen (i1, a1) (i2, a2) = (Interval.widen i1 i2, AbsArray.widen a1 a2)
  let narrow (i1, a1) (i2, a2) = (Interval.narrow i1 i2, AbsArray.narrow a1 a2)
  let order (i1, a1) (i2, a2) = Interval.order i1 i2 && AbsArray.order a1 a2
  let add (i1, a1) (i2, a2) = (Interval.add i1 i2, AbsArray.join a1 a2)
  let mul (i1, a1) (i2, a2) = (Interval.mul i1 i2, AbsArray.join a1 a2)
  let sub (i1, a1) (i2, a2) = (Interval.sub i1 i2, AbsArray.join a1 a2)
  let div (i1, a1) (i2, a2) = (Interval.div i1 i2, AbsArray.join a1 a2)
  let le (i1, a1) (i2, a2) = (Interval.le i1 i2, AbsArray.join a1 a2)
  let lt (i1, a1) (i2, a2) = (Interval.lt i1 i2, AbsArray.join a1 a2)
  let ge (i1, a1) (i2, a2) = (Interval.ge i1 i2, AbsArray.join a1 a2)
  let gt (i1, a1) (i2, a2) = (Interval.gt i1 i2, AbsArray.join a1 a2)
  let eq (i1, a1) (i2, a2) = (Interval.eq i1 i2, AbsArray.join a1 a2)
  let not (i, a) = (Interval.not i, a)
  let band (i1, a1) (i2, a2) = (Interval.band i1 i2, AbsArray.join a1 a2)
  let bor (i1, a1) (i2, a2) = (Interval.bor i1 i2, AbsArray.join a1 a2)
  let to_string : t -> string 
  =fun (itv, arr) -> Printf.sprintf "(%s, %s)" (Interval.to_string itv) (AbsArray.to_string arr)
end;; 

module type AbsMem = sig
  type t = (AbsLoc.t, AbsVal.t) BatMap.t
  val empty : t
  val find : AbsLoc.t -> t -> AbsVal.t 
  val find_set : AbsLoc.t BatSet.t -> t -> AbsVal.t 
  val add : AbsLoc.t -> AbsVal.t -> t -> t
  val add_set : AbsLoc.t BatSet.t -> AbsVal.t -> t -> t 
  val join : t -> t -> t 
  val widen : t -> t -> t 
  val narrow : t -> t -> t
  val order : t -> t -> bool 
  val print : t -> unit 
end;;

module AbsMem : AbsMem = struct
  type t = (AbsLoc.t, AbsVal.t) BatMap.t
  let empty = BatMap.empty
  let find x m = try BatMap.find x m with _ -> AbsVal.bot
  let find_set xs m = BatSet.fold (fun x -> AbsVal.join (find x m)) xs AbsVal.bot 
  let strong_update loc v m = BatMap.add loc v m 
  let weak_update loc v m = BatMap.add loc (AbsVal.join (find loc m) v) m
  let add loc v m = 
    match loc with 
    | AbsLoc.Var _ -> strong_update loc v m 
    | AbsLoc.Allocsite _ -> weak_update loc v m 
  let add_set locs v m = 
    if BatSet.cardinal locs = 1 then add (BatSet.choose locs) v m 
    else BatSet.fold (fun loc -> weak_update loc v) locs m 
  let join m1 m2 = BatMap.foldi (fun x v m' -> add x (AbsVal.join v (find x m')) m') m1 m2
  let widen m1 m2 = BatMap.foldi (fun x v m' -> add x (AbsVal.widen v (find x m')) m') m1 m2
  let narrow m1 m2 = BatMap.foldi (fun x v m' -> add x (AbsVal.narrow v (find x m')) m') m1 m2
  let order m1 m2 = BatMap.for_all (fun x v -> AbsVal.order v (find x m2)) m1
  let print m = 
    BatMap.iter (fun x v -> 
      prerr_endline (AbsLoc.to_string x ^ " |-> " ^ AbsVal.to_string v)
    ) m 
end;;

module type Table = sig
  type t = AbsMem.t NodeMap.t
  val empty : t
  val init : Node.t list -> t 
  val find : Node.t -> t -> AbsMem.t 
  val add : Node.t -> AbsMem.t -> t -> t
  val print : t -> unit
end;;

module Table : Table = struct 
  type t = AbsMem.t NodeMap.t
  let empty = NodeMap.empty 
  let add = NodeMap.add
  let init ns = List.fold_right (fun n -> add n AbsMem.empty) ns empty
  let find : Node.t -> t -> AbsMem.t 
  =fun n t -> try NodeMap.find n t with _ -> AbsMem.empty
  let print t = NodeMap.iter (fun n m -> 
    prerr_endline (string_of_int (Node.get_nodeid n)); 
    AbsMem.print m; 
    prerr_endline "") t  
end;;


let test_l1 = Interval.Range(Interval.Int 1, Interval.Int 1);;
let test_l2 = Interval.Range(Interval.Int 0, Interval.Int 0);;
let test_l3 = Interval.Range(Interval.Int 0, Interval.Int 1);;
let test_l4 = Interval.Range(Interval.MinusInf, Interval.Int 1);;
let b1 = Interval.order test_l1 test_l1;;
let b2 = Interval.order test_l2 test_l1;;
let b3 = Interval.order test_l2 test_l3;;
let b4 = Interval.order test_l3 test_l2;;

