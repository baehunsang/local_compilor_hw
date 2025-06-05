#use "topfind";;
#thread;;
#require "threads";;
open Mutex;;
#require "batteries";;
#mod_use "./S.ml";;
#mod_use "./T.ml";;
#mod_use "./G.ml";;
open S ;;
(***********************************)
(* abstract syntax definition of T *)
(***********************************)

type program = linstr list
and linstr = label * instr (* labeled instruction *)
and instr = 
  | SKIP
  | ALLOC of var * int  (* x = alloc(n) *)
  | ASSIGNV of var * bop * var * var (* x = y bop z *)
  | ASSIGNC of var * bop * var * int (* x = y bop n *)
  | ASSIGNU of var * uop * var  (* x = uop y *)
  | COPY of var * var           (* x = y *)
  | COPYC of var * int          (* x = n *)
  | UJUMP of label              (* goto L *)
  | CJUMP of var * label        (* if x goto L *)
  | CJUMPF of var * label       (* ifFalse x goto L *)
  | LOAD of var * arr           (* x = a[i] *)
  | STORE of arr * var          (* a[i] = x *)
  | READ of var                 (* read x *)
  | WRITE of var                (* write x *)
  | HALT
and var = string
and label = int
and arr = var * var
and bop = ADD | SUB | MUL | DIV | LT | LE | GT | GE | EQ | AND | OR
and uop = MINUS | NOT;;

let dummy_label = 0;;

(*************************************)
(*        Interpreter for T          *)
(*************************************)
exception RuntimeErr of string ;;

type state = pc * Memory.t
and pc = int
and l2pc = (label,pc) BatMap.t
and global = program * l2pc;;

let eval_binary : value -> bop -> value -> value
=fun v1 op v2 ->
  match v1,op,v2 with
  | INT n1, ADD, INT n2 -> INT (n1+n2)
  | INT n1, SUB, INT n2 -> INT (n1-n2)
  | INT n1, MUL, INT n2 -> INT (n1*n2)
  | INT n1, DIV, INT n2 -> INT (n1/n2)
  | INT n1, LT, INT n2 -> if n1 < n2 then INT 1 else INT 0
  | INT n1, LE, INT n2 -> if n1 <= n2 then INT 1 else INT 0
  | INT n1, GT, INT n2 -> if n1 > n2 then INT 1 else INT 0
  | INT n1, GE, INT n2 -> if n1 >= n2 then INT 1 else INT 0
  | INT n1, EQ, INT n2 -> if n1 = n2 then INT 1 else INT 0
  | INT n1, AND, INT n2 -> if n1 != 0 && n2 != 0 then INT 1 else INT 0
  | INT n1, OR, INT n2 -> if n1 != 0 || n2 != 0 then INT 1 else INT 0
  | _ -> raise (RuntimeErr "T.eval_binary");;

let eval_unary : uop -> value -> value
=fun op v ->
  match op, v with
  | MINUS, INT n -> INT (-n)
  | NOT, INT n -> if n = 0 then INT 1 else INT 0
  | _ -> raise (RuntimeErr "T.eval_unary");;

let get_array_location : arr -> Memory.t -> loc
=fun (a,x) mem ->
  match Memory.lookup (VAR a) mem with
  | ARRAY (base, size) -> 
    begin
      match Memory.lookup (VAR x) mem with
      | INT offset -> 
        if offset < 0 || offset >= size then raise (RuntimeErr "T: invalid array index") 
        else ADDR (base, offset)
      | _ -> raise (RuntimeErr "T: invalid array index")
    end
  | _ -> raise (RuntimeErr "T: invalid array");;

let get_instr : program -> pc -> instr
=fun pgm pc -> 
  let (_,instr) = List.nth pgm pc in
    instr;;

let get_next_mem : instr -> Memory.t -> Memory.t
=fun instr mem -> 
  match instr with
  | ALLOC (x,n) -> Memory.alloc x n mem
  | ASSIGNV (x,o,y,z) ->
    let v_y = Memory.lookup (VAR y) mem in
    let v_z = Memory.lookup (VAR z) mem in
    let v_x = eval_binary v_y o v_z in
      Memory.bind (VAR x) v_x mem
  | ASSIGNC (x,o,y,n) ->
    let v_y = Memory.lookup (VAR y) mem in
    let v_x = eval_binary v_y o (INT n) in
      Memory.bind (VAR x) v_x mem
  | ASSIGNU (x,o,y) ->
    let v_y = Memory.lookup (VAR y) mem in
    let v_x = eval_unary o v_y in
      Memory.bind (VAR x) v_x mem
  | COPY (x,y) -> Memory.bind (VAR x) (Memory.lookup (VAR y) mem) mem
  | COPYC (x,c) -> Memory.bind (VAR x) (INT c) mem
  | LOAD (x,arr) ->
    let arrloc = get_array_location arr mem in
    let v_x = Memory.lookup arrloc mem in
      Memory.bind (VAR x) v_x mem
  | STORE (arr,x) ->
    let v_x = Memory.lookup (VAR x) mem in
    let arrloc = get_array_location arr mem in
      Memory.bind arrloc v_x mem
  | READ x ->
    let _ = print_endline "=======Debug point hit!!!========" in 
    let v = read_int () in
      Memory.bind (VAR x) (INT v) mem
  | WRITE x ->
    let v_x = Memory.lookup (VAR x) mem in
    (match v_x with
    | INT n -> print_endline (string_of_int n)
    | _ -> raise (RuntimeErr "WRITE: type error (not an integer)")
    );
    mem
  | _ -> mem;;

let get_pc_of_label : global -> label -> pc
=fun (_,l2pc) l -> try BatMap.find l l2pc with _ -> raise (Failure ("T: Label not found :"^ string_of_int l));;
  
let get_next_pc  : global -> instr -> state -> pc
=fun global instr (pc,mem) -> 
  match instr with
  | UJUMP l -> get_pc_of_label global l 
  | CJUMP (x,l) -> 
    let v = Memory.lookup (VAR x) mem in 
      begin
      match v with
      | INT n -> if n != 0 then get_pc_of_label global l else pc+1
      | _ -> raise (RuntimeErr "T: invalid operands for CJUMP") 
      end
  | CJUMPF (x,l) -> 
    let v = Memory.lookup (VAR x) mem in 
      begin
      match v with
      | INT n -> if n = 0 then get_pc_of_label global l else pc+1
      | _ -> raise (RuntimeErr "T: invalid operands for CJUMP") 
      end
  | _ -> pc+1;;
 
let run : global -> state -> state
=fun (pgm,l2pc) (pc,mem) -> 
  let instr = get_instr pgm pc in
  let mem' = get_next_mem instr mem in
  let pc'  = get_next_pc (pgm,l2pc) instr (pc,mem) in
    (pc',mem');;

let rec loop : global -> state -> int -> unit
=fun (pgm,l2pc) (pc,mem) k -> 
  if get_instr pgm pc = HALT then print_endline ("The number of instructions executed : " ^ string_of_int k)
  else loop (pgm,l2pc) (run (pgm,l2pc) (pc,mem)) (k+1);;

let get_label2pc : program -> l2pc 
=fun pgm -> 
  let _,map =
    List.fold_left (fun (pc,map) (l,_) ->
      if l = dummy_label then (pc+1,map) else (pc+1,BatMap.add l pc map)
    ) (0,BatMap.empty) pgm in
  map;;

let execute : program -> unit
=fun pgm -> 
  let l2pc = get_label2pc pgm in
    loop (pgm,l2pc) (0,Memory.empty) 0;;

(*************************************)
(* pretty printer for the T language *)
(*************************************)
let pp : program -> unit
=fun pgm -> 
  let ps = print_string in
  let pn = print_endline in
  let s_bop o = match o with ADD -> "+" | SUB -> "-" | MUL -> "*" | DIV -> "/"
  | LT -> "<" | LE -> "<=" | GT -> ">" | GE -> ">=" | EQ -> "==" | AND -> "&&" |
  OR -> "||" in
  let s_uop o = match o with MINUS -> "-" | NOT -> "!" in
  let s_arr (x,y) = x ^ "[" ^ y ^ "]" in
  List.iter (fun (label, instr) ->
    ps (string_of_int label ^ " : ");
    match instr with
    | HALT -> pn "HALT"
    | SKIP -> pn "SKIP"
    | ALLOC (x,n) -> pn (x ^ " = alloc (" ^ string_of_int n ^ ")")
    | ASSIGNV (x,o,y,z) -> pn (x ^ " = " ^ y ^ " " ^ s_bop o ^ " " ^ z)
    | ASSIGNC (x,o,y,n) -> pn (x ^ " = " ^ y ^ " " ^ s_bop o ^ " " ^ string_of_int n)
    | ASSIGNU (x,o,y) -> pn (x ^ " = " ^ s_uop o ^ y)
    | COPY (x,y) -> pn (x ^ " = " ^ y)
    | COPYC (x,n) -> pn (x ^ " = " ^ string_of_int n)
    | UJUMP label -> pn ("goto " ^ string_of_int label)
    | CJUMP (x,l) -> pn ("if " ^ x ^ " goto " ^ string_of_int l)
    | CJUMPF (x,l) -> pn ("iffalse " ^ x ^ " goto " ^ string_of_int l)
    | LOAD (x,a) -> pn (x ^ " = " ^ s_arr a)
    | STORE (a,x) -> pn (s_arr a ^  " = " ^ x)
    | READ x -> pn ("read " ^ x)
    | WRITE x -> pn ("write " ^ x)
  ) pgm;;



(* 예시 프로그램 : x ← read(); y ← x + 1; write y; halt *)
let example_prog =
  [(0, ALLOC ("arr", 10)); (0, COPYC ("i", 0)); (0, COPYC ("j", 0));
   (0, COPYC (".t1", 0)); (0, COPY ("i", ".t1")); (0, COPYC (".t2", 0));
   (0, COPY ("j", ".t2")); (2, SKIP); (0, COPY (".t3", "i"));
   (0, COPYC (".t4", 10)); (0, ASSIGNV (".t5", LT, ".t3", ".t4"));
   (0, CJUMPF (".t5", 3)); (0, COPY (".t6", "i")); (0, COPY (".t7", "i"));
   (0, STORE (("arr", ".t6"), ".t7")); (0, COPY (".t8", "i"));
   (0, COPYC (".t9", 1)); (0, ASSIGNV (".t10", ADD, ".t8", ".t9"));
   (0, COPY ("i", ".t10")); (0, COPY (".t11", "j")); (0, COPYC (".t12", 1));
   (0, ASSIGNV (".t13", ADD, ".t11", ".t12")); (0, COPY ("j", ".t13"));
   (0, UJUMP 2); (3, SKIP); (0, COPY (".t14", "i")); (0, WRITE ".t14");
   (0, HALT)];;

let _ = execute example_prog;;

module Node = struct
  type t = { id : int; label : label; instr : instr }
  let counter = ref 0
  let new_id () = incr counter; !counter
  let create lbl instr = { id = new_id (); label = lbl; instr }
  let get_nodeid n = n.id
  let get_label n = n.label
  let get_instr n = n.instr
  let to_string n =
    let str_of_line = fun (label, instr) ->
      let s_bop o = match o with ADD -> "+" | SUB -> "-" | MUL -> "*" | DIV -> "/"
        | LT -> "<" | LE -> "<=" | GT -> ">" | GE -> ">=" | EQ -> "==" | AND -> "&&" |
         OR -> "||" in
      let s_uop o = match o with MINUS -> "-" | NOT -> "!" in
      let s_arr (x,y) = x ^ "[" ^ y ^ "]" in
    let ln = string_of_int label ^ " : " in 
    match instr with
    | HALT -> ln ^ "HALT"
    | SKIP -> ln ^ "SKIP"
    | ALLOC (x,n) -> ln^ (x ^ " = alloc (" ^ string_of_int n ^ ")")
    | ASSIGNV (x,o,y,z) -> ln^ (x ^ " = " ^ y ^ " " ^ s_bop o ^ " " ^ z)
    | ASSIGNC (x,o,y,n) -> ln^ (x ^ " = " ^ y ^ " " ^ s_bop o ^ " " ^ string_of_int n)
    | ASSIGNU (x,o,y) -> ln^ (x ^ " = " ^ s_uop o ^ y)
    | COPY (x,y) -> ln^ (x ^ " = " ^ y)
    | COPYC (x,n) -> ln^ (x ^ " = " ^ string_of_int n)
    | UJUMP label -> ln^ ("goto " ^ string_of_int label)
    | CJUMP (x,l) -> (ln^ ("if " ^ x ^ " goto " ^ string_of_int l))
    | CJUMPF (x,l) -> (ln^ ("iffalse " ^ x ^ " goto " ^ string_of_int l))
    | LOAD (x,a) -> (ln^ (x ^ " = " ^ s_arr a))
    | STORE (a,x) -> (ln^ (s_arr a ^  " = " ^ x))
    | READ x -> (ln^ ("read " ^ x))
    | WRITE x -> (ln^ ("write " ^ x))in 
  str_of_line (n.label, n.instr)
  let compare n1 n2 = compare n1.id n2.id
end;;

module NodeSet = Set.Make(Node);;
module NodeMap = Map.Make(Node);;

module Cfg = struct
  type t = {
    nodes : NodeSet.t;
    succs : NodeSet.t NodeMap.t;
    preds : NodeSet.t NodeMap.t;
  }
  let empty = { nodes = NodeSet.empty; succs = NodeMap.empty; preds = NodeMap.empty }

  let nodesof g = NodeSet.elements g.nodes
  let succs n g = try NodeMap.find n g.succs with Not_found -> NodeSet.empty
  let preds n g = try NodeMap.find n g.preds with Not_found -> NodeSet.empty

  let add_node n g = { g with nodes = NodeSet.add n g.nodes }
  let add_nodes ns g = List.fold_right add_node ns g
  let add_edge n1 n2 g =
    g
    |> add_nodes [n1; n2]
    |> fun g -> { g with succs = NodeMap.add n1 (NodeSet.add n2 (succs n1 g)) g.succs }
    |> fun g -> { g with preds = NodeMap.add n2 (NodeSet.add n1 (preds n2 g)) g.preds }
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

  let replace_node old_n new_n set =
    NodeSet.fold (fun n acc ->
      if Node.compare n old_n = 0 then NodeSet.add new_n acc
      else NodeSet.add n acc
    ) set NodeSet.empty

  let replace_key old_n new_n map =
    NodeMap.fold (fun k v acc ->
      let k' = if Node.compare k old_n = 0 then new_n else k in
      let v' = replace_node old_n new_n v in
      NodeMap.add k' v' acc
    ) map NodeMap.empty

  let update_instr n instr g =
    let n' = { n with Node.instr = instr } in
    {
      nodes = replace_node n n' g.nodes;
      succs = replace_key n n' g.succs;
      preds = replace_key n n' g.preds;
    }

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
    Printf.fprintf oc "}";
    close_out oc
end;;

module Table= struct 
  type t = int BatSet.t NodeMap.t
  let empty = NodeMap.empty 
  let add = NodeMap.add
  let init ns = List.fold_right (fun n -> add n BatSet.empty) ns empty
  let find : Node.t -> t -> int BatSet.t 
  =fun n t -> try NodeMap.find n t with _ -> BatSet.empty 
end;;

let t_2_cfg (pgm : program) : Cfg.t =
  let nodes = List.map (fun (lbl, instr) -> Node.create lbl instr) pgm in
  let arr = Array.of_list nodes in
  let label_map =
    List.fold_left
      (fun m n ->
         let lbl = Node.get_label n in
         if lbl <> dummy_label then BatMap.add lbl n m else m)
      BatMap.empty nodes
  in
  let g = ref Cfg.empty in
  Array.iter (fun n -> g := Cfg.add_node n !g) arr;
  let add_edge i n =
    match Node.get_instr n with
    | UJUMP l ->
        begin match BatMap.find_opt l label_map with
        | Some t -> g := Cfg.add_edge n t !g
        | None -> ()
        end
    | CJUMP (_, l) ->
        begin
          (match BatMap.find_opt l label_map with
          | Some t -> g := Cfg.add_edge n t !g
          | None -> ());
          if i + 1 < Array.length arr then g := Cfg.add_edge n arr.(i+1) !g
        end
    | CJUMPF (_, l) ->
        begin
          (match BatMap.find_opt l label_map with
          | Some t -> g := Cfg.add_edge n t !g
          | None -> ());
          if i + 1 < Array.length arr then g := Cfg.add_edge n arr.(i+1) !g
        end
    | HALT -> ()
    | _ ->
        if i + 1 < Array.length arr then g := Cfg.add_edge n arr.(i+1) !g
  in
  Array.iteri add_edge arr;
  !g
;;
let cfg_2_t (cfg : Cfg.t) : program =
  Cfg.nodesof cfg
  |> List.sort (fun n1 n2 -> compare (Node.get_nodeid n1) (Node.get_nodeid n2))
  |> List.map (fun n -> (Node.get_label n, Node.get_instr n))
;;
let optimize (pgm : program) : program =
  pgm |> t_2_cfg |> cfg_2_t
;;

let sample_prog = [
  (0, ASSIGNC("i", SUB, "m", 1)); (*d1: i = m - 1*)
  (0, COPY("j", "n")); (*d2: j = n*)
  (0, COPY("a", "u1")); (*d3: a = u1*)
  (1, ASSIGNC("i", ADD, "i", 1)); (*d4: i + 1*)
  (0, ASSIGNC("j", SUB, "j", 1)); (*d5: j= j-1*)
  (0, ASSIGNC("b", GE, "i", 0)); (*d6: b = i >= 0*)
  (0, CJUMP("b", 2)); (*d7: if b goto 2*)
  (0, COPY("a", "u2"));(*d8: a = u2*)
  (2, COPY("i", "u3"));(*d9: i=u3*)
  (0, ASSIGNC("b", GE, "j", 0));(*d10: b = j>=0*)
  (0, CJUMP("b", 1));(*d11: if b goto 1 *)
  (0, HALT)
];;

let cfg = t_2_cfg sample_prog;;
let _ = Cfg.dot cfg;;


let gen (n: Node.t) = 
  let inst = Node.get_instr n in 
  match inst with
  | ASSIGNC(x, _, _, _) 
  | ASSIGNV(x, _, _, _) 
  | ASSIGNU(x, _, _) 
  | COPY(x, _) 
  | COPYC(x, _) 
  | LOAD(x, _) 
    -> BatSet.singleton (Node.get_nodeid n)
  | _ -> BatSet.empty
;;

let kill (n: Node.t) (cfg:Cfg.t) =
  let inst = Node.get_instr n in 
  let my_id = Node.get_nodeid n in 
  let nodes = Cfg.nodesof cfg in 
  let to_killed var nodes = 
    List.fold_left (
      fun acc node -> 
        let inst = Node.get_instr node in 
        let id = Node.get_nodeid node in
        match inst with
        | ASSIGNC(x, _, _, _) 
        | ASSIGNV(x, _, _, _) 
        | ASSIGNU(x, _, _) 
        | COPY(x, _) 
        | COPYC(x, _) 
        | LOAD(x, _) 
          -> (if x=var then (BatSet.add id acc) else acc )
        | _ -> acc
    ) BatSet.empty nodes 
  in
  match inst with
  | ASSIGNC(x, _, _, _) 
  | ASSIGNV(x, _, _, _) 
  | ASSIGNU(x, _, _) 
  | COPY(x, _) 
  | COPYC(x, _) 
  | LOAD(x, _) 
    -> BatSet.diff (to_killed x nodes) (BatSet.singleton my_id)
  | _ -> BatSet.empty
;;

let nodes = Cfg.nodesof cfg;;
let idx = 3;;
let node = print_endline (Node.to_string (List.nth nodes idx));;
let set = kill (List.nth nodes idx) cfg;;
let _ = BatSet.fold (fun e acc -> print_endline (string_of_int e)) set ();;
(*let _ = List.fold_left (fun acc node -> print_endline ((string_of_int (Node.get_nodeid node))^" "^(Node.to_string node))) () nodes;;*)

let compute_table nodes in_table out_table cfg = 
  List.fold_left (
    fun (prev_in, prev_out) node -> 
      let preds = Cfg.preds node cfg in 
      
      (*compute new in set*)
      let new_in_set = 
        NodeSet.fold (
          fun node acc -> 
            BatSet.union acc (Table.find node prev_out)
        ) preds BatSet.empty in 
      
      let new_in = Table.add node new_in_set prev_in in 
      
      (*compute new out set*)
      let new_out_set = BatSet.union (gen node) (BatSet.diff (Table.find node new_in) (kill node cfg)) in 
      let new_out = Table.add node new_out_set prev_out in 
      (new_in, new_out)
  ) (in_table, out_table) nodes;;

(*fixpoint loop*)
let rec solver nodes in_table out_table cfg = 
  let prev_in = in_table in 
  let prev_out = out_table in 
  let (next_in, next_out) = compute_table nodes prev_in prev_out cfg in 
  if (
    ((NodeMap.compare (fun a b-> BatSet.compare a b) prev_in next_in)=0)&&
    ((NodeMap.compare (fun a b-> BatSet.compare a b) prev_out next_out)=0)
  ) then (next_in, next_out) else solver nodes next_in next_out cfg;;

(*lambda node : empty*)
let in_table = Table.init nodes;;
let out_table = Table.init nodes;;

let (in_table, out_table) = solver nodes in_table out_table cfg;;

(*print in, out set*)
let _ = List.fold_left (
  fun acc node -> 
    let _ = print_endline "node: " in 
    let _ = print_endline ((string_of_int (Node.get_nodeid node))^" "^(Node.to_string node)) in 
     let _ = print_endline "in: " in 
    let in_set = Table.find node in_table in 
    let _ = print_string "{" in 
    let _ = BatSet.fold (fun e acc -> 
      print_string ((string_of_int e) ^ " ")
      ) in_set () in
    let out_set = Table.find node out_table in 
    let _ = print_endline "}" in 
     let _ = print_endline "out" in 
    let _ = print_string "{" in 
    let _ = BatSet.fold (fun e acc -> 
      print_string ((string_of_int e) ^ " ")
      ) out_set () in  
    print_endline "}\n\n"
) () nodes