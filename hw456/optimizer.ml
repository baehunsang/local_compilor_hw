open T


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
end

module NodeSet = Set.Make(Node)
module NodeMap = Map.Make(Node)

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
end

module Table= struct 
  type t = int BatSet.t NodeMap.t
  let empty = NodeMap.empty 
  let add = NodeMap.add
  let init ns = List.fold_right (fun n -> add n BatSet.empty) ns empty
  let find : Node.t -> t -> int BatSet.t 
  =fun n t -> try NodeMap.find n t with _ -> BatSet.empty 
end

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

let cfg_2_t (cfg : Cfg.t) : program =
  Cfg.nodesof cfg
  |> List.sort (fun n1 n2 -> compare (Node.get_nodeid n1) (Node.get_nodeid n2))
  |> List.map (fun n -> (Node.get_label n, Node.get_instr n))

let gen (n: Node.t) = 
  let inst = Node.get_instr n in 
  match inst with
  | ASSIGNC(_, _, _, _) 
  | ASSIGNV(_, _, _, _) 
  | ASSIGNU(_, _, _) 
  | COPY(_, _) 
  | COPYC(_, _) 
  | LOAD(_, _) 
    -> BatSet.singleton (Node.get_nodeid n)
  | _ -> BatSet.empty

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
  ) (in_table, out_table) nodes

(*fixpoint loop*)
let rec solver nodes in_table out_table cfg = 
  let prev_in = in_table in 
  let prev_out = out_table in 
  let (next_in, next_out) = compute_table nodes prev_in prev_out cfg in 
  if (
    ((NodeMap.compare (fun a b-> BatSet.compare a b) prev_in next_in)=0)&&
    ((NodeMap.compare (fun a b-> BatSet.compare a b) prev_out next_out)=0)
  ) then (next_in, next_out) else solver nodes next_in next_out cfg

let optimize (pgm : program) : program =
  pgm |> t_2_cfg |> cfg_2_t
