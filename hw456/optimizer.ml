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
    
  let update_label n label g =
    let n' = { n with Node.label = label } in
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
  | READ(_)
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
        | READ(x)
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
  | READ(x)
    -> BatSet.diff (to_killed x nodes) (BatSet.singleton my_id)
  | _ -> BatSet.empty

let compute_table_for_rda nodes in_table out_table cfg = 
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
let rec solver nodes in_table out_table cfg compute_table= 
  let prev_in = in_table in 
  let prev_out = out_table in 
  let (next_in, next_out) = compute_table nodes prev_in prev_out cfg in 
  if (
    ((NodeMap.compare (fun a b-> BatSet.compare a b) prev_in next_in)=0)&&
    ((NodeMap.compare (fun a b-> BatSet.compare a b) prev_out next_out)=0)
  ) then (next_in, next_out) else solver nodes next_in next_out cfg compute_table


let filter_node nodes input_set var = 
  BatSet.fold (fun id acc -> 
    let node = List.nth nodes (id - 1) in 
    let instr = Node.get_instr node in 
    match instr with
    | ASSIGNC(x, _, _, _) 
    | ASSIGNV(x, _, _, _) 
    | ASSIGNU(x, _, _) 
    | COPY(x, _) 
    | COPYC(x, _) 
    | LOAD(x, _) 
    | READ(x)
      -> if x=var then (NodeSet.add node acc) else acc 
    | _ -> acc
    ) input_set NodeSet.empty


let extract_copyc_consts_set (nodeset : NodeSet.t) : int BatSet.t =
  NodeSet.fold (fun node acc ->
    match Node.get_instr node with
    | COPYC (_, n) ->
        BatSet.add n acc
    | _ -> acc
  ) nodeset BatSet.empty

let extract_copy_variable_set (nodeset : NodeSet.t) : var BatSet.t =
  NodeSet.fold (fun node acc ->
    match Node.get_instr node with
    | COPY (_, y) ->
        BatSet.add y acc
    | _ -> acc
  ) nodeset BatSet.empty

(*constant propagation -> change ASSIGNC, ASSIGNV, ASSIGNU , COPY to COPYC or ASSIGNC*)
(*Make sure you can exchange the variable to constant or other variable iff n_set is singleton and v_Set is empty or vv*)
let constant_propagation cfg in_table = 
  let nodes = Cfg.nodesof cfg in 
  List.fold_left (
    fun acc node ->
      let nodes = Cfg.nodesof acc in 
      let inst = Node.get_instr node in
      match inst with
      | ASSIGNV(x, bop, y, z) -> (

        (*find reaching definition for y*)
        let reaching_definitions = filter_node nodes (Table.find node in_table) y in 
        let n_set_y = extract_copyc_consts_set reaching_definitions in 
        let v_set_y = extract_copy_variable_set reaching_definitions in
        (*find reaching definition for z*)
        let reaching_definitions = filter_node nodes (Table.find node in_table) z in 
        let v_set_z = extract_copy_variable_set reaching_definitions in 
        let n_set_z = extract_copyc_consts_set reaching_definitions in 

        (*both are singletone*)
        if (BatSet.is_singleton n_set_y)&&(BatSet.is_singleton n_set_z)&&(BatSet.is_empty v_set_y)&&(BatSet.is_empty v_set_z) then (

          match bop with
          | ADD -> Cfg.update_instr node (COPYC(x, (BatSet.max_elt n_set_y) + (BatSet.max_elt n_set_z))) acc
          | SUB -> Cfg.update_instr node (COPYC(x, (BatSet.max_elt n_set_y) - (BatSet.max_elt n_set_z))) acc
          | MUL -> Cfg.update_instr node (COPYC(x, (BatSet.max_elt n_set_y) * (BatSet.max_elt n_set_z))) acc
          | DIV -> Cfg.update_instr node (COPYC(x, (BatSet.max_elt n_set_y) / (BatSet.max_elt n_set_z))) acc
          | LT -> Cfg.update_instr node (COPYC(x, if ((BatSet.max_elt n_set_y) < (BatSet.max_elt n_set_z)) then 1 else 0)) acc
          | LE -> Cfg.update_instr node (COPYC(x, if ((BatSet.max_elt n_set_y) <= (BatSet.max_elt n_set_z)) then 1 else 0)) acc
          | GT -> Cfg.update_instr node (COPYC(x, if ((BatSet.max_elt n_set_y) > (BatSet.max_elt n_set_z)) then 1 else 0)) acc
          | GE -> Cfg.update_instr node (COPYC(x, if ((BatSet.max_elt n_set_y) >= (BatSet.max_elt n_set_z)) then 1 else 0)) acc
          | EQ -> Cfg.update_instr node (COPYC(x, if ((BatSet.max_elt n_set_y) = (BatSet.max_elt n_set_z)) then 1 else 0)) acc 
          | AND -> Cfg.update_instr node (COPYC(x, if ((BatSet.max_elt n_set_y)!=0 && (BatSet.max_elt n_set_z)!=0) then 1 else 0)) acc
          | OR -> Cfg.update_instr node (COPYC(x, if ((BatSet.max_elt n_set_y)!=0 || (BatSet.max_elt n_set_z)!=0) then 1 else 0)) acc
        ) else (
          if (BatSet.is_singleton n_set_z) then (
            Cfg.update_instr node (ASSIGNC(x,bop,y ,BatSet.max_elt n_set_z)) acc
          ) else (
            acc
          )
        )
      )


      | ASSIGNC(x, bop, y, n) -> (
        (*find reaching definition for y*)
        let reaching_definitions = filter_node nodes (Table.find node in_table) y in 
        let n_set_y = extract_copyc_consts_set reaching_definitions in 
        let v_set_y = extract_copy_variable_set reaching_definitions in
        if (BatSet.is_singleton n_set_y)&&(BatSet.is_empty v_set_y) then (
          match bop with
          | ADD -> Cfg.update_instr node (COPYC(x, (BatSet.max_elt n_set_y) + n)) acc
          | SUB -> Cfg.update_instr node (COPYC(x, (BatSet.max_elt n_set_y) - n)) acc
          | MUL -> Cfg.update_instr node (COPYC(x, (BatSet.max_elt n_set_y) * n)) acc
          | DIV -> Cfg.update_instr node (COPYC(x, (BatSet.max_elt n_set_y) / n)) acc
          | LT -> Cfg.update_instr node (COPYC(x, if ((BatSet.max_elt n_set_y) < n) then 1 else 0)) acc
          | LE -> Cfg.update_instr node (COPYC(x, if ((BatSet.max_elt n_set_y) <= n) then 1 else 0)) acc
          | GT -> Cfg.update_instr node (COPYC(x, if ((BatSet.max_elt n_set_y) > n) then 1 else 0)) acc
          | GE -> Cfg.update_instr node (COPYC(x, if ((BatSet.max_elt n_set_y) >= n) then 1 else 0)) acc
          | EQ -> Cfg.update_instr node (COPYC(x, if ((BatSet.max_elt n_set_y) = n) then 1 else 0)) acc 
          | AND -> Cfg.update_instr node (COPYC(x, if ((BatSet.max_elt n_set_y)!=0 && n!=0) then 1 else 0)) acc
          | OR -> Cfg.update_instr node (COPYC(x, if ((BatSet.max_elt n_set_y)!=0 || n!=0) then 1 else 0)) acc
        ) else (
            acc
        )

      )

      | ASSIGNU(x, uop, y)-> (
        (*find reaching definition for y*)
        let reaching_definitions = filter_node nodes (Table.find node in_table) y in 
        let n_set_y = extract_copyc_consts_set reaching_definitions in 
        let v_set_y = extract_copy_variable_set reaching_definitions in
         if (BatSet.is_singleton n_set_y)&&(BatSet.is_empty v_set_y) then (
          match uop with
          | MINUS ->(
            Cfg.update_instr node (COPYC(x, -(BatSet.max_elt n_set_y))) acc
          ) 
          | NOT -> (
            Cfg.update_instr node (COPYC(x, (if (BatSet.max_elt n_set_y)=0 then 1 else 0))) acc
          )
        ) else (
            acc
        )
      )

      | COPY(x, y) -> (
        (*find out reaching definition*)
        let reaching_definitions = filter_node nodes (Table.find node in_table) y in 
        let v_set_y = extract_copy_variable_set reaching_definitions in
        let n_set_y = extract_copyc_consts_set reaching_definitions in 
        if (BatSet.is_singleton n_set_y)&&(BatSet.is_empty v_set_y) then (
          Cfg.update_instr node (COPYC(x, BatSet.max_elt n_set_y)) acc
         ) else acc
      ) 
      | _ -> acc
  ) cfg nodes


(*variable propagation -*)
let variable_propagation cfg in_table = 
  let nodes = Cfg.nodesof cfg in 
  List.fold_left (
    fun acc node ->
      let nodes = Cfg.nodesof acc in 
      let inst = Node.get_instr node in
      match inst with
      | ASSIGNV(x, bop, y, z) -> (

        (*find reaching definition for y*)
        let reaching_definitions = filter_node nodes (Table.find node in_table) y in 
        let v_set_y = extract_copy_variable_set reaching_definitions in 
        let n_set_y = extract_copyc_consts_set reaching_definitions in 
        (*find reaching definition for z*)
        let reaching_definitions = filter_node nodes (Table.find node in_table) z in 
        let v_set_z = extract_copy_variable_set reaching_definitions in 
        let n_set_z = extract_copyc_consts_set reaching_definitions in 

        (*both are singletone*)
        if (BatSet.is_singleton v_set_y)&&(BatSet.is_singleton v_set_z)&&(BatSet.is_empty n_set_y)&&(BatSet.is_empty n_set_z) then (
          Cfg.update_instr node (ASSIGNV(x,bop,BatSet.max_elt v_set_y ,BatSet.max_elt v_set_z)) acc
        ) else (
          if (BatSet.is_singleton v_set_z)&&(BatSet.is_empty n_set_z) then (
            Cfg.update_instr node (ASSIGNV(x,bop,y ,BatSet.max_elt v_set_z)) acc
          ) else (
            if (BatSet.is_singleton v_set_y)&&(BatSet.is_empty n_set_y) then (
               Cfg.update_instr node (ASSIGNV(x,bop,BatSet.max_elt v_set_y ,z)) acc
            ) else acc
          )
        )
      )


      | ASSIGNC(x, bop, y, n) -> (
        (*find reaching definition for y*)
        let reaching_definitions = filter_node nodes (Table.find node in_table) y in 
        let v_set_y = extract_copy_variable_set reaching_definitions in 
        let n_set_y = extract_copyc_consts_set reaching_definitions in 
        if (BatSet.is_singleton v_set_y)&&(BatSet.is_empty n_set_y) then (
          Cfg.update_instr node (ASSIGNC(x,bop, BatSet.max_elt v_set_y , n)) acc
        ) else (
            acc
        )
      )

      | ASSIGNU(x, uop, y)-> (
        (*find reaching definition for y*)
        let reaching_definitions = filter_node nodes (Table.find node in_table) y in 
        let v_set_y = extract_copy_variable_set reaching_definitions in 
        let n_set_y = extract_copyc_consts_set reaching_definitions in 
         if (BatSet.is_singleton v_set_y)&&(BatSet.is_empty n_set_y) then (
          Cfg.update_instr node (ASSIGNU(x,uop, BatSet.max_elt v_set_y)) acc
        ) else (
            acc
        )
      )

      | COPY(x, y) -> (
        (*find out reaching definition*)
        let reaching_definitions = filter_node nodes (Table.find node in_table) y in 
        let v_set = extract_copy_variable_set reaching_definitions in 
        let n_set_y = extract_copyc_consts_set reaching_definitions in
        if (BatSet.is_singleton v_set)&&(BatSet.is_empty n_set_y) then (
          Cfg.update_instr node (COPY(x, BatSet.max_elt v_set)) acc
         ) else (acc)
      ) 

      | LOAD(x, (a, i))->(
        let reaching_definitions = filter_node nodes (Table.find node in_table) i in 
        let v_set = extract_copy_variable_set reaching_definitions in 
        let n_set_y = extract_copyc_consts_set reaching_definitions in
        if (BatSet.is_singleton v_set)&&(BatSet.is_empty n_set_y) then (
          Cfg.update_instr node (LOAD(x, (a, BatSet.max_elt v_set))) acc
         ) else (acc)
      )
      | STORE((a, i), x) -> (
         (*find reaching definition for y*)
        let reaching_definitions = filter_node nodes (Table.find node in_table) i in 
        let v_set_y = extract_copy_variable_set reaching_definitions in 
        let n_set_y = extract_copyc_consts_set reaching_definitions in 
        (*find reaching definition for z*)
        let reaching_definitions = filter_node nodes (Table.find node in_table) x in 
        let v_set_z = extract_copy_variable_set reaching_definitions in 
        let n_set_z = extract_copyc_consts_set reaching_definitions in 

        (*both are singletone*)
        if (BatSet.is_singleton v_set_y)&&(BatSet.is_singleton v_set_z)&&(BatSet.is_empty n_set_y)&&(BatSet.is_empty n_set_z) then (
          Cfg.update_instr node (STORE((a, BatSet.max_elt v_set_y), BatSet.max_elt v_set_z)) acc
        ) else (
          if (BatSet.is_singleton v_set_z)&&(BatSet.is_empty n_set_z) then (
            Cfg.update_instr node (STORE((a, i), BatSet.max_elt v_set_z)) acc
          ) else (
            if (BatSet.is_singleton v_set_y)&&(BatSet.is_empty n_set_y) then (
              Cfg.update_instr node (STORE((a, BatSet.max_elt v_set_y), x)) acc
            ) else acc
          )
        )
      )
      | WRITE(x) -> (
        let reaching_definitions = filter_node nodes (Table.find node in_table) x in 
        let v_set = extract_copy_variable_set reaching_definitions in 
        let n_set_y = extract_copyc_consts_set reaching_definitions in
        if (BatSet.is_singleton v_set)&&(BatSet.is_empty n_set_y) then (
          Cfg.update_instr node (WRITE(BatSet.max_elt v_set)) acc
         ) else (acc)
      )
      | _ -> acc
  ) cfg nodes

(*Optimize for COPY
  ex.
  tn = x + 1
  x = .tn
*)

let extract_assignv_instr (nodeset : NodeSet.t) : NodeSet.t =
  NodeSet.fold (fun node acc ->
    match Node.get_instr node with
    | ASSIGNV (x, _, y, z) ->if (String.compare x y)!=0 &&  (String.compare x z)!=0 then (NodeSet.add node acc) else (acc)
    | _ -> acc
  ) nodeset NodeSet.empty

let extract_assignc_instr (nodeset : NodeSet.t) : NodeSet.t =
  NodeSet.fold (fun node acc ->
    match Node.get_instr node with
    | ASSIGNC (x, _, y, _) ->if (String.compare x y)!=0 then (NodeSet.add node acc) else (acc)
    | _ -> acc
  ) nodeset NodeSet.empty

let extract_assignu_instr (nodeset : NodeSet.t) : NodeSet.t =
  NodeSet.fold (fun node acc ->
    match Node.get_instr node with
    | ASSIGNU (x, _, y) ->if (String.compare x y)!=0 then  (NodeSet.add node acc) else (acc)
    | _ -> acc
  ) nodeset NodeSet.empty

(* Make sure there are no instrs in predset of COPY while propagation*)
let exchange_to_assignv cfg nodes in_table = 
  List.fold_left (
    fun acc node ->
      let nodes = Cfg.nodesof acc in 
      let inst = Node.get_instr node in
      match inst with
      | COPY(x, y) -> (
          let reaching_definitions = filter_node nodes (Table.find node in_table) y in
          let assignv_set = extract_assignv_instr reaching_definitions in 
          if (List.length (NodeSet.elements assignv_set) = 1) then (
            match Node.get_instr (NodeSet.max_elt assignv_set) with
            | ASSIGNV(_, bop, y', z') -> if (NodeSet.mem (NodeSet.max_elt assignv_set) (Cfg.preds node acc)) then Cfg.update_instr node (ASSIGNV(x, bop, y', z')) acc else acc
            (*DO NOT HAPPEN*)
            | _ -> acc
          ) else (acc)
        )
      | _ -> acc
  ) cfg nodes 

let exchange_to_assignc cfg nodes in_table = 
  List.fold_left (
    fun acc node ->
      let nodes = Cfg.nodesof acc in 
      let inst = Node.get_instr node in
      match inst with
      | COPY(x, y) -> (
          let reaching_definitions = filter_node nodes (Table.find node in_table) y in
          let assignv_set = extract_assignc_instr reaching_definitions in 
          if (List.length (NodeSet.elements assignv_set) = 1) then (
            match Node.get_instr (NodeSet.max_elt assignv_set) with
            | ASSIGNC(_, bop, y', z') -> if (NodeSet.mem (NodeSet.max_elt assignv_set) (Cfg.preds node acc)) then Cfg.update_instr node (ASSIGNC(x, bop, y', z')) acc else acc
            (*DO NOT HAPPEN*)
            | _ -> acc
          ) else (acc)
        )
      | _ -> acc
  ) cfg nodes 

let exchange_to_assignu cfg nodes in_table = 
  List.fold_left (
    fun acc node ->
      let nodes = Cfg.nodesof acc in 
      let inst = Node.get_instr node in
      match inst with
      | COPY(x, y) -> (
          let reaching_definitions = filter_node nodes (Table.find node in_table) y in
          let assignv_set = extract_assignc_instr reaching_definitions in 
          if (List.length (NodeSet.elements assignv_set) = 1) then (
            match Node.get_instr (NodeSet.max_elt assignv_set) with
            | ASSIGNU(_, uop, y') -> if (NodeSet.mem (NodeSet.max_elt assignv_set) (Cfg.preds node acc)) then Cfg.update_instr node (ASSIGNU(x, uop, y')) acc else acc
            (*DO NOT HAPPEN*)
            | _ -> acc
          ) else (acc)
        )
      | _ -> acc
  ) cfg nodes 


let copy_propagation cfg in_table = 
  let nodes = Cfg.nodesof cfg in 
  let ret = exchange_to_assignv cfg nodes in_table in 
  let ret = exchange_to_assignc ret nodes in_table in 
  exchange_to_assignu ret nodes in_table

module Table2= struct 
  type t = var BatSet.t NodeMap.t
  let empty = NodeMap.empty 
  let add = NodeMap.add
  let init ns = List.fold_right (fun n -> add n BatSet.empty) ns empty
  let find : Node.t -> t -> var BatSet.t 
  =fun n t -> try NodeMap.find n t with _ -> BatSet.empty 
end;;

let def node = 
  let instr = Node.get_instr node in 
  match instr with
  | ASSIGNV(x, _, _,_) 
  | ASSIGNU(x,_,_) 
  | COPY(x, _)          
  | COPYC(x,_)       
  | LOAD(x,_)         
  | READ(x)
    -> BatSet.singleton x
  | _ -> BatSet.empty;;     
  
let use node = 
  let instr = Node.get_instr node in 
  match instr with
  | ASSIGNV(_, _, y, z) -> (let ret = BatSet.empty in let ret = BatSet.add y ret in BatSet.add z ret)
  | ASSIGNC(_, _, y, _) ->(let ret = BatSet.empty in BatSet.add y ret)
  | ASSIGNU(_, _, y) -> (let ret = BatSet.empty in BatSet.add y ret)
  | COPY(_, y) -> (let ret = BatSet.empty in BatSet.add y ret)
  | LOAD(_, (a, i)) -> (let ret = BatSet.empty in let ret = BatSet.add a ret in BatSet.add i ret)
  | STORE((a, i), x) -> (let ret = BatSet.empty in let ret = BatSet.add a ret in let ret = BatSet.add x ret in BatSet.add i ret)
  | WRITE(x) -> (let ret = BatSet.empty in BatSet.add x ret)
  | CJUMP(x,_) -> (let ret = BatSet.empty in BatSet.add x ret)
  | CJUMPF(x,_) -> (let ret = BatSet.empty in BatSet.add x ret)
  | _ -> BatSet.empty


let compute_table_for_lva nodes in_table out_table cfg = 
  List.fold_left (
    fun (prev_in, prev_out) node -> 
      let succs = Cfg.succs node cfg in 
      let new_in_set = BatSet.union (use node) (BatSet.diff (Table2.find node prev_out) (def node)) in 
      let new_in = Table2.add node new_in_set prev_in in 
      let new_out_set = NodeSet.fold (
          fun node acc -> 
            BatSet.union acc (Table2.find node new_in)
        ) succs BatSet.empty in 
      let new_out = Table2.add node new_out_set prev_out in 
      (new_in, new_out)
  ) (in_table, out_table) nodes


let delete_dead_code (cfg: Cfg.t) (nodes: Node.t list) (out_table: Table2.t) = 
  List.fold_left (
    fun acc node -> 
      let inst = Node.get_instr node in
      match inst with
      | ASSIGNV(x,_,_,_) 
      | ASSIGNC(x,_,_,_) 
      | ASSIGNU(x,_,_ ) 
      | COPY(x,_) 
      | COPYC(x,_)
      | LOAD(x,_) 
      | READ(x) 
      | ALLOC(x, _) -> (if (BatSet.mem x (Table2.find node out_table)) then acc else (Cfg.remove_node node acc))
      | _ -> acc
  ) cfg nodes


let delete_skip (cfg: Cfg.t) (nodes: Node.t list) = 
  List.fold_left (
    fun acc node -> 
      let inst = Node.get_instr node in
      match inst with
      | SKIP -> (
        let pred_node = NodeSet.max_elt(Cfg.succs node acc) in 
        if (Node.get_instr pred_node)=SKIP then acc else (
        let succ_node = NodeSet.max_elt(Cfg.succs node acc) in 
        let label = Node.get_label node in 
        let label_moved = Cfg.update_label succ_node label acc in 
        Cfg.remove_node node label_moved)
      )
      | _ -> acc
  ) cfg nodes


let optimize (pgm : program) : program =
  (*RDA*)
  let cfg = t_2_cfg pgm in
  let nodes = Cfg.nodesof cfg in 
  let in_table = Table.init nodes in 
  let out_table = Table.init nodes in 
  let (in_table, _) = solver nodes in_table out_table cfg compute_table_for_rda in  
  (*
  let _ = List.fold_left (
  fun _ node -> 
    let _ = print_endline "node: " in 
    let _ = print_endline ((string_of_int (Node.get_nodeid node))^" "^(Node.to_string node)) in 
     let _ = print_endline "in: " in 
    let in_set = Table.find node in_table in 
    let _ = print_string "{" in 
    let _ = BatSet.fold (fun e _ -> 
      print_string ((string_of_int e) ^ " ")
      ) in_set () in
    let out_set = Table.find node out_table in 
    let _ = print_endline "}" in 
     let _ = print_endline "out" in 
    let _ = print_string "{" in 
    let _ = BatSet.fold (fun e _ -> 
      print_string ((string_of_int e) ^ " ")
      ) out_set () in  
    print_endline "}\n\n"
  ) () (Cfg.nodesof cfg) in 
*)
  let propagated = constant_propagation cfg in_table in 
  let propagated = variable_propagation propagated in_table in
  let propagated = copy_propagation propagated in_table in 

  (*LVA*)
  let in_table = Table2.init (Cfg.nodesof propagated) in 
  let out_table = Table2.init (Cfg.nodesof propagated) in 
  let (_, out_table) = solver (Cfg.nodesof propagated) in_table out_table cfg compute_table_for_lva in
(*let _ = List.fold_left (
  fun _ node -> 
    let _ = print_endline "node: " in 
    let _ = print_endline ((string_of_int (Node.get_nodeid node))^" "^(Node.to_string node)) in 
     let _ = print_endline "in: " in 
    let in_set = Table2.find node in_table in 
    let _ = print_string "{" in 
    let _ = BatSet.fold (fun e _ -> 
      print_string ((e) ^ " ")
      ) in_set () in
    let out_set = Table2.find node out_table in 
    let _ = print_endline "}" in 
     let _ = print_endline "out" in 
    let _ = print_string "{" in 
    let _ = BatSet.fold (fun e _ -> 
      print_string ((e) ^ " ")
      ) out_set () in  
    print_endline "}\n\n"
  ) () (Cfg.nodesof propagated) in *)
  let propagated = delete_dead_code propagated (Cfg.nodesof propagated) out_table in 
  let propagated = t_2_cfg (cfg_2_t propagated) in 
  let propagated = delete_skip propagated (Cfg.nodesof propagated) in 

  cfg_2_t propagated