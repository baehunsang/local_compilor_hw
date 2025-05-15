open G

exception Not_implemented 

let tmp_index = ref 0
let label_index = ref 1
let new_temp() = tmp_index := !tmp_index + 1; ".t" ^ (string_of_int !tmp_index)
let new_label() = label_index := !label_index + 1; !label_index

(*************************************)
(*          translation to T         *)
(*************************************)
 
let rec trans_e: S.exp -> (T.var* T.program) = 
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
      let (t2, code2) = trans_e e2 in
      let (t1, code1) = trans_e e1 in 
      let new_t3 = new_temp () in 
      (new_t3, code1@code2@[(0, ASSIGNV(new_t3, ADD, t1, t2))])
      
    | SUB(e1, e2) -> 
      let (t2, code2) = trans_e e2 in
      let (t1, code1) = trans_e e1 in  
      let new_t3 = new_temp () in 
      (new_t3, code1@code2@[(0, ASSIGNV(new_t3, SUB, t1, t2))])
  
    | MUL(e1, e2) -> 
      let (t2, code2) = trans_e e2 in
      let (t1, code1) = trans_e e1 in  
      let new_t3 = new_temp () in 
      (new_t3, code1@code2@[(0, ASSIGNV(new_t3, MUL, t1, t2))])
  
    | DIV(e1, e2) -> 
      let (t2, code2) = trans_e e2 in
      let (t1, code1) = trans_e e1 in 
      let new_t3 = new_temp () in 
      (new_t3, code1@code2@[(0, ASSIGNV(new_t3, DIV, t1, t2))])
  
    | LT(e1, e2) -> 
      let (t2, code2) = trans_e e2 in
      let (t1, code1) = trans_e e1 in 
      let new_t3 = new_temp () in 
      (new_t3, code1@code2@[(0, ASSIGNV(new_t3, LT, t1, t2))])
  
    | LE(e1, e2) -> 
      let (t2, code2) = trans_e e2 in
      let (t1, code1) = trans_e e1 in 
      let new_t3 = new_temp () in 
      (new_t3, code1@code2@[(0, ASSIGNV(new_t3, LE, t1, t2))])
  
    | GT(e1, e2) -> 
      let (t2, code2) = trans_e e2 in
      let (t1, code1) = trans_e e1 in  
      let new_t3 = new_temp () in 
      (new_t3, code1@code2@[(0, ASSIGNV(new_t3, GT, t1, t2))])
  
    | GE(e1, e2) -> 
      let (t2, code2) = trans_e e2 in
      let (t1, code1) = trans_e e1 in  
      let new_t3 = new_temp () in 
      (new_t3, code1@code2@[(0, ASSIGNV(new_t3, GE, t1, t2))])
  
    | EQ(e1, e2) -> 
      let (t2, code2) = trans_e e2 in
      let (t1, code1) = trans_e e1 in  
      let new_t3 = new_temp () in 
      (new_t3, code1@code2@[(0, ASSIGNV(new_t3, EQ, t1, t2))])
  
    | AND(e1, e2) -> 
      let (t2, code2) = trans_e e2 in
      let (t1, code1) = trans_e e1 in 
      let new_t3 = new_temp () in 
      (new_t3, code1@code2@[(0, ASSIGNV(new_t3, AND, t1, t2))])
  
    | OR(e1, e2) -> 
      let (t2, code2) = trans_e e2 in
      let (t1, code1) = trans_e e1 in  
      let new_t3 = new_temp () in 
      (new_t3, code1@code2@[(0, ASSIGNV(new_t3, OR, t1, t2))])
  
    | MINUS(e) -> 
      let (t1, code1) = trans_e e in 
      let new_t2 = new_temp () in 
      (new_t2, code1@[(0, ASSIGNU(new_t2, MINUS, t1))])
  
    | NOT(e) -> 
      let (t1, code1) = trans_e e in 
      let new_t2 = new_temp () in 
      (new_t2, code1@[(0, ASSIGNU(new_t2, NOT, t1))])

let trans_d: S.decl->T.program = 
fun (t, id) ->
  match t with
  | TINT -> [(0, COPYC(id, 0))]
  | TARR(n) ->[(0, ALLOC(id, n))]
      
let rec trans_s: S.stmt -> T.program = 
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
    code1@[(0, T.CJUMP(t1, l_t))]@[(0, T.UJUMP l_f)]@[(l_t, T.SKIP)]@code_t@[(0, T.UJUMP l_x)]@[(l_f, T.SKIP)]@code_f@[(0, T.UJUMP l_x)]@[(l_x, T.SKIP)]
    

  | WHILE(e, stmt) -> 
    let (t1, code1) = trans_e e in 
    let code_b = trans_s stmt in 
    let l_e = new_label () in 
    let l_x = new_label () in 
    [(l_e, T.SKIP)]@code1@[(0, T.CJUMPF(t1, l_x))]@code_b@[(0, T.UJUMP l_e)]@[(l_x, T.SKIP)]
    

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
      
      
let s2t : S.program -> T.program
=fun s -> (trans_b s)@[(0, T.HALT)]

(*************************************)
(*     translation from S to Cfg     *)
(*************************************)

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

  Cfg.add_edge n1 n2 g


let cfg_decl :S.decl-> Cfg.t =
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
    Cfg.add_edge new_node new_exit new_cfg

let rec cfg_stmt: S.stmt -> Cfg.t = 
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

    let new_cfg = merge_cfg new_cfg cfg_S1 (assume1) (Cfg.get_entry cfg_S1) in

    let new_cfg = merge_cfg new_cfg cfg_S2 (assume2) (Cfg.get_entry cfg_S2) in

    let new_cfg = Cfg.add_edge (Cfg.get_exit cfg_S1) n2 new_cfg in

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

    let new_cfg = merge_cfg new_cfg cfg_S (assume1) (Cfg.get_entry cfg_S) in

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

    let new_cfg = merge_cfg new_cfg cfg_S (new_entry) (Cfg.get_entry cfg_S) in 

    let new_cfg = merge_cfg new_cfg cfg_while (Cfg.get_exit cfg_S) (Cfg.get_entry cfg_while) in
    let new_cfg = Cfg.add_node new_exit new_cfg in 

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

    let new_cfg = merge_cfg new_cfg cfg_block (new_entry) (Cfg.get_entry cfg_block) in 
    let new_cfg = Cfg.add_node new_exit new_cfg in 

    Cfg.add_edge (Cfg.get_exit cfg_block) (new_exit) new_cfg 

and cfg_b (d_list, s_list) =
  let entry = Node.create_skip () in
  let exit = Node.create_skip () in
  let init_cfg = Cfg.add_node entry Cfg.empty in

  (* declarations *)
  let d_cfg = List.fold_left (fun acc decl ->
    let decl_cfg = cfg_decl decl in
    merge_cfg acc decl_cfg (Cfg.get_exit acc) (Cfg.get_entry decl_cfg)
  ) init_cfg d_list in

  (* statements *)
  let s_cfg = List.fold_left (fun acc stmt ->
    let stmt_cfg = cfg_stmt stmt in
    merge_cfg acc stmt_cfg (Cfg.get_exit acc) (Cfg.get_entry stmt_cfg)
  ) d_cfg s_list in

  let final_cfg = Cfg.add_node exit s_cfg in
  Cfg.add_edge (Cfg.get_exit s_cfg) exit final_cfg



let s2cfg : S.program -> Cfg.t 
=fun s -> Cfg.remove_unnecessary_skips (cfg_b s)