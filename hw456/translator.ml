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

let s2cfg : S.program -> Cfg.t 
=fun s -> ignore s; Cfg.empty