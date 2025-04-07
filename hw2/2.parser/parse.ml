open Util

type symbol = T of string | N of string | Epsilon | End
type production = symbol * symbol list
type cfg = symbol list * symbol list * symbol * production list

let string_of_symbol s = 
  match s with 
  | T x -> x 
  | N x -> x 
  | Epsilon -> "epsilon"
  | End -> "$"

let string_of_prod (lhs, rhs) = 
    string_of_symbol lhs ^ " -> " ^ 
      string_of_list ~first:"" ~last:"" ~sep:" " string_of_symbol rhs 

module FIRST = struct 
  type t = (symbol, symbol BatSet.t) BatMap.t

  let empty = BatMap.empty 
  
  let find : symbol -> t -> symbol BatSet.t 
  =fun s t -> try BatMap.find s t with _ -> BatSet.empty 
  
  let add : symbol -> symbol -> t -> t 
  =fun s1 s2 t -> BatMap.add s1 (BatSet.add s2 (find s1 t)) t
  
  let add_set : symbol -> symbol BatSet.t -> t -> t 
  =fun s1 ss t -> BatSet.fold (fun s2 -> add s1 s2) ss t

  let tostring : t -> string
  =fun t -> 
    BatMap.foldi (fun s ss str -> 
      str ^ string_of_symbol s ^ " |-> " ^ string_of_set string_of_symbol ss ^ "\n"
    ) t ""
end   

module FOLLOW = struct
  type t = (symbol, symbol BatSet.t) BatMap.t 

  let empty = BatMap.empty 

  let find : symbol -> t -> symbol BatSet.t 
  =fun s t -> try BatMap.find s t with _ -> BatSet.empty 

  let add : symbol -> symbol -> t -> t 
  =fun s1 s2 t -> BatMap.add s1 (BatSet.add s2 (find s1 t)) t

  let add_set : symbol -> symbol BatSet.t -> t -> t 
  =fun s1 ss t -> BatSet.fold (fun s2 -> add s1 s2) ss t

  let tostring : t -> string
  =fun t -> 
    BatMap.foldi (fun s ss str -> 
      str ^ string_of_symbol s ^ " |-> " ^ string_of_set string_of_symbol ss ^ "\n"
    ) t ""
end

module ParsingTable = struct
  type t = (symbol * symbol, (symbol * symbol list) BatSet.t) BatMap.t 

  let empty = BatMap.empty 

  let find (nonterm, term) t = try BatMap.find (nonterm, term) t with _ -> BatSet.empty 

  let add (nonterm, term) prod t = 
    BatMap.add (nonterm, term) (BatSet.add prod (find (nonterm, term) t)) t
    
  let tostring : t -> string 
  =fun t -> 
    BatMap.foldi (fun (nonterm, term) prods str -> 
      str ^ string_of_symbol nonterm ^ ", " ^ string_of_symbol term ^ " |-> " ^
        string_of_set string_of_prod prods ^ "\n"
    ) t ""
    
  let foldi = BatMap.foldi 

  let for_all = BatMap.for_all
end

let rec first_of_symbols: symbol list-> FIRST.t->symbol BatSet.t = 
  fun syms first_map -> 
    match syms with
    (*Dst is epsilon | all First(Nonterminal) contains epsilon*)
    | [] -> BatSet.singleton Epsilon
    (*else*)
    | sym::sym_next -> 
      let f_sym = FIRST.find sym first_map in 
      let f_sym_wo_e = BatSet.remove Epsilon f_sym in 
      if BatSet.mem Epsilon f_sym then BatSet.union (first_of_symbols sym_next first_map) f_sym_wo_e else f_sym_wo_e

let find_first : cfg->FIRST.t = 
  fun cfg ->
    let (t, nt, _, pr) = cfg in 
    let all_symbols = t@nt in  

    (*init firstmap for all terminal symbols *)
    let init_first = 
      Util.list_fold 
      (fun f acc -> 
        match f with
        | T _ -> FIRST.add f f acc
        | N _ -> acc
        | Epsilon -> FIRST.add Epsilon Epsilon acc
        | End -> FIRST.add End End acc
        )
      all_symbols 
      FIRST.empty in
    
    (*fixed point loop*)
    let rec loop = 
      fun first_map -> 
        let next = Util.list_fold 
        (fun f acc -> 
          let src, dst = f in 
          let d_syms = first_of_symbols dst acc in 
 
          FIRST.add_set src d_syms acc
          ) pr first_map in 

        if BatMap.equal (fun v1 v2 -> BatSet.equal v1 v2) next first_map then first_map else loop next in 
    
    loop init_first

let find_follow: cfg->FIRST.t-> FOLLOW.t = 
fun cfg first_map->
  let (_, _, start_symbol, prods) = cfg in

  (*initialize followset*)
  let init_follow = FOLLOW.empty in 
  let init_follow = FOLLOW.add start_symbol End init_follow in 

  (*fixed point loop*)
  let rec loop = 
    fun follow_map -> 
      let next = Util.list_fold 
      (
        fun (src, dst) acc -> 
          let len = List.length dst in

          
          let rec for_loop i follow =
            if i >= len then

              follow
            else
              let cur_sym = List.nth dst i in
            
              match cur_sym with 
              | N _ -> 
                let beta = Util.drop (i+1) (dst) in 
                
                let first_beta = first_of_symbols beta first_map in 
                let first_beta_wo_e = BatSet.remove Epsilon first_beta in
                let next_follow = FOLLOW.add_set cur_sym first_beta_wo_e follow in
                let next_follow = 
                  if BatSet.mem Epsilon first_beta then
                    FOLLOW.add_set cur_sym (FOLLOW.find src next_follow) next_follow
                  else 
                    next_follow in 
                for_loop (i+1) next_follow
              | _ -> 
                for_loop (i+1) follow
            in 
          for_loop 0 acc 
      ) prods follow_map in 

      if BatMap.equal (BatSet.equal) next follow_map then follow_map else loop next in 
  loop init_follow

let construct_parsing_table: cfg->FIRST.t->FOLLOW.t->ParsingTable.t =
fun cfg first_map follow_map ->
  let (_, _, _, prods) = cfg in  
  (*for prod in prods*)
  let rec for_prod_in prods ret_table = 
    match prods with 
    | [] -> ret_table
    | prod::next -> 
      let src, alpha = prod in
      let first_alpha = first_of_symbols alpha first_map in 
      
      (*[1]*)
      let ret_table = 
        BatSet.fold 
        (
          fun sym table -> 
            match sym with 
            | T _ -> 
              ParsingTable.add (src, sym) prod table
            | _ -> table
        ) 
        first_alpha 
        ret_table in 
      
      (*[2]*)
      let ret_table = 
        if BatSet.mem Epsilon first_alpha then
            let follow_src = FOLLOW.find src follow_map in
            let ret_table =  
            BatSet.fold 
            (
              fun sym table ->
                match sym with 
                | T _ -> 
                  ParsingTable.add (src, sym) prod table
                | _ -> table
            ) 
            follow_src 
            ret_table in 

            if BatSet.mem End follow_src then 
              ParsingTable.add (src, End) prod ret_table
            else
              ret_table
        else
          ret_table in 
      for_prod_in next ret_table in 
  for_prod_in prods ParsingTable.empty

let map_all m = 
  ParsingTable.foldi
  (fun _ v acc -> 
    ((BatSet.cardinal v)=1)&&acc
    )
  m 
  true
  


let check_LL1 : cfg -> bool
=fun cfg -> 
  let first_map = find_first cfg in 

  let follow_map = find_follow cfg first_map in 

  let parsing_table = construct_parsing_table cfg first_map follow_map in 

  map_all parsing_table (* TODO *)


let parse : cfg -> symbol list -> bool
=fun cfg _ ->
  let first_map = find_first cfg in 

  let follow_map = find_follow cfg first_map in 

  let _ = construct_parsing_table cfg first_map follow_map in 
  false 
  
