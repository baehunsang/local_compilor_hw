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


let check_LL1 : cfg -> bool
=fun cfg -> 
  let first_map = find_first cfg in 
  let _ = print_endline "" in 
  let _ = print_endline "[*] first map" in 
  let _ = print_string (FIRST.tostring first_map) in 
  false (* TODO *)

let parse : cfg -> symbol list -> bool
=fun _ _ -> false (* TODO *)
