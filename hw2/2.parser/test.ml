#use "topfind";;
#require "batteries";;
#require "base";;
#mod_use "util.ml";;
#mod_use "parse.ml";;

open Util;;
open Parse;;

let cfg1 = (
  [N "E"; N "E'"; N "T"; N "T'"; N "F"], 
  [T "+"; T "*"; T "("; T ")"; T "id"], 
  N "E",
  [
    (N "E", [N "T"; N "E'"]);
    (N "E'", [T "+"; N "T"; N "E'"]);
    (N "E'", []);
    (N "T", [N "F"; N "T'"]);
    (N "T'", [T "*"; N "F"; N "T'"]);
    (N "T'", []);
    (N "F", [T "("; N "E"; T ")"]);
    (N "F", [T "id"])
  ]);;

let cfg2 = (
  [N "S"; N "E"; N "E'"; N "T"; N "T'"; N "F"],
  [T "+"; T "-"; T "*"; T "/"; T "id"; T "num"; T "("; T ")"],
  N "S",
  [
      (N "S", [N "E"]);
      (N "E", [N "T"; N "E'"]);
      (N "E'", [T "+"; N "T"; N "E'"]);
      (N "E'", [T "-"; N "T"; N "E'"]);
      (N "E'", []);
      (N "T", [N "F"; N "T'"]);
      (N "T'", [T "*"; N "F"; N "T'"]);
      (N "T'", [T "/"; N "F"; N "T'"]);
      (N "T'", []);
      (N "F", [T "id"]);
      (N "F", [T "num"]);
      (N "F", [T "("; N "E" ;T ")"]);
  ]
);;

let cfg3 = (
  [N "X"; N "Y"; N "Z"],
  [T "a"; T"c"; T"d"], 
  N "X", 
  [
    (N "X", [N "Y"]);
    (N "X", [T "a"]);
    (N "Y", [T "c"]);
    (N "Y", []);
    (N "Z", [T "d"]);
    (N "Z", [N "X"; N "Y"; N "Z"])
  ]
);;

let cfg4 = (
  [N "S"; N "S'"; N "E"],
  [T "a"; T "b"; T "e"; T "i"; T "t"],
  N "S",
  [
   (N "S", [T "i"; N "E"; T "t"; N "S"; N "S'"]);
   (N "S", [T "a"]);
   (N "S'", [T "e"; N "S"]);
   (N "S'", []);
   (N "E", [T "b"])
  ] 
);;

let s1 = [T "id"; T "+"; T "id"; T "*"; T "id"; End];;
let s2 = [T "id"; T "/"; T "("; T "num"; T "+"; T "id"; T ")"; End];;

let rec first_of_symbols: symbol list-> FIRST.t->symbol BatSet.t = 
  fun syms first_map -> 
    match syms with
    (*Dst is epsilon | all First(Nonterminal) contains epsilon*)
    | [] -> BatSet.singleton Epsilon
    (*else*)
    | sym::sym_next -> 
      let f_sym = FIRST.find sym first_map in 
      let f_sym_wo_e = BatSet.remove Epsilon f_sym in 
      if BatSet.mem Epsilon f_sym then BatSet.union (first_of_symbols sym_next first_map) f_sym_wo_e else f_sym_wo_e;;

  
let find_first : cfg->FIRST.t = 
  fun cfg ->
    let (t, nt, s, pr) = cfg in 
    let all_symbols = t@nt in  

    (*for all terminal symbols *)
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
    
    let _ = print_endline (FIRST.tostring init_first) in 

    let rec loop = 
      fun first_map -> 
        let next = Util.list_fold 
        (fun f acc -> 
          let src, dst = f in 
          let d_syms = first_of_symbols dst acc in 

          FIRST.add_set src d_syms acc
          ) pr first_map in 

        if BatMap.equal (BatSet.equal) next first_map then first_map else loop next in 
    
    loop init_first;;

let first_map = find_first cfg1;;

let _ = print_endline "[*] first map";;
let _ = print_endline (FIRST.tostring first_map);;
(*-----------------------------FOLLOW-------------------------------------------------------------------------------*)



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

let follow = find_follow cfg1 first_map;;
let _ = print_string (FOLLOW.tostring follow);;
