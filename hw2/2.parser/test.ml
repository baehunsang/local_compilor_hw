#use "topfind";;
#require "batteries";;
#require "base";;
#mod_use "util.ml";;
#mod_use "parse.ml";;

open Base;;
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
          let _ = print_endline "" in 
          let _ = print_endline ("cur: "^(string_of_symbol src)) in 
          let _ = print_endline "" in 
          let _ = BatSet.iter (fun f -> print_endline ("symbols: "^(string_of_symbol f))) d_syms in 
          FIRST.add_set src d_syms acc
          ) pr first_map in 
        let _ = print_endline "" in
        let _ = print_string (FIRST.tostring next) in 
        if BatMap.equal (fun v1 v2 -> BatSet.equal v1 v2) next first_map then first_map else loop next in 
    
    loop init_first;;

let first_map = find_first cfg1;;

let _ = print_endline "";;

let _ = print_string (FIRST.tostring first_map);;

    
    