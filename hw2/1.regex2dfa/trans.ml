open Regex 

exception Not_implemented

let regex2nfa : Regex.t -> Nfa.t 
=fun regex -> 
  match regex with
  | Empty -> Nfa.create_new_nfa ()
  | Epsilon -> 
    let new_nfa = Nfa.create_new_nfa () in 
    let new_st, new_nfa = Nfa.create_state new_nfa in 
    let new_nfa = Nfa.add_final_state new_nfa new_st in 
    Nfa.add_epsilon_edge new_nfa (Nfa.get_initial_state new_nfa , new_st) 
    
  | _ -> raise Not_implemented

let nfa2dfa : Nfa.t -> Dfa.t
=fun _ -> raise Not_implemented (* TODO *)
 
(* Do not modify this function *)
let regex2dfa : Regex.t -> Dfa.t
=fun regex -> 
  let nfa = regex2nfa regex in
  let dfa = nfa2dfa nfa in
    dfa

let run_dfa : Dfa.t -> alphabet list -> bool
=fun _ _ -> raise Not_implemented (* TODO *)
