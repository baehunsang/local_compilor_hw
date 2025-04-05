open Regex 

exception Not_implemented


let union_nfa: Nfa.t -> Nfa.t -> Nfa.t =
  fun r1 r2 -> 
    let base = Nfa.create_new_nfa () in 
    let r1_union_r2 = Nfa.add_states base (Nfa.get_states r1) in 
    let r1_union_r2 = Nfa.add_states r1_union_r2 (Nfa.get_states r2) in 
    let r1_union_r2 = Nfa.add_edges r1_union_r2 (Nfa.get_edges r2) in 
    let r1_union_r2 = Nfa.add_edges r1_union_r2 (Nfa.get_edges r1) in 
    let new_final, r1_union_r2 = Nfa.create_state r1_union_r2 in
    let r1_union_r2 = Nfa.add_final_state r1_union_r2 new_final in 
    let r1_union_r2 = Nfa.add_epsilon_edge r1_union_r2 (Nfa.get_initial_state r1_union_r2, Nfa.get_initial_state r1) in 
    let r1_union_r2 = Nfa.add_epsilon_edge r1_union_r2 (Nfa.get_initial_state r1_union_r2, Nfa.get_initial_state r2) in 
    let r1_finals = Nfa.get_final_states r1 in 
    let r1_union_r2 = BatSet.fold (fun f acc -> Nfa.add_epsilon_edge acc (f, new_final)) r1_finals r1_union_r2 in 
    let r2_finals = Nfa.get_final_states r2 in
    BatSet.fold (fun f acc -> Nfa.add_epsilon_edge acc (f, new_final)) r2_finals r1_union_r2

let concat_nfa: Nfa.t -> Nfa.t -> Nfa.t =
    fun r1 r2 -> 
      let base = Nfa.create_new_nfa () in 
      let r1_init = Nfa.get_initial_state r1 in
      let base_init = Nfa.get_initial_state base in 
      let states_from_r1 = BatSet.remove r1_init (Nfa.get_states r1) in 
      let r1_d_list, r1_ed_list = Nfa.get_edges r1 in
      let map_edge (s,a,d) = if s = r1_init then (base_init,a,d) else (s,a,d) in
      let map_eps  (s,d)   = if s = r1_init then (base_init,d)  else (s,d)   in 
      let d_list_to_add = List.map map_edge r1_d_list in 
      let ed_list_to_add = List.map map_eps r1_ed_list in
      let base = Nfa.add_states base states_from_r1 in 
      let base = Nfa.add_edges base (d_list_to_add, ed_list_to_add) in 
      let base = Nfa.add_states base (Nfa.get_states r2) in
      let base = Nfa.add_edges base (Nfa.get_edges r2) in 
      let base = BatSet.fold (fun f acc -> Nfa.add_final_state acc f) (Nfa.get_final_states r2) base in
      BatSet.fold (fun f acc -> Nfa.add_epsilon_edge acc (f, Nfa.get_initial_state r2)) (Nfa.get_final_states r1) base

let rec regex2nfa : Regex.t -> Nfa.t 
=fun regex -> 
  match regex with
  | Empty -> Nfa.create_new_nfa ()
  | Epsilon -> 
    (let new_nfa = Nfa.create_new_nfa () in 
    let new_st, new_nfa = Nfa.create_state new_nfa in 
    let new_nfa = Nfa.add_final_state new_nfa new_st in 
    Nfa.add_epsilon_edge new_nfa (Nfa.get_initial_state new_nfa , new_st))

  | Alpha al -> 
    (let new_nfa = Nfa.create_new_nfa () in 
    let new_st, new_nfa = Nfa.create_state new_nfa in 
    let new_nfa = Nfa.add_final_state new_nfa new_st in 
    Nfa.add_edge new_nfa (Nfa.get_initial_state new_nfa, al, new_st))
  
  | OR(r1, r2) -> 
    let complied_r1 = regex2nfa r1 in 
    let complied_r2 = regex2nfa r2 in 
    union_nfa complied_r1 complied_r2

  | CONCAT(r1, r2) -> 
    let complied_r1 = regex2nfa r1 in 
    let complied_r2 = regex2nfa r2 in 
    concat_nfa complied_r1 complied_r2

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
