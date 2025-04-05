#use "topfind";;
#require "batteries";;
#mod_use "regex.ml";;
#mod_use "nfa.ml";;

exception Not_implemented;;
open Regex;;
open Nfa;;

let testcases : (Regex.t * alphabet list) list = 
  [ 
    (Empty, []);
    (Epsilon, []);
    (*
    (Alpha A, [A]);
    (Alpha A, [B]);
    (OR (Alpha A, Alpha B), [B]);
    (CONCAT (STAR (Alpha A), Alpha B), [B]);
    (CONCAT (STAR (Alpha A), Alpha B), [A;B]);
    (CONCAT (STAR (Alpha A), Alpha B), [A;A;B]);
    (CONCAT (STAR (Alpha A), Alpha B), [A;B;B]);
    (CONCAT (CONCAT (STAR (CONCAT (Alpha A, Alpha A)), STAR (CONCAT (Alpha B, Alpha B))), Alpha B), [B]);
    (CONCAT (CONCAT (STAR (CONCAT (Alpha A, Alpha A)), STAR (CONCAT (Alpha B, Alpha B))), Alpha B), [A;A;B]);
    (CONCAT (CONCAT (STAR (CONCAT (Alpha A, Alpha A)), STAR (CONCAT (Alpha B, Alpha B))), Alpha B), [B;B;B]);
    (CONCAT (CONCAT (STAR (CONCAT (Alpha A, Alpha A)), STAR (CONCAT (Alpha B, Alpha B))), Alpha B), [A;A;A;A;B;B;B]);
    (CONCAT (CONCAT (STAR (CONCAT (Alpha A, Alpha A)), STAR (CONCAT (Alpha B, Alpha B))), Alpha B), [A;A;A;B;B;B])
    *)
    ];;

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
  ;;
let _ = 
  List.iter (fun (regex, _) -> 
    Nfa.print (regex2nfa regex)
  ) testcases;;