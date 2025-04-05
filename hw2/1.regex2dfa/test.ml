#use "topfind";;
#require "batteries";;
#mod_use "regex.ml";;
#mod_use "nfa.ml";;
open Regex;;
open Nfa;;

let a = create_new_nfa () in 
Nfa.print a;;