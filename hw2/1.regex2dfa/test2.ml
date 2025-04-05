#use "topfind";;
#require "batteries";;



type state  = int
type states = state BatSet.t

(* 예시 집합 *)
let st : states = BatSet.of_list [3; 1; 4; 1; 5]   (* 중복은 자동 제거 *)

(* 1) BatSet.iter : 부작용 함수 실행 ------------------------------------------------ *)
let () =
  BatSet.iter (fun s -> Printf.printf "state = %d\n" s) st
;;
(* 출력 예
   state = 1
   state = 3
   state = 4
   state = 5
*)

(* 2) BatSet.fold : 누적값 만들기 ---------------------------------------------------- *)
let sum =
  BatSet.fold (fun s acc -> acc + s) st 0
;;
let _ = Printf.printf ("sum of states = %d\n") sum;;      (* → 13 *)

(* 3) enum / to_list : 다른 컨테이너로 변환 후 표준 함수 사용 ------------------------ *)
let lst   = BatSet.to_list st;;          (* [1;3;4;5] *)
let array = BatSet.to_array st;;         (* [|1;3;4;5|] *)
let () =
  List.iter (Printf.printf "from list: %d\n") lst;;

