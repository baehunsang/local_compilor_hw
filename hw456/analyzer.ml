open G 

exception NotImplemented
exception DivByZero

module type Interval = sig
  type integer = PlusInf | MinusInf | Int of int 
  type t = Bot | Range of integer * integer 
  val bot : t
  val top : t 
  val one : t 
  val zero : t 
  val from_int : int -> t 
  val from_bounds : integer -> integer -> t
  val order : t -> t -> bool
  val join : t -> t -> t
  val meet : t -> t -> t
  val widen : t -> t -> t
  val narrow : t -> t -> t
  val add : t -> t -> t
  val mul : t -> t -> t
  val sub : t -> t -> t
  val div : t -> t -> t
  val eq : t -> t -> t
  val not : t -> t
  val le : t -> t -> t
  val lt : t -> t -> t 
  val ge : t -> t -> t 
  val gt : t -> t -> t 
  val band : t -> t -> t
  val bor : t -> t -> t
  val to_string : t -> string
end

module Interval : Interval = struct
  type integer = PlusInf | MinusInf | Int of int 
  type t = Bot | Range of integer * integer 
  let bot = Bot 
  let top = Range (MinusInf, PlusInf)
  let one = Range (Int 1, Int 1)
  let zero = Range (Int 0, Int 0)
  let string_of_integer i = 
    match i with
    | PlusInf -> "+oo"
    | MinusInf -> "-oo"
    | Int n -> string_of_int n 
  let to_string i = 
    match i with 
    | Bot -> "Bot"
    | Range (i1, i2) -> "[" ^ string_of_integer i1 ^ ", " ^ string_of_integer i2 ^ "]"
  let from_int n = Range (Int n, Int n)
  let from_bounds i1 i2 = Range (i1, i2)

  let le_int (i1:integer) (i2:integer) = 
      match i1,i2 with
      | Int(n1), Int(n2) -> n1 <= n2
      | MinusInf, Int(_) -> true
      | _, MinusInf -> false
      | Int(_), PlusInf -> true
      | PlusInf, _ -> false
      | MinusInf, PlusInf -> true

  let ge_int (i1:integer) (i2:integer) = 
     match i1,i2 with
     | Int(n1), Int(n2) -> n1 >= n2
     | MinusInf, _ -> false
     | Int(_) , MinusInf -> true
     | PlusInf, Int(_) -> true
     | _, PlusInf -> false
     | PlusInf, MinusInf -> true

  let min (i1:integer) (i2:integer) = 
    if (le_int i1 i2) then i1 else i2

  let max (i1:integer) (i2:integer) = 
    if not(le_int i1 i2) then i1 else i2

  let order a b = 
  match a,b with
  | Bot,_ -> true
  | _,Bot -> false
  | Range(l1, u1), Range(l2, u2) -> (le_int l2 l1) && (le_int u1 u2)
  let join a b = 
  match a, b with
  | Bot, _ -> b
  | _, Bot -> a
  | Range(l1, u1), Range(l2, u2)-> Range((min l1 l2), (max u1 u2))
  let meet a b = 
    match a, b with
    | Bot, _ -> Bot
    | _, Bot -> Bot
    | Range(l1, u1), Range(l2, u2) ->(
      if ((le_int l1 l2)&&(le_int l2 u1)) then Range(l2, u1) else
        (if ((le_int l2 l1)&&(le_int l1 u2)) then Range(l1, u2) else Bot)
      )
  let widen a b =
    match a, b with
    | Bot, _ -> b
    | _, Bot -> a
    | Range(l1, u1), Range(l2, u2) -> 
      Range(
        (if not(le_int l1 l2) then MinusInf else l1),
        (if not(ge_int u1 u2) then PlusInf else u1)
      ) 

  let narrow a b = 
    match a, b with
    | Bot, _ -> Bot
    | _, Bot -> Bot
    | Range(l1, u1), Range(l2, u2) ->
      Range(
        (if l1=MinusInf then l2 else l1),
        (if u1=PlusInf then u2 else u1)
      ) 

  let add a b = 
    match a, b with
    | Range (MinusInf, PlusInf), _ -> (top)
    | _, Range (MinusInf, PlusInf) -> (top)
    | Range(Int n1, Int n2), Range(Int n3, Int n4) -> Range(Int(n1 + n3), Int(n2+n4))
    | Range(MinusInf , Int n2), Range(Int _ , Int n4) -> Range(MinusInf, Int(n2+n4))
    | Range(Int n1 , PlusInf), Range(Int n3 , Int _) -> Range(Int(n1+n3), PlusInf)
    | Range(Int _, Int n2), Range(MinusInf , Int n4) -> Range(MinusInf, Int(n2+n4))
    | Range(Int n1 , Int _), Range(Int n3 , PlusInf) -> Range(Int(n1+n3), PlusInf)
    | Range(MinusInf, Int n2), Range(MinusInf, Int n4) -> Range(MinusInf, Int(n2+n4))
    | Range(MinusInf, Int _), Range(Int _, PlusInf) -> (top)
    | Range(Int _, PlusInf), Range(MinusInf, Int _) -> (top)
    | Range(Int n1, PlusInf), Range(Int n3, PlusInf) -> (Range(Int(n1+n3), PlusInf))
    | _, _ -> Bot
      
  let mul_int i1 i2 = 
    match i1, i2 with
    | PlusInf, Int n -> if n > 0 then PlusInf else (if n=0 then Int 0 else MinusInf)
    | Int n, PlusInf -> if n > 0 then PlusInf else (if n=0 then Int 0 else MinusInf)
    | MinusInf, Int n -> if n > 0 then MinusInf else (if n=0 then Int 0 else PlusInf)
    | Int n, MinusInf -> if n > 0 then MinusInf else (if n=0 then Int 0 else PlusInf)
    | PlusInf, MinusInf -> MinusInf
    | MinusInf, PlusInf -> MinusInf
    | PlusInf, PlusInf -> PlusInf
    | MinusInf, MinusInf -> PlusInf
    | Int n1, Int n2 -> Int (n1*n2)

  let mul a b = 
    match a, b with
    | Range (MinusInf, PlusInf), _ -> (top)
    | _, Range (MinusInf, PlusInf) -> (top)
    | Range(Int 0, Int 0), _ -> Range(Int 0, Int 0)
    | _, Range(Int 0, Int 0) -> Range(Int 0, Int 0)
    | Range(n1, n2), Range(n3, n4) -> Range(
      (List.fold_left (fun acc e-> min acc e) (PlusInf) [(mul_int n1 n3);(mul_int n1 n4);(mul_int n2 n3);(mul_int n2 n4)]), 
      (List.fold_left (fun acc e-> max acc e) (MinusInf) [(mul_int n1 n3);(mul_int n1 n4);(mul_int n2 n3);(mul_int n2 n4)]))
    | _, _ -> Bot


  let sub a b = 
    match a, b with
    | Range (MinusInf, PlusInf), _ -> (top)
    | _, Range (MinusInf, PlusInf) -> (top)
    | Range(Int n1, Int n2), Range(Int n3, Int n4) -> (Range(Int(n1 - n4), Int(n2-n3)))
    | Range(MinusInf , Int n2), Range(Int n3 , Int _) -> (Range(MinusInf, Int(n2-n3)))
    | Range(Int n1 , PlusInf), Range(Int _ , Int n4) -> (Range(Int(n1-n4), PlusInf))
    | Range(Int n1, Int _), Range(MinusInf , Int n4) -> (Range(Int(n1-n4), PlusInf))
    | Range(Int _ , Int n2), Range(Int n3 , PlusInf) -> (Range(MinusInf, Int(n2-n3)))
    | Range(MinusInf, Int _), Range(MinusInf, Int _) -> (top)
    | Range(MinusInf, Int n2), Range(Int n3, PlusInf) -> (Range(MinusInf, Int(n2-n3)))
    | Range(Int n1, PlusInf), Range(MinusInf, Int n4) -> (Range(Int(n1-n4), PlusInf))
    | Range(Int _, PlusInf), Range(Int _, PlusInf) -> (top)
    | _, _ -> Bot

  let div_int i1 i2 = 
    match i1, i2 with
    | PlusInf, Int n -> if n > 0 then PlusInf else (if n=0 then raise DivByZero else MinusInf)
    | Int n, PlusInf -> if n > 0 then Int 0 else (if n=0 then Int 0 else Int 0)
    | MinusInf, Int n -> if n > 0 then MinusInf else (if n=0 then raise DivByZero else PlusInf)
    | Int n, MinusInf -> if n > 0 then Int 0 else (if n=0 then Int 0 else Int 0)
    | PlusInf, MinusInf -> MinusInf
    | MinusInf, PlusInf -> MinusInf
    | PlusInf, PlusInf -> PlusInf
    | MinusInf, MinusInf -> PlusInf
    | Int n1, Int n2 -> Int (n1/n2)


  let div a b =
    match b with
    | Bot -> Bot
    | Range(l, u) -> 
      if ((le_int (l) (Int 0))&&(le_int (Int 0) (u))) then Bot else 
        (
          match a,b with
          | Range(MinusInf, PlusInf),_ -> top
          | Range(Int 0, Int 0), _ -> Range(Int 0, Int 0)
          | Range(n1, n2), Range(n3, n4) -> Range(
            (List.fold_left (fun acc e-> min acc e) (PlusInf) [(div_int n1 n3);(div_int n1 n4);(div_int n2 n3);(div_int n2 n4)]), 
            (List.fold_left (fun acc e-> max acc e) (MinusInf) [(div_int n1 n3);(div_int n1 n4);(div_int n2 n3);(div_int n2 n4)]))
          | _, _ -> Bot
        )
  let eq a b = 
    match a,b with
    | Range(l1, u1), Range(l2, u2) -> 
      if ((l1=u1)&&(l2=u2)&&(u1=l2)) then one else (
        if ((not(ge_int u1 l2))||(not(ge_int u2 l1))) then zero else top
      )
    | _, _ -> top 

  let le a b = 
    match a, b with
    | Range(l1, u1), Range(l2, u2) -> 
      if (le_int u1 l2) then one else 
        (if not(le_int l1 u2) then zero else top)
    | _, _ -> top

  let lt a b = 
    match a, b with
    | Range(l1, u1), Range(l2, u2) ->
      if not(ge_int u1 l2) then one else 
        (if (ge_int l1 u2) then zero else top)
    | _, _ -> top

  let ge a b = 
    match a, b with
    | Range(l1, u1), Range(l2, u2) -> 
      if (le_int u2 l1) then one else 
        (if not(le_int l2 u1) then zero else top)
    | _, _ -> top

  let gt a b = 
    match a, b with
    | Range(l1, u1), Range(l2, u2) -> 
      if not(ge_int u2 l1) then one else 
        (if (ge_int l2 u1) then zero else top)
    | _,_ -> top
  let not b =
    match b with
    | Range(Int 0, Int 0) -> one
    | Range(Int 1, Int 1) -> zero
    | _ -> top 

  let band a b = 
    match a, b with
    | Range(Int 0, Int 0), _ -> zero
    | _, Range(Int 0, Int 0) -> zero
    | Range(Int 1, Int 1), Range(Int 1, Int 1) -> one 
    | _, _ -> top
  let bor a b = 
    match a, b with
    | Range(Int 0, Int 0), Range(Int 0, Int 0) -> zero 
    | Range(Int 1, Int 1), _ -> one 
    | _, Range(Int 1, Int 1) -> one 
    | _, _ -> top
end

type allocsite = int 
let string_of_allocsite l = "l" ^ string_of_int l

module AbsLoc = struct
  type t = Var of string | Allocsite of allocsite 
  let from_var x = Var x 
  let from_allocsite a = Allocsite a 
  let to_string a = 
    match a with 
    | Var x -> x 
    | Allocsite l -> string_of_allocsite l  
end 

module AbsArray = struct
  type t = allocsite BatSet.t * Interval.t 
  let bot = (BatSet.empty, Interval.bot)
  let get_allocsites (a, _) = a
  let get_size (_, sz) = sz
  let create l n = (BatSet.singleton l, Interval.from_int n)
  let join (a1, sz1) (a2, sz2) = (BatSet.union a1 a2, Interval.join sz1 sz2)
  let widen (a1, sz1) (a2, sz2) = (BatSet.union a1 a2, Interval.widen sz1 sz2)
  let narrow (a1, sz1) (a2, sz2) = (BatSet.intersect a1 a2, Interval.narrow sz1 sz2)
  let order (a1, sz1) (a2, sz2) = BatSet.subset a1 a2 && Interval.order sz1 sz2
  let to_string : t -> string 
  =fun (a, sz) -> Printf.sprintf "(%s, %s)" (Utils.string_of_set string_of_allocsite a) (Interval.to_string sz)
end 

module AbsVal = struct
  type t = Interval.t * AbsArray.t
  let bot = (Interval.bot, AbsArray.bot)
  let from_itv itv = (itv, AbsArray.bot)
  let from_absarr a = (Interval.bot, a)
  let get_interval (i, _) = i 
  let get_absarray (_, a) = a
  let join (i1, a1) (i2, a2) = (Interval.join i1 i2, AbsArray.join a1 a2)
  let meet_itv itv (i, a) = (Interval.meet itv i, a)
  let widen (i1, a1) (i2, a2) = (Interval.widen i1 i2, AbsArray.widen a1 a2)
  let narrow (i1, a1) (i2, a2) = (Interval.narrow i1 i2, AbsArray.narrow a1 a2)
  let order (i1, a1) (i2, a2) = Interval.order i1 i2 && AbsArray.order a1 a2
  let add (i1, a1) (i2, a2) = (Interval.add i1 i2, AbsArray.join a1 a2)
  let mul (i1, a1) (i2, a2) = (Interval.mul i1 i2, AbsArray.join a1 a2)
  let sub (i1, a1) (i2, a2) = (Interval.sub i1 i2, AbsArray.join a1 a2)
  let div (i1, a1) (i2, a2) = (Interval.div i1 i2, AbsArray.join a1 a2)
  let le (i1, a1) (i2, a2) = (Interval.le i1 i2, AbsArray.join a1 a2)
  let lt (i1, a1) (i2, a2) = (Interval.lt i1 i2, AbsArray.join a1 a2)
  let ge (i1, a1) (i2, a2) = (Interval.ge i1 i2, AbsArray.join a1 a2)
  let gt (i1, a1) (i2, a2) = (Interval.gt i1 i2, AbsArray.join a1 a2)
  let eq (i1, a1) (i2, a2) = (Interval.eq i1 i2, AbsArray.join a1 a2)
  let not (i, a) = (Interval.not i, a)
  let band (i1, a1) (i2, a2) = (Interval.band i1 i2, AbsArray.join a1 a2)
  let bor (i1, a1) (i2, a2) = (Interval.bor i1 i2, AbsArray.join a1 a2)
  let to_string : t -> string 
  =fun (itv, arr) -> Printf.sprintf "(%s, %s)" (Interval.to_string itv) (AbsArray.to_string arr)
end 

module type AbsMem = sig
  type t = (AbsLoc.t, AbsVal.t) BatMap.t
  val empty : t
  val find : AbsLoc.t -> t -> AbsVal.t 
  val find_set : AbsLoc.t BatSet.t -> t -> AbsVal.t 
  val add : AbsLoc.t -> AbsVal.t -> t -> t
  val add_set : AbsLoc.t BatSet.t -> AbsVal.t -> t -> t 
  val strong_update : AbsLoc.t -> AbsVal.t -> t -> t
  val weak_update : AbsLoc.t -> AbsVal.t -> t -> t
  val join : t -> t -> t 
  val widen : t -> t -> t 
  val narrow : t -> t -> t
  val order : t -> t -> bool 
  val print : t -> unit 
end

module AbsMem : AbsMem = struct
  type t = (AbsLoc.t, AbsVal.t) BatMap.t
  let empty = BatMap.empty
  let find x m = try BatMap.find x m with _ -> AbsVal.bot
  let find_set xs m = BatSet.fold (fun x -> AbsVal.join (find x m)) xs AbsVal.bot 
  let strong_update loc v m = BatMap.add loc v m 
  let weak_update loc v m = BatMap.add loc (AbsVal.join (find loc m) v) m
  let add loc v m = 
    match loc with 
    | AbsLoc.Var _ -> strong_update loc v m 
    | AbsLoc.Allocsite _ -> weak_update loc v m 
  let add_set locs v m = 
    if BatSet.cardinal locs = 1 then add (BatSet.choose locs) v m 
    else BatSet.fold (fun loc -> weak_update loc v) locs m 
  let join m1 m2 = BatMap.foldi (fun x v m' -> add x (AbsVal.join v (find x m')) m') m1 m2
  let widen m1 m2 = BatMap.foldi (fun x v m' -> add x (AbsVal.widen v (find x m')) m') m1 m2
  let narrow m1 m2 = BatMap.foldi (fun x v m' -> add x (AbsVal.narrow v (find x m')) m') m1 m2
  let order m1 m2 = BatMap.for_all (fun x v -> AbsVal.order v (find x m2)) m1
  let print m = 
    BatMap.iter (fun x v -> 
      prerr_endline (AbsLoc.to_string x ^ " |-> " ^ AbsVal.to_string v)
    ) m 
end

module type Table = sig
  type t = AbsMem.t NodeMap.t
  val empty : t
  val init : Node.t list -> t 
  val find : Node.t -> t -> AbsMem.t 
  val add : Node.t -> AbsMem.t -> t -> t
  val print : t -> unit
end 

module Table : Table = struct 
  type t = AbsMem.t NodeMap.t
  let empty = NodeMap.empty 
  let add = NodeMap.add
  let init ns = List.fold_right (fun n -> add n AbsMem.empty) ns empty
  let find : Node.t -> t -> AbsMem.t 
  =fun n t -> try NodeMap.find n t with _ -> AbsMem.empty
  let print t = NodeMap.iter (fun n m -> 
    prerr_endline (string_of_int (Node.get_nodeid n)); 
    AbsMem.print m; 
    prerr_endline "") t  
end

let rec abs_eval : S.exp->AbsMem.t->AbsVal.t
=fun e m ->
  match e with
  | NUM n -> AbsVal.from_itv (Interval.from_int n)
  | LV lv -> 
    let locations = abs_eval_lv lv m in 
    BatSet.fold (fun elt acc -> AbsVal.join (AbsMem.find elt m ) acc) locations AbsVal.bot
  | ADD(e1, e2) -> AbsVal.add (abs_eval e1 m) (abs_eval e2 m)
  | SUB(e1, e2) -> AbsVal.sub (abs_eval e1 m) (abs_eval e2 m)
  | MUL(e1, e2) -> AbsVal.mul (abs_eval e1 m) (abs_eval e2 m)
  | DIV(e1, e2) -> AbsVal.div (abs_eval e1 m) (abs_eval e2 m)
  | MINUS e -> AbsVal.mul (abs_eval e m) (AbsVal.from_itv (Interval.from_int (-1)))
  | NOT e -> AbsVal.not (abs_eval e m)
  | LT(e1, e2) -> AbsVal.lt (abs_eval e1 m) (abs_eval e2 m)
  | LE(e1, e2) -> AbsVal.le (abs_eval e1 m) (abs_eval e2 m)
  | GT(e1, e2) -> AbsVal.gt (abs_eval e1 m) (abs_eval e2 m)
  | GE(e1, e2) -> AbsVal.ge (abs_eval e1 m) (abs_eval e2 m)
  | EQ(e1, e2) -> AbsVal.eq (abs_eval e1 m) (abs_eval e2 m)
  | AND(e1, e2) -> AbsVal.band (abs_eval e1 m) (abs_eval e2 m)
  | OR(e1, e2) -> AbsVal.bor (abs_eval e1 m) (abs_eval e2 m)


and abs_eval_lv : S.lv->AbsMem.t->AbsLoc.t BatSet.t
=fun lv m ->
  match lv with
  | ID x -> BatSet.singleton (AbsLoc.Var x)
  | ARR(x, _) -> 
    let _, arr_val = AbsMem.find (AbsLoc.Var x) m in 
    let allocsites, _ = arr_val in 
    BatSet.fold (fun elt acc -> BatSet.add (AbsLoc.Allocsite elt) acc) allocsites BatSet.empty

let new_allocsite : unit -> int =
  let id =  ref 0 in 
    fun _ -> (id := !id + 1; !id)

let prune (b: S.exp) (m: AbsMem.t) = 
  match (AbsVal.get_interval (abs_eval b m)) with
  | Interval.Range(Interval.Int 1, Interval.Int 1) -> m
  | Interval.Range(Interval.Int 0, Interval.Int 0) -> AbsMem.empty 
  | Interval.Range(MinusInf, PlusInf) -> (
    match b with
    | LT(LV(ID x), e) -> 
        (match AbsVal.get_interval (abs_eval e m), AbsVal.get_interval (AbsMem.find (AbsLoc.Var x) m) with
        | Range(Int l, _), Range(Int l_org, _) -> 
          let new_val = if (l_org<=(l-1)) then  AbsVal.from_itv (Interval.Range(Int l_org, Int (l - 1))) else AbsVal.bot in 
          AbsMem.strong_update (AbsLoc.Var x) new_val m 
        | _,_ -> m)
    | LT(e, LV(ID x)) -> 
        (match AbsVal.get_interval (abs_eval e m), AbsVal.get_interval (AbsMem.find (AbsLoc.Var x) m) with
        | Range(_, Int u), Range(_, Int u_org)  -> 
          let new_val = if ((u+1)<=u_org) then AbsVal.from_itv (Interval.Range(Int (u + 1), Int u_org)) else AbsVal.bot in 
          AbsMem.strong_update (AbsLoc.Var x) new_val m 
        | _, _ -> m)
    | GT(LV(ID x), e) -> 
      ( match AbsVal.get_interval (abs_eval e m), AbsVal.get_interval (AbsMem.find (AbsLoc.Var x) m) with
        | Range(_, Int u), Range(_, Int u_org)  -> 
            let new_val = if (u+1<=u_org) then AbsVal.from_itv (Interval.Range(Int (u + 1), Int u_org)) else AbsVal.bot in 
            AbsMem.strong_update (AbsLoc.Var x) new_val m 
        | _, _ -> m)
    | GT(e, LV(ID x)) -> 
      (
        match AbsVal.get_interval (abs_eval e m) , AbsVal.get_interval (AbsMem.find (AbsLoc.Var x) m) with
        | Range(Int l, _),Range(Int l_org, _) ->  
          let new_val = if (l_org<=l-1) then AbsVal.from_itv (Interval.Range(Int l_org, Int (l - 1))) else AbsVal.bot in 
          AbsMem.strong_update (AbsLoc.Var x) new_val m 
        | _, _ -> m
      )
    | LE(LV(ID x), e) -> 
      (match AbsVal.get_interval (abs_eval e m), AbsVal.get_interval (AbsMem.find (AbsLoc.Var x) m) with
        | Range(Int l, _), Range(Int l_org, _) -> 
          let new_val = if (l_org<=(l)) then  AbsVal.from_itv (Interval.Range(Int l_org, Int (l))) else AbsVal.bot in 
          AbsMem.strong_update (AbsLoc.Var x) new_val m 
        | _,_ -> m)
    | LE(e, LV(ID x)) -> 
        (match AbsVal.get_interval (abs_eval e m), AbsVal.get_interval (AbsMem.find (AbsLoc.Var x) m) with
        | Range(_, Int u), Range(_, Int u_org)  -> 
          let new_val = if ((u)<=u_org) then AbsVal.from_itv (Interval.Range(Int (u), Int u_org)) else AbsVal.bot in 
          AbsMem.strong_update (AbsLoc.Var x) new_val m 
        | _, _ -> m)
    | GE(LV(ID x), e) ->
      ( match AbsVal.get_interval (abs_eval e m), AbsVal.get_interval (AbsMem.find (AbsLoc.Var x) m) with
        | Range(_, Int u), Range(_, Int u_org)  -> 
            let new_val = if (u<=u_org) then AbsVal.from_itv (Interval.Range(Int (u), Int u_org)) else AbsVal.bot in 
            AbsMem.strong_update (AbsLoc.Var x) new_val m 
        | _, _ -> m)
    | GE(e, LV(ID x)) -> 
      (
        match AbsVal.get_interval (abs_eval e m) , AbsVal.get_interval (AbsMem.find (AbsLoc.Var x) m) with
        | Range(Int l, _),Range(Int l_org, _) ->  
          let new_val = if (l_org<=l) then AbsVal.from_itv (Interval.Range(Int l_org, Int (l))) else AbsVal.bot in 
          AbsMem.strong_update (AbsLoc.Var x) new_val m 
        | _, _ -> m
      )
    | EQ(LV(ID x), e) -> 
      (
        let e_interval = AbsVal.get_interval (abs_eval e m) in
        let x_interval  = AbsVal.get_interval (AbsMem.find (AbsLoc.Var x) m) in
        let new_val = AbsVal.from_itv (Interval.meet e_interval x_interval) in 
        AbsMem.strong_update (AbsLoc.Var x) new_val m 
      )
    | EQ(e, LV(ID x)) -> 
      (
        let e_interval = AbsVal.get_interval (abs_eval e m) in
        let x_interval  = AbsVal.get_interval (AbsMem.find (AbsLoc.Var x) m) in
        let new_val = AbsVal.from_itv (Interval.meet e_interval x_interval) in 
        AbsMem.strong_update (AbsLoc.Var x) new_val m 
      )
    | _ -> m
  )
  | _-> AbsMem.empty

let transfer : Node.t -> AbsMem.t -> AbsMem.t
= fun node m -> 
  match Node.get_instr node with
  | I_alloc(id, size) -> 
    (let new_arr = AbsArray.create (new_allocsite ()) (size) in 
    let new_mem = AbsMem.add (Var id) (Interval.bot, new_arr) AbsMem.empty in 
    let allocsites = AbsArray.get_allocsites new_arr in
    let to_join = BatSet.fold (fun e acc -> AbsMem.add (Allocsite (e)) (Range(Int 0, Int 0), AbsArray.bot) acc) allocsites new_mem in 
    AbsMem.join m to_join
    
    )

  | I_assign(lv, e) -> 
    let loc_set = abs_eval_lv lv m in 
    let abs_val = abs_eval e m in 
    if BatSet.is_singleton (loc_set) then 
      (
        BatSet.fold (fun elt acc -> AbsMem.strong_update elt abs_val acc) loc_set m
      )
    else
      (
        BatSet.fold (fun elt acc -> AbsMem.join acc (AbsMem.weak_update elt abs_val acc)) loc_set m
      ) 
  | I_skip -> m
  | I_assume b -> prune b m 
  | I_read id -> 
    AbsMem.strong_update (AbsLoc.Var id) (Interval.top, AbsArray.bot) m
  | I_print _ -> m

let fixpoint : Cfg.t -> Table.t
=fun _ -> Table.empty

let inspect : Cfg.t -> Table.t -> bool 
=fun _ _ -> true 

let analyze : Cfg.t -> bool 
=fun cfg -> 
  cfg 
  |> fixpoint  
  |> inspect cfg 