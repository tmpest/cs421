(* CS421 - Spring 2013
 * MP1
 *)

(* Problem 1 *)
let pair_to_list (x, y) = [y; x];;

(* Problem 2 *)
let dist ((x0,y0), (x1,y1)) =
  sqrt((x1 -. x0)**2.0 +. (y1 -. y0)**2.0);;

(* Problem 3 *)
let sort_first_two l =
  match l with
    x::x'::xs -> if x > x' then x'::x::xs else x::x'::xs
  | l2        -> l2;;

(* Problem 4 *)
let rec concat_odd l =
  match l with
    []    -> ""
  | s::s'::ss -> s ^ concat_odd ss
  | s::[] -> s ;;

(* Problem 5 *)
let rec is_sorted l =
  match l with
  | []    -> true
  | x::[] -> true
  | x::x'::xs -> x <= x' & is_sorted (x'::xs);;

(* Problem 6 *)
let rec group_ascending lis = match lis with
      [] -> []
    | [a] -> [[a]]
    | a::t -> let (b::lis')::lis'' = group_ascending t
              in if a<b then (a::b::lis')::lis''
                        else [a] :: (b::lis') :: lis'' ;;

(* Problem 7 *)
let rec split_list lis = match lis with
      [] -> ([], [])
    | [a] -> ([a], [])
    | a::b::t -> let (l1, l2) = split_list t
                 in (a::l1, b::l2) ;;

(* or
let rec split_list lis = match lis with
      [] -> ([], [])
    | h::t -> let (l1, l2) = split_list t
              in (h::l2, l1) ;;
*)


(* Problem 8 *)
let rec merge l1 l2 =
  match l1, l2 with
  | _, [] -> l1
  | [], _ -> l2
  | x::xs, y::ys -> if x < y then x::(merge xs l2) else y::(merge l1 ys);;

(* Problem 9 *)
let rec mergesort lis = match lis with
      [] -> []
    | [a] -> [a]
    | _ -> let (l1, l2) = split_list lis
           in merge (mergesort l1) (mergesort l2) ;;

