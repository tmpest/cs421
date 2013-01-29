
open Mp2common

(* TODO: complete cases for each listed expression construct.
   You will need a function to process a list of expressions. *)

(*
let rec removeExistingId lis curr = match lis with
		h::t	->	if h = curr then t else h::(removeExistingId t curr)
	|	[]	->	[];; *)

let rec alldeclaredExpWraped vars e = match e with
          Operation(e1,_,e2) -> (alldeclaredExp vars e1) && (alldeclaredExp vars e2)
        | Subscript(e1,e2) -> (alldeclaredExp vars e1) && (alldeclaredExp vars e2)
        | Length(e1) -> (alldeclaredExp vars e1)
        | MethodCall(e1,_,el) -> (alldeclaredExp vars e1) 
        | FieldRef(e1,_) -> alldeclaredExp vars e1
        | NewArray(_,e1) -> alldeclaredExp vars e1
        | Not(e1) -> alldeclaredExp vars e1
        | Id(s) -> removeExistingId vars s
        | _ -> if Length vars = 0 then true else false ;;
     
let rec initIsDeclaredList vars = match vars with
		h::t	->	false::initIsDeclaredList t
	|	[]		->	[];;

let rec allValuesDeclared lst = match lst with
		h::t	->	if h = true then allValuesDeclared t else false
	|	[]		->	true;;
        
let rec alldeclaredExp vars e = begin
	let decList = initIsDeclaredList vars;
	let finalDecList = alldeclaredExpWraped vars e decList;
	allValuesDeclared finalDecList
end;;

let rec adeOnExpressionList vars elist = match elist with
		h::t	->	(alldeclaredExp vars h) || (adeOnExpressionList vars t)
	|	[]		->	false;;
let rec alldeclaredSt vars st = true ;;

let rec alldeclaredClass (Class(c,s,vdl,mdl)) = true ;;

