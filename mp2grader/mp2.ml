
open Mp2common

(* TODO: complete cases for each listed expression construct.
   You will need a function to process a list of expressions. *)

let rec setDecTrue decLst n = match decLst with
		h::t	->	if n = 0 then true::t else h::(setDecTrue t (n-1)) 
	|	[]		->	[];;

let rec checkDecList decLst vars var n = if n >= List.length vars then decLst
		else if (List.nth vars n) = var then setDecTrue decLst n 
		else checkDecList decLst vars var (n + 1);; 



let rec alldeclaredExpWraped vars e decLst = match e with
          Operation(e1,_,e2) -> let lst = alldeclaredExpWraped vars e1 decLst in alldeclaredExpWraped vars e2 lst
        | Subscript(e1,e2) -> let lst = alldeclaredExpWraped vars e1 decLst in alldeclaredExpWraped vars e2 lst
        | Length(e1) -> alldeclaredExpWraped vars e1 decLst
        | MethodCall(e1,_,el) -> let lst = alldeclaredExpWraped vars e1 decLst in 
        	let rec alldecExpLst vars lst el = match el with
					h::t	->	let decList = alldeclaredExpWraped vars lst h in alldecExpLst vars decList t
				|	[]		->	lst;;
        | FieldRef(e1,_) -> alldeclaredExpWraped vars e1 decLst 
        | NewArray(_,e1) -> alldeclaredExpWraped vars e1 decLst
        | Not(e1) -> alldeclaredExpWraped vars e1 decLst
        | Id(s) -> checkDecList decLst vars s 0
        | _ -> decLst
     
let rec initIsDeclaredList vars = match vars with
		h::t	->	false::initIsDeclaredList t
	|	[]		->	[];;

let rec allValuesDeclared lst = match lst with
		h::t	->	if h = true then allValuesDeclared t else false
	|	[]		->	true;;
        
let rec alldeclaredExp vars e = 
	(
		let decList = initIsDeclaredList vars in
		let finalDecList = alldeclaredExpWraped vars e decList in
		allValuesDeclared finalDecList
	);;

let rec adeOnExpressionList vars elist = match elist with
		h::t	->	(alldeclaredExp vars h) || (adeOnExpressionList vars t)
	|	[]		->	false;;
let rec alldeclaredSt vars st = true ;;

let rec alldeclaredClass (Class(c,s,vdl,mdl)) = true ;;

