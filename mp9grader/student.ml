open Mp9common
open Miniocamlast

let emptyStructuralEnv = []
let emptyFunctionalEnv = envError (* same as fun id -> envError id *)
let emptyEnv = emptyStructuralEnv

(* You may find it helpful to use the following function
   when defining the semantics of Equals *)

let rec zip (l1:'a list) (l2:'b list) : ('a * 'b) list =
  match (l1, l2) with
    ([], []) -> []
  | (x1 :: l1, x2 :: l2) -> (x1, x2) :: zip l1 l2
  | _ -> raise (TypeError ("Mismatched lists"))

(* Common between both the interpreter and reducer *)

let rec applyOp (bop:binary_operation) (v1:value) (v2:value) : value =
  match bop with
      Equals ->
        (match (v1, v2) with
            IntConst i1, IntConst i2 -> if i1 = i2 then True else False
          | StrConst s1, StrConst s2 -> if s1 = s1 then True else False
          | True, True -> True
          | True, False -> False
          | False, True -> False
          | False, False -> True
          | _ -> raise (TypeError "Can't Compare given values for Equality"))

    | NotEquals -> if True = (applyOp Equals v1 v2) then False else True

    | LessThan -> 
      (match (v1, v2) with
          IntConst i1, IntConst i2 -> if i1 < i2 then True else False
        | _ -> raise (TypeError "Incompatible types for Less Than"))

    | GreaterThan ->
      (match (v1, v2) with
          IntConst i1, IntConst i2 -> if i1 > i2 then True else False
        | _ -> raise (TypeError "Incompatible types for Greater Than"))

    | And -> 
      (match v1, v2 with 
        True, True -> True
      | True, False -> False
      | False, True -> False
      | False, False -> False
      | _ -> raise (TypeError "Incompatible types for And"))

    | Or -> 
      (match v1, v2 with 
        True, True -> True
      | True, False -> True
      | False, True -> True
      | False, False -> False
      | _ -> raise (TypeError "Incompatible types for Or"))

    | Plus -> 
      (match (v1, v2) with
          IntConst i1, IntConst i2 -> IntConst(i1 + i2)
          | _ -> raise (TypeError "Incompatible types for Plus"))

    | Minus -> 
      (match (v1, v2) with
          IntConst i1, IntConst i2 -> IntConst(i1 - i2)
          | _ -> raise (TypeError "Incompatible types for Minus"))

    | Div -> 
      (match (v1, v2) with
          IntConst i1, IntConst i2 -> if i2 <> 0 then IntConst(i1 / i2)
              else raise (RuntimeError "Division by Zero")
          | _ -> raise (TypeError "Incompatible types for Divide"))

    | Mult -> 
      (match (v1, v2) with
          IntConst i1, IntConst i2 -> IntConst(i1 * i2)
          | _ -> raise (TypeError "Incompatible types for Multiply"))

    | StringAppend -> 
      (match (v1, v2) with
          StrConst s1, StrConst s2 -> StrConst(s1 ^ s2)
          | _ -> raise (TypeError "Incompatible types for String Append"))

    | ListAppend -> 
      (match (v1, v2) with
          List lis1, List lis2 -> List(lis1 @ lis2)
          | _ -> raise (TypeError "Incompatible types for List Append"))
    | Cons -> 
      (match v2 with
          List lis -> List(v1 :: lis)
        | _ -> raise (TypeError "Incompatible types for Cons"))

    | _ -> raise (TypeError "No Binary Op")  

let rec applyUnop (bop:unary_operation) (v:value) : value =
  match bop with
      Not -> 
        (match v with
            True -> False
          | False -> True
          | _ -> raise (TypeError "Incompatible type for Not"))

    | Head ->
      (match v with
          List (h::t) -> h 
        | _ -> raise (TypeError "Incompatible type for Head"))

    | Tail -> 
      (match v with
          List ([]) -> List []
        | List (h::t) -> List t 
        | _ -> raise (TypeError "Incompatible type for Tail"))

    | Fst ->
      (match v with
        Tuple (h::t::[]) -> h 
        | _ -> raise (TypeError "Incompatible type for Fst"))

    | Snd ->
      (match v with
        Tuple (h::t::[]) -> t 
        | _ -> raise (TypeError "Incompatible type for Snd"))
    
    | _ -> raise (TypeError "No Uniary Op");;

(* Reducer *)

(* subst's signature below is the same as (id:id) (v:value) (exp:exp) -> exp,
   but is a big hint on how to write a helper function inside with the type
   exp -> exp (subst's id and value arguments don't change on recursive
   calls!) *)
let rec subst (id:id) (v:value) : exp -> exp =
  (* let rec helper : exp -> exp = match exp with
    Operation(e1, bop, e2) -> exp
  | UnaryOperation(uop, e) -> exp
  | Var(i) -> if i = id then v else exp
  | StrConst(s) -> exp
  | IntConst(i) -> exp
  | True -> exp
  | False -> exp
  | List(lis) -> exp
  | Tuple(lis) -> exp
  | If(e1, e2, e3) -> exp
  | Let(i, e1, e2) -> exp
  | Fun(i, e) -> exp
  | Rec(i, e) -> exp
  | App(e1, e2) -> exp *)
  failwith "not implemented"

let rec reduce (expr:exp) : exp = match expr with
     Operation(e1, bop, e2) -> let v = reduce e1 in let v' = reduce e2 in 
        applyOp bop v v'
  | UnaryOperation(uop, e1) -> let v = reduce e1 in applyUnop uop v
  | Var(v) -> Var v
  | StrConst(s) -> StrConst s
  | IntConst(i) -> IntConst i
  | True -> True
  | False -> False
  | List(lis) ->
    (match lis with
        [] -> List([])
      | h::t -> let v = reduce h in 
        (match (reduce (List t)) with
            List lis -> List(v :: lis)
            | _ -> raise (TypeError "Error in List during Reduce")))
  | Tuple lis -> 
    (match lis with
        h::t::[] -> Tuple((reduce h) :: ((reduce t) :: []))
      | _ -> raise (TypeError "Error in Tuple during Reduce"))
  | If(e1, e2, e3) -> 
    (match (reduce e1) with
          True -> reduce e2
        | False -> reduce e3
        | _ -> raise (TypeError "Error in If during Reduce"))
  | Let(a, e, e') -> let v = reduce e in reduce (subst a v e')
  | Fun(a, e) -> Fun(a, e)
  | Rec(f, Fun(a, e)) -> Fun(a, (subst f expr e))
  | App(e, e') ->
    (match (reduce e) with
        Fun(a, e'') -> let v' = reduce e' in reduce (subst a v' e'')
      | _ -> raise (TypeError "Error in App during Reduce")) 
  | _ -> raise (TypeError "No matching expression in Reduce");;

(* Interpreter *)

(*let rec fetch (id:id) (env:environment) : value option =
*)
let rec fetch (id:id) (env:environment) : value =
  failwith "not implemented"
  (* match env with
      [] -> raise (TypeError ("Unbound Variable: "^id))
    | (i, v)::t   ->  if i = id then v else fetch id t *)

let rec extend (id:id) (v:value) (env:environment) : environment =
  failwith "not implemented"
  (* env @ [(id, v)];; *)

let rec eval (expr:exp) (env:environment) : exp =
  failwith "not implemented"