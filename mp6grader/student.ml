open List
open Minijavaast
open Mp6common

(* Helper methods *)

let rec asgn (id:id) (v:value) (sigma:state) : state =
  match sigma with
     [] -> raise (TypeError ("Assignment to unbound varialbe " ^ id))
  | (id1,v1) :: t -> if id = id1 then (id,v) :: t
                     else (id1,v1) :: asgn id v t;;


let rec binds (id:id) (sigma:state) : bool =
  match sigma with
    [] -> false
  | (id', _)::t -> id=id' || binds id t

let rec fetch (id:id) (sigma:state) : value =
  match sigma with
    [] -> raise (TypeError ("Unbound variable: "^id))
  | (id', v)::t -> if id=id' then v else fetch id t

let rec mklist (i:int) (v:value) : value list =
       if i=0 then [] else v :: mklist (i-1) v

let rec zip (lis1:id list) (lis2:value list) : state =
  match (lis1, lis2) with
    ([], []) -> [] | (h1::t1, h2::t2) -> (h1,h2) :: zip t1 t2
  | _ -> raise (TypeError ("Mismatched formal and actual param lists"))

let zipscalar (lis:id list) (v:value) : state =
                                zip lis (mklist (length lis) v)

let rec varnames (varlis:var_decl list) : id list =
   match varlis with
     [] -> [] | (Var(_, s))::t -> s :: varnames t

let getMethodInClass (id:id) (Class(_, _, _, methlis)) : method_decl =
  let rec aux methlis = match methlis with
      [] -> raise (TypeError ("No such method: "^id))
    | (Method(_, m, _, _, _, _) as themethod) :: t ->
        if id=m then themethod else aux t
  in aux methlis

let getMethod (id:id) (Program classes) : method_decl =
  getMethodInClass id (hd classes)


(* START HERE *)
(*raise (NotImplemented "applyOp") *)

let applyOp (bop:binary_operation) (v1:value) (v2:value) : value =
  (*Plus, Minus, Multiplication, Division, LessThan, and Equal;*)
  match bop with
      (* Handles int+int, string concat with strings and int first and second*)
      Plus -> 
        (match (v1, v2) with
            (IntV i1, IntV i2) -> IntV(i1 + i2)
          | (IntV i1, StringV s2) -> StringV((string_of_value (IntV(i1))) ^ s2)
          | (StringV s1, IntV i2) -> StringV(s1 ^ (string_of_value (IntV(i2))))
          | (StringV s1, StringV s2) -> StringV(s1 ^ s2)
          | _ -> raise (TypeError "Type Error during Plus"))

    | Minus -> 
        (match (v1, v2) with 
            (IntV i1, IntV i2) -> IntV(i1 - i2)
          | _ -> raise (TypeError "Type Error during Minus")) 

    | Multiplication -> 
        (match (v1, v2) with
          (IntV i1, IntV i2) -> IntV(i1 * i2)
          | _ -> raise (TypeError "Type Error during Multiplication"))

    | Division -> 
        (match (v1, v2) with
            (IntV i1, IntV i2) -> if i2 != 0 then IntV(i1 / i2)
                                             else raise (RuntimeError
                                                "DivisionByZero")
          | _ -> raise (TypeError "Type Error during Division"))

    | LessThan -> 
        (match (v1, v2) with
            (IntV i1, IntV i2) -> BoolV(i1 < i2)
          | _ -> raise (TypeError "Type Error during LessThan"))

    | Equal -> 
        (match (v1, v2) with
            (BoolV b1, BoolV b2) -> BoolV(if b1 = b2 then true 
                                                     else false)
          | (StringV s1, StringV s2) -> BoolV(if s1 = s2 then true 
                                                         else false)
          | (IntV i1, IntV i2) -> BoolV(if i1 = i2 then true 
                                                   else false)
          | (NullV, NullV) -> BoolV(true)
          | (NullV, _) -> BoolV(false) 
          | (_, NullV) -> BoolV(false) 
          | _ -> raise (TypeError "Type Error during Equal"))
    (* Not sure what kind of error if BinOp is not present to raise, assuming
      it is a TypeError for now*)
    | _ -> raise (TypeError "Type Error during BinOp pattern matching");;

(* Main interpreter code *)

let rec eval (e:exp) (sigma:state) (prog:program) : value =
  match e with
      Integer i -> IntV i

    | True -> BoolV(true)

    | False -> BoolV(false)

    | Id i -> fetch i sigma  

    | Not ex -> let e = eval ex sigma prog in
        (match e with
            BoolV b -> BoolV(if b then false else true)
          | _ -> raise (TypeError "TypeError Not:Exp not of type BoolV"))
    
    | Null -> NullV
    
    | String s -> StringV s
    
    | Operation (e1, bop, e2) -> 
        (match bop with
            And -> 
              (match (eval e1 sigma prog) with
                  BoolV b -> if b then 
                    (match (eval e2 sigma prog) with
                        BoolV b -> BoolV(if b then true else false)
                        | _ -> raise (TypeError "TypeError on Exp2 of And"))                   
                                  else BoolV(false)

                | _ ->  raise (TypeError "TypeError on Exp1 of And"))

          | Or -> 
              (match (eval e1 sigma prog) with
                  BoolV b -> if b = false then 
                    (match (eval e2 sigma prog) with
                        BoolV b -> BoolV(if b then true else false)
                        | _ -> raise (TypeError "TypeError on Exp2 of Or"))                   
                                          else BoolV(true)

                | _ ->  raise (TypeError "TypeError on Exp1 of Or"))

          | _ -> let v1 = eval e1 sigma prog
                and v2 = eval e2 sigma prog in
                    applyOp bop v1 v2)

    | MethodCall (_, i, expLst) ->
      match getMethod i prog with
          Method (_, _, al, lvl, sl, ret) -> 
            evalMethodCall sl ret ((zip (varnames al) (evallist expLst sigma prog))
              @(zipscalar (varnames lvl) NullV)) prog
    
    | _ -> raise (NotImplemented "eval")

and evallist (el:exp list) (sigma:state) (prog:program) : value list =
  match el with
      [] -> []
    | h::t -> (eval h sigma prog)::(evallist t sigma prog) 

and evalMethodCall (stms:statement list) (retval:exp)
                          (sigma:state) (prog:program) : value =
  eval retval (execstmtlis stms sigma prog) prog

and execstmt (s:statement) (sigma:state) (prog:program) : state =
  match s with 
      Block sList -> execstmtlis sList sigma prog
    | If (e, s1, s2) -> 
        (match (eval e sigma prog) with
            BoolV true -> execstmt s1 sigma prog
          | BoolV false -> execstmt s2 sigma prog
          | _ -> raise (TypeError "TypeError with If"))

    | Assignment (id, e) -> 
      if binds id sigma 
        then 
          let v = eval e sigma prog in 
            asgn id v sigma
        else
          raise (TypeError "TypeError var not declared") 

    | _ -> raise (TypeError "TypeError with Statement")

and execstmtlis (sl:statement list) (sigma:state) (prog:program) : state =
  match sl with
      [] -> sigma
    | h::t -> execstmtlis t (execstmt h sigma prog) prog 

(* Run your program with these functions *)
let run_with_args (prog:program) (args:exp list) : string = 
  string_of_value (eval (MethodCall(Null, "main", args)) [] prog)

let run (prog:program) : string = run_with_args prog []

let eval_exp (prog:program) : string =
   let Program [Class(_, _, _, [meth])] = prog
   in let Method(_,_,_,_,_,retval) = meth
      in string_of_value (eval retval [] prog)
