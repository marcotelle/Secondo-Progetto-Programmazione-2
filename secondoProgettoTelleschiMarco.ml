(* Interprete di un'estensione di un semplice linguaggio funzionale didattico *)
(* che manipoli  tuple di  espressioni, e che permetta  di  combinare opportunamente  funzioni. *)

type variable = string ;;

type constant = Int of int | Bool of bool ;;

type operator = Plus | Minus | Times | Div | LessThan | LessThanEq ;;

(* Le espressioni. *)

type exp = 
  | Constant_e of constant
  | Op_e of exp * operator * exp
  | Var_e of variable
  | If_e of exp * exp * exp
  | Fun_e of variable * exp
  | FunCall_e of exp * exp
  | Let_e of variable * exp * exp
  | Letrec_e of variable * exp * exp
  | Etup of tuple
  | Pipe of tuple * exp
  | ManyTimes of int * exp * exp
and tuple = Nil
  | Seq of exp * tuple
;;

(* funzioni del run-time *)

(* Controllo per valori *)

let rec is_value (e:exp) : bool = 
  match e with 
    | Constant_e _ -> true
    | Fun_e (_,_) -> true
    | Etup (_) -> true
    | (Op_e (_,_,_) | Var_e _ | If_e (_,_,_)
      | FunCall_e (_,_) | Let_e (_,_,_)
      | Letrec_e (_,_,_)) | Pipe (_,_) | ManyTimes (_,_,_) -> false
;;

(* Casi possibili di run-time exception *)

exception UnboundVariable of variable ;;
exception BadApplication of exp ;;
exception BadIf of exp ;;
exception BadOp of exp * operator * exp ;;

(* Type checker *)

let typecheck (x,y) =
  match x with
  | "int" -> 
    (match y with
      | Constant_e (Int u) -> true
      | _ -> false)
  | "bool" -> 
    (match y with
      | Constant_e (Bool u) -> true
      | _ -> false)
  | _ -> failwith ("not a valid type")
;;

(* Decodifica delle operazioni di base *)

let apply_op v1 op v2 =
  match op with
    | Plus -> if typecheck ("int",v1) && typecheck ("int",v2)
      then (match v1, v2 with
        | Constant_e (Int i), Constant_e (Int j) -> Constant_e (Int (i+j))
        | _, _ -> failwith ("impossible"))
      else failwith ("type error")
    | Minus -> if typecheck ("int",v1) && typecheck ("int",v2)
      then (match v1, v2 with
        | Constant_e (Int i), Constant_e (Int j) -> Constant_e (Int (i-j))
        | _, _ -> failwith ("impossible"))
      else failwith ("type error")
    | Times -> if typecheck ("int",v1) && typecheck ("int",v2)
      then (match v1, v2 with
        | Constant_e (Int i), Constant_e (Int j) -> Constant_e (Int (i*j))
        | _, _ -> failwith ("impossible"))
      else failwith ("type error")
    | Div -> if typecheck ("int",v1) && typecheck ("int",v2)
      then (match v1, v2 with
        | Constant_e (Int i), Constant_e (Int j) -> Constant_e (Int (i/j))
        | _, _ -> failwith ("impossible"))
      else failwith ("type error")
    | LessThan -> if typecheck ("int",v1) && typecheck ("int",v2)
      then (match v1, v2 with
        | Constant_e (Int i), Constant_e (Int j) -> Constant_e (Bool (i<j))
        | _, _ -> failwith ("impossible"))
      else failwith ("type error")
    | LessThanEq -> if typecheck ("int",v1) && typecheck ("int",v2)
      then (match v1, v2 with
        | Constant_e (Int i), Constant_e (Int j) -> Constant_e (Bool (i<=j))
        | _, _ -> failwith ("impossible"))
      else failwith ("type error")
;;

(* Funzione di sostituzione *)

let substitute (v:exp) (x:variable) (e:exp) : exp = 
  let rec subst (e:exp) : exp = 
    match e with 
    | Var_e y -> if x = y then v else e
    | Constant_e _ -> e
    | Op_e (e1,op,e2) -> Op_e(subst e1,op,subst e2)
    | If_e (e1,e2,e3) -> If_e(subst e1,subst e2,subst e3)
    | FunCall_e (e1,e2) -> FunCall_e(subst e1,subst e2)
    | Fun_e (y,e1) -> if x = y then e else Fun_e (y, subst e1)
    | Let_e (y,e1,e2) -> 
        Let_e (y, subst e1, if x = y then e2 else subst e2)
    | Letrec_e (y,e1,e2) -> 
        if x = y then Letrec_e (y,e1,e2) else Letrec_e (y,subst e1,subst e2)
    | Etup (t) -> 
      let rec tuplesubst t =
        (match t with
        | Nil -> t
        | Seq (e, tp) -> Seq(subst(e),tuplesubst(tp)))
      in Etup (tuplesubst(t))
    | Pipe (t,e) -> 
      let rec tuplesubst (t) =
        (match t with
        | Nil -> t
        | Seq (ee, tp) -> Seq(subst(ee),tuplesubst(tp)))
      in Pipe (tuplesubst(t),subst(e))
    | ManyTimes (i, e1, e2) -> ManyTimes (i, subst(e1), subst(e2))
  in 
    subst e
;;

(* Ciclo dell'interprete *)

let eval_body (eval_loop:exp->exp) (e:exp) : exp = 
  match e with
    | Constant_e c -> Constant_e c 
    | Fun_e (x,e) -> Fun_e (x,e)
    | Op_e (e1,op,e2) -> 
        let v1 = eval_loop e1 in 
        let v2 = eval_loop e2 in 
          apply_op v1 op v2 
    | If_e (e1,e2,e3) -> 
          (match eval_loop e1 with 
             | Constant_e (Bool true) -> eval_loop e2
             | Constant_e (Bool false) -> eval_loop e3
             | v1 -> raise (BadIf v1))
    | Let_e (x,e1,e2) -> eval_loop (substitute (eval_loop e1) x e2)
    | FunCall_e (e1,e2) -> 
        (match eval_loop e1 with 
           | Fun_e (x,e) -> eval_loop (substitute (eval_loop e2) x e)
           | v1 -> raise (BadApplication v1))
    | Var_e x -> raise (UnboundVariable x)
    | Letrec_e (x,e1,e2) -> 
        let e1_unwind = substitute (Letrec_e (x,e1,Var_e x)) x e1 in 
          eval_loop (Let_e (x,e1_unwind,e2))
    | Etup (t) -> 
      let rec etp t =
        (match t with
        | Nil -> Nil
        | Seq (e,tp) -> Seq (eval_loop (e),etp (tp)))
      in Etup (etp (t))
    | Pipe (t,e) -> 
      let rec pip (t,e) =
       (match t with
       | Nil -> raise (BadApplication (Pipe (t,e)))
       | Seq (ee,tp) ->
          (match tp with
          | Nil -> eval_loop (FunCall_e (ee,e))
          | Seq (eee,tpp) -> pip (tp,eval_loop (FunCall_e(ee,e)))))
      in pip (t,e) 
    | ManyTimes (i,e1,e2) -> 
      let rec mtimes (i,e1,e2) =
        (match i with
          | 0 -> raise (BadApplication (ManyTimes(i,e1,e2)))
          | 1 -> eval_loop (FunCall_e (e1,e2))
          | _ -> let ii = i-1 in let e3 = eval_loop (FunCall_e(e1,e2)) in mtimes (ii,e1,e3))
      in mtimes (i,e1,e2)
;;

let rec eval e = eval_body eval e
;;


(* Test: il fattoriale *)

let fact_body = Fun_e ("n", 
                       If_e (Op_e (Var_e "n", LessThan, Constant_e (Int 1)),
                             Constant_e (Int 1),
                             Op_e (Var_e "n", Times, 
                             FunCall_e (Var_e "fact", 
                                        Op_e (Var_e "n", Minus, 
                                              Constant_e (Int 1))))));;

let fact_call = FunCall_e (Var_e "fact", (Constant_e (Int 4)));;

let fact4 = Letrec_e ("fact", fact_body, fact_call) ;;

eval fact4;;

(* Test: semplice funzione *)

let funa = Fun_e ("x",
                  Let_e("y",Op_e(Var_e "x",Times,Constant_e (Int 10)),Op_e(Var_e "y",Times,Var_e "y")));;

let funa_call = FunCall_e (funa,Constant_e (Int 5));;

eval funa_call;;

(* Test: pipe *)

let pipe = Pipe(Seq(funa,Seq(funa,Nil)),Constant_e (Int 5));;

eval pipe;;

(* Test: manytimes *)

let manytimes = ManyTimes(2,funa, Constant_e (Int 5));;

eval manytimes;;

(* Test: etup *)

let pluss = Op_e(Constant_e (Int (10)),Plus,Constant_e (Int (25)));;

let timess = Op_e(Constant_e (Int (10)),Times,Constant_e (Int (25)));;

let iff = If_e(Op_e(Constant_e (Int (10)),LessThanEq,Constant_e (Int (25))),pluss,timess);;

let etup = Etup(Seq(funa_call,Seq(pluss,Seq(iff,Seq(timess,Nil)))));;

eval etup;;