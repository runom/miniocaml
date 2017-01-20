open Syntax;;

type tyvar = string
type ty = 
    | TInt 
    | TBool
    | TArrow of ty * ty
    | TVar of tyvar

type tyenv = (string * ty) list
type tysubst = (tyvar * ty) list

let rec lookup x env =
    match env with
    |[] -> failwith("unbound variable:" ^ x)
    |(y,v)::tl -> if x=y then v else lookup x tl

let rec occurs tx t =
    if tx = t then true
    else 
        match t with
        | TArrow(t1, t2) -> (occurs tx t1) || (occurs tx t2)
        | _ -> false

(*
memo. Pervasives.or は非推奨
*)

let rec subst_ty theta t =
    let rec subst_ty' theta1 s =
        match theta1 with
        | [] -> TVar(s)
        | (tx, t1) :: theta2 ->
            if tx = s then t1
            else subst_ty' theta2 s
    in match t with
        | TInt -> TInt
        | TBool -> TBool
        | TArrow(t2, t3) -> TArrow(subst_ty theta t2, subst_ty theta t3)
        | TVar(s) -> subst_ty' theta s

let subst_tyenv theta te =
    List.map (fun (x, t) -> (x, subst_ty theta t)) te

let subst_eql theta eql =
    List.map (fun (t1, t2) -> (subst_ty theta t1, subst_ty theta t2)) eql

let rec compose_subst theta2 theta1 =
    let theta11 = 
        List.map (fun(tx, t) -> (tx, subst_ty theta2 t)) theta1
    in 
        List.fold_left (fun tau -> fun (tx, t) ->
                            try
                                let _ = lookup tx theta1 
                                    in tau 
                            with Failure(_) ->
                                (tx, t) :: tau
        ) theta11 theta2

let unify eql =
    let rec solve eql theta =
        match eql with
        | [] -> theta
        | (t1, t2) :: eql2 ->
            if t1 = t2 then solve eql2 theta
            else (
                match (t1, t2) with 
                | (TArrow(t11, t12), TArrow(t21, t22))
                    -> solve ((t11, t21) :: (t12, t22) :: eql2) theta
                | (TVar(s), _)
                    -> if (occurs t1 t2) 
                        then failwith "unification failed"
                        else solve (subst_eql [(s, t2)] eql2)
                                (compose_subst [(s, t2)] theta)
                | (_, TVar(s))
                    -> if (occurs t2 t1) 
                        then failwith "unification failed"
                        else solve (subst_eql [(s, t1)] eql2)
                                (compose_subst [(s, t1)] theta)
                | (_, _) -> failwith "unification failed"
                )
    in solve eql []

let emptyenv () = [];;

let ext env x v = (x, v) :: env;;

let new_typevar s = TVar("'" ^ s)

let substitute tvar t te =
    List.map (fun (x, t2) ->  if t2 = tvar then (x, t) else (x, t2)) te

let rec tinf te e =
    match e with
    | IntLit(_) -> (te, TInt)
    | BoolLit(_) -> (te, TBool)
    | Var(s) -> 
        (try
            let t1 = lookup s te in (te, t1)
        with Failure(_) -> 
            let tvar = new_typevar s in
            let te1 = ext te s tvar in
                (te1, tvar)
        )
    | Plus(e1, e2) ->
        let (te1, t1) = tinf te e1 in
        let te2 = 
            (match t1 with
            | TInt -> te1
            | TVar(_) -> substitute t1 TInt te1
            | _ -> failwith "type error in Plus"
            ) 
        in
        let (te3, t2) = tinf te2 e2 in
        let te4 = 
            (match t2 with
            | TInt -> te3
            | TVar(_) -> substitute t2 TInt te3
            | _ -> failwith "type error in Plus"
            )
        in (te4, TInt)
    | If(e1, e2, e3) ->
        let (te1, t1) = tinf te e1 in
        let te2 =
            (match t1 with
            | TBool -> te1
            | TVar(s) -> substitute t1 TBool te1
            | _ -> failwith "type error in If"
            )
        in
        let (te3, t2) = tinf te2 e2 in
        let (te4, t3) = tinf te3 e3 in
            (match (t2, t3) with 
            | (TInt, TInt) -> (te4, TInt)
            | (TBool, TBool) -> (te4, TBool)
            | (TInt, TVar(_)) ->
                let te5 = substitute t3 TInt te4 in (te5, TInt)
            | (TVar(_), TInt) ->
                let te5 = substitute t2 TInt te4 in (te5, TInt)  
            | (TBool, TVar(_)) ->
                let te5 = substitute t3 TBool te4 in (te5, TBool)
            | (TVar(_), TBool) ->
                let te5 = substitute t2 TBool te4 in (te5, TBool)
            | (TVar(_), TVar(_)) ->
                let te5 = substitute t2 t3 te4 in (te5, t3)
            | _ -> failwith "type error in If"
            )
    | _ -> failwith "unknown expression"

