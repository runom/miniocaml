open Syntax;;

type ty = 
    | TInt 
    | TBool
    | TVar of string

type tyenv = (string * ty) list

let rec lookup x env =
    match env with
    |[] -> failwith("unbound variable:" ^ x)
    |(y,v)::tl -> if x=y then v else lookup x tl

let emptyenv () = [];;

let ext env x v = (x, v) :: env;;

let new_typevar s = TVar("'" ^ s)

let rec substitute' tvar t te =
    match te with
    | [] -> []
    | (x, t2) :: te2 ->
        let t3 = (if t2 = tvar then t else t2) in
        (x, t3) :: (substitute' tvar t te2)

let substitute tvar t te =
    List.map (fun (x, t2) -> 
        if t2 = tvar then (x, t) else (x, t2))
        te

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

