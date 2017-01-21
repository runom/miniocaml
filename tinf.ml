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
let remove env x =
    List.remove_assoc x env

let theta0 = ([] : tysubst)

let new_typevar n = 
    let suf = if n / 26 = 0 then "" else string_of_int (n / 26) in
    let ch = char_of_int (int_of_char 'a' + n mod 26) in
        (TVar("'" ^ (String.make 1 ch) ^ suf), n + 1)

let rec tinf te e n =
    let arithmetic te e1 e2 n =
        let (te, t1, theta1, n) = tinf te e1 n in
        let (te, t2, theta2, n) = tinf te e2 n in
        let t1 = subst_ty theta2 t1 in
        let theta3 = unify [(t1, TInt); (t2, TInt)] in
        let te = subst_tyenv theta3 te in
        let theta = compose_subst theta3 (compose_subst theta2 theta1) in
            (te, TInt, theta, n) in
    let compare te e1 e2 n =
        let (te, t1, theta1, n) = tinf te e1 n in
        let (te, t2, theta2, n) = tinf te e2 n in
        let t1 = subst_ty theta2 t1 in
        let theta3 = unify [(t1, t2)] in  (* FIXME:  関数同士の比較を弾けない *)
        let te = subst_tyenv theta3 te in
        let theta = compose_subst theta3 (compose_subst theta2 theta1) in
            (te, TBool, theta, n) in
    let order te e1 e2 n =
        let (te, t1, theta1, n) = tinf te e1 n in
        let (te, t2, theta2, n) = tinf te e2 n in
        let t1 = subst_ty theta2 t1 in
        let theta3 = unify [(t1, TInt); (t2, TInt)] in
        let te = subst_tyenv theta3 te in
        let theta = compose_subst theta3 (compose_subst theta2 theta1) in
            (te, TBool, theta, n) in
    match e with
    | Var(s) ->
        (try
            let t1 = lookup s te in (te, t1, theta0, n)
        with Failure(_) ->
            let (tx, n) = new_typevar n in
            let te = ext te s tx in
                (te, tx, theta0, n)
        )
    | IntLit(_) -> (te, TInt, theta0, n)
    | BoolLit(_) -> (te, TBool, theta0, n)
    | If(e1, e2, e3) ->
        let (te, t1, theta1, n) = tinf te e1 n in
        let (te, t2, theta2, n) = tinf te e2 n in
        let t1 = subst_ty theta2 t1 in
        let (te, t3, theta3, n) = tinf te e3 n in
        let t1 = subst_ty theta3 t1 in
        let t2 = subst_ty theta3 t2 in
        let theta4 = unify [(t1, TBool); (t2, t3)] in
        let t3 = subst_ty theta4 t3 in
        let te = subst_tyenv theta4 te in
        let theta = compose_subst theta4 (compose_subst theta3 (compose_subst theta2 theta1)) in
            (te, t3, theta, n)
    | Let(x, e1, e2) ->
        let (te, t1, theta1, n) = tinf te e1 n in
        let te = ext te x t1 in
        let (te, t2, theta2, n) = tinf te e2 n in
        let te = remove te x in
        let theta = compose_subst theta2 theta1 in
            (te, t2, theta, n)
    | LetRec(f, x, e1, e2) ->
        let (tx, n) = new_typevar n in
        let te = ext te x tx in
        let (ty, n) = new_typevar n in
        let te = ext te f (TArrow(tx, ty)) in
        let (te, t1, theta1, n) = tinf te e1 n in
        let t2 = subst_ty theta1 tx in
        let te = remove te f in
        let te = remove te x in
        let te = ext te f (TArrow(t2, t1)) in
        let (te, t3, theta2, n) = tinf te e2 n in
        let te = remove te f in
        let theta = compose_subst theta2 theta1 in
            (te, t3, theta, n) 
    | Fun(x, e) ->
        let (tx, n) = new_typevar n in
        let te = ext te x tx in
        let (te, t1, theta, n) = tinf te e n in
        let t2 = subst_ty theta tx in
        let te = remove te x in
            (te, TArrow(t2, t1), theta, n)
    | App(e1, e2) ->
        let (te, t1, theta1, n) = tinf te e1 n in
        let (te, t2, theta2, n) = tinf te e2 n in
        let (tx, n) = new_typevar n in
        let t1 = subst_ty theta2 t1 in
        let theta3 = unify [(t1, TArrow(t2, tx))] in
        let t3 = subst_ty theta3 tx in
        let te = subst_tyenv theta3 te in
        let theta = compose_subst theta3 (compose_subst theta2 theta1) in
            (te, t3, theta, n)
    | Eq(e1, e2) -> compare te e1 e2 n
    | Neq(e1, e2) -> compare te e1 e2 n
    | Greater(e1, e2) -> order te e1 e2 n
    | Less(e1, e2) -> order te e1 e2 n
    | Plus(e1, e2) -> arithmetic te e1 e2 n
    | Minus(e1, e2) -> arithmetic te e1 e2 n
    | Times(e1, e2) -> arithmetic te e1 e2 n
    | Div(e1, e2) -> arithmetic te e1 e2 n    
    | _ -> failwith "unknown expression"


let tinf e = tinf (emptyenv ()) e 0