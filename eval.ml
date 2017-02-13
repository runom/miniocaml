open Syntax;;

let emptyenv () = [];;

let ext env x v = (x, v) :: env;;

let rec lookup x env =
    match env with
    |[] -> failwith("unbound variable:" ^ x)
    |(y,v)::tl -> if x=y then v else lookup x tl;;

let rec eval e env =
    let binop f e1 e2 env =
        let rhs = eval e2 env in let lhs = eval e1 env in
            match (lhs, rhs) with
            |(IntVal(n1), IntVal(n2)) -> IntVal(f n1 n2)
            | _ -> failwith "integer values expected"
    in
    let equal lhs rhs =
        let rec comp lhs rhs =
            match (lhs, rhs) with
            | (IntVal(n1), IntVal(n2)) -> BoolVal(n1 = n2)
            | (BoolVal(b1), BoolVal(b2)) -> BoolVal(b1 = b2)
            | (ListVal(l1), ListVal(l2)) -> 
                if List.length l1 <> List.length l2 then BoolVal(false)
                else 
                (match (l1, l2) with 
                        | ([], []) -> BoolVal(true)
                        | (v1 :: l1, v2 :: l2) -> 
                            (match (comp v1 v2) with 
                            | BoolVal(true) -> comp (ListVal(l1)) (ListVal(l2))
                            | BoolVal(false) -> BoolVal(false);
                            | _ -> failwith "internal error"
                            )
                        | _ -> failwith "internal error"
                )
            | _ -> failwith "wrong value"
        in comp lhs rhs
    in
    let greater lhs rhs =
        let rec comp lhs rhs =
            match (lhs, rhs) with
            | (IntVal(n1), IntVal(n2)) -> BoolVal(n1 > n2)
            | (BoolVal(b1), BoolVal(b2)) -> BoolVal(b1 > b2)
            | (ListVal(l1), ListVal(l2)) -> 
                (match (l1, l2) with 
                        | ([], []) -> BoolVal(false)
                        | (_, []) -> BoolVal(true)
                        | ([], _) -> BoolVal(false)
                        | (v1 :: l1, v2 :: l2) -> 
                            (match (equal v1 v2) with 
                            | BoolVal(true) -> comp (ListVal(l1))  (ListVal(l2))
                            | BoolVal(false) -> comp v1 v2
                            | _ -> failwith "internal error"
                            )
                )
            | _ -> failwith "wrong value"
        in comp lhs rhs
    in
    match e with
    | Var(x) -> lookup x env
    | IntLit(n) -> IntVal(n)
    | BoolLit(b) -> BoolVal(b)
    | If(e1, e2, e3) -> (match (eval e1 env) with
                            | BoolVal(true) -> eval e2 env
                            | BoolVal(false) -> eval e3 env
                            | _ -> failwith "wrong value")
    | Let(x, e1, e2) -> 
        let env1 = ext env x (eval e1 env) 
        in eval e2 env1
    | LetRec(f, x, e1, e2) ->
        let env1 = ext env f (RecFunVal(f, x, e1, env))
        in eval e2 env1
    | Fun(x, e1) -> FunVal(x, e1, env)
    | App(e1, e2) -> 
        (let arg = eval e2 env in let funpart = (eval e1 env) in
            match (funpart) with
            | FunVal(x, body, env1) -> 
                eval body (ext env1 x arg)
            | RecFunVal(f, x, body, env1) ->
                eval body (ext (ext env1 x arg) f funpart)
            | _ -> failwith "function value expected")
    | Eq(e1, e2) -> 
        let rhs = eval e2 env in let lhs = eval e1 env in
            equal lhs rhs
    | Neq(e1, e2) ->
        let rhs = eval e2 env in let lhs = eval e1 env in
            (match (equal lhs rhs) with
            | BoolVal(b) -> BoolVal(not b)
            | _ -> failwith "internal error"
            )
    | Greater(e1, e2) -> 
        let rhs = eval e2 env in let lhs = eval e1 env in
            greater lhs rhs
    | Less(e1, e2) -> 
        let rhs = eval e2 env in let lhs = eval e1 env in
            greater rhs lhs
    | Plus(e1, e2) -> binop (+) e1 e2 env
    | Minus(e1, e2) -> binop (-) e1 e2 env
    | Times(e1, e2) -> binop ( * ) e1 e2 env
    | Div(e1, e2) -> binop (/) e1 e2 env
    | Empty -> ListVal([]);
    | List(l1) -> 
        ListVal(List.map (fun e -> eval e env) l1)
    | Cons(e1, e2) ->
        begin
            match (eval e1 env, eval e2 env) with
            | (v1, ListVal(v2)) -> ListVal(v1 :: v2)
            | _ -> failwith "list value expected"
        end
    | Head(e1) ->
        begin 
            match (eval e1 env) with
            | ListVal(hd :: tl) -> hd
            | ListVal([]) -> failwith "list is empty"
            | _ -> failwith "list value expected"
        end
    | Tail(e1) ->
        begin
            match (eval e1 env) with
            | ListVal(hd :: tl) -> ListVal(tl)
            | ListVal([]) -> failwith "list is empty"
            | _ -> failwith "list value expected"
        end
    | _ -> failwith "unknown expression";;

let eval e = eval e (emptyenv ())
