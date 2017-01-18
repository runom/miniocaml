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
    match e with
    | Var(x) -> lookup x env
    | IntLit(n) -> IntVal(n)
    | Plus(e1, e2) -> binop (+) e1 e2 env
    | Times(e1, e2) -> binop ( * ) e1 e2 env
    | Minus(e1, e2) -> binop (-) e1 e2 env
    | Div(e1, e2) -> binop (/) e1 e2 env
    | Eq(e1, e2) -> 
        (let rhs = eval e2 env in let lhs = eval e1 env in
            match (lhs, rhs) with
            | (IntVal(n1), IntVal(n2)) -> BoolVal(n1 = n2)
            | (BoolVal(b1), BoolVal(b2)) -> BoolVal(b1 = b2)
            | (ListVal(l1), ListVal(l2)) -> BoolVal(l1 = l2)
            | _ -> failwith "wrong value")
    | Neq(e1, e2) ->
        (let rhs = eval e2 env in let lhs = eval e1 env in
            match (lhs, rhs) with
            | (IntVal(n1), IntVal(n2)) -> BoolVal(n1 <> n2)
            | (BoolVal(b1), BoolVal(b2)) -> BoolVal(b1 <> b2)
            | _ -> failwith "wrong value")
    | BoolLit(b) -> BoolVal(b)
    | If(e1, e2, e3) -> (match (eval e1 env) with
                            | BoolVal(true) -> eval e2 env
                            | BoolVal(false) -> eval e3 env
                            | _ -> failwith "wrong value")
    | Greater(e1, e2) -> 
        (let rhs = eval e2 env in let lhs = eval e1 env in
            match (lhs, rhs) with
            | (IntVal(n1), IntVal(n2)) -> BoolVal(n1 < n2)
            | _ -> failwith "integer values expected")
    | Let(x, e1, e2) -> 
        let env1 = ext env x (eval e1 env) 
        in eval e2 env1
    | Fun(x, e1) -> FunVal(x, e1, env)
    | LetRec(f, x, e1, e2) ->
        let env1 = ext env f (RecFunVal(f, x, e1, env))
        in eval e2 env1
    | App(e1, e2) -> 
        (let arg = eval e2 env in let funpart = (eval e1 env) in
            match (funpart) with
            | FunVal(x, body, env1) -> 
                eval body (ext env1 x arg)
            | RecFunVal(f, x, body, env1) ->
                eval body (ext (ext env1 x arg) f funpart)
            | _ -> failwith "function value expected")
    | Empty -> ListVal([]);
    | Cons(e1, e2) ->
        begin
            match (eval e1 env, eval e2 env) with
            | (v1, ListVal(v2)) -> ListVal(v1 :: v2)
            | _ -> failwith "list value expected"
        end
    | List(l1) -> 
        ListVal(List.map (fun e -> eval e env) l1)
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

