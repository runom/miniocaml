(* main.ml *)

let parse str = 
  Parser.main Lexer.token 
    (Lexing.from_string str)

let interpret str =
    let e = parse str in
    let (_, ty, _, _) = Tinf.tinf e in
    let value = Eval.eval e in
      (value, ty)

let compile str = 
    let e = parse str in
    let _ = Tinf.tinf e in
        Compiler.compile e

let execute code =
    Compiler.execute code