#use "reader.ml";;


type expr =
  | ScmConst of sexpr
  | ScmVar of string
  | ScmIf of expr * expr * expr
  | ScmSeq of expr list
  | ScmSet of expr * expr
  | ScmDef of expr * expr
  | ScmOr of expr list
  | ScmLambdaSimple of string list * expr
  | ScmLambdaOpt of string list * string * expr
  | ScmApplic of expr * (expr list);;

exception X_syntax_error of sexpr * string;;
exception X_reserved_word of string;;
exception X_proper_list_error;;
exception X_not_implemented;;

let rec list_to_proper_list = function
| [] -> ScmNil
| hd::[] -> ScmPair (hd, ScmNil)
| hd::tl -> ScmPair (hd, list_to_proper_list tl);;

let rec list_to_improper_list = function
| [] -> raise X_proper_list_error
| hd::[] -> hd
| hd::tl -> ScmPair (hd, list_to_improper_list tl);;

let rec scm_append scm_list sexpr =
match scm_list with
| ScmNil -> sexpr
| ScmPair (car, cdr) -> ScmPair (car, scm_append cdr sexpr)
| _ -> raise (X_syntax_error (scm_list, "Append expects a proper list"))

let rec scm_map f sexpr =
match sexpr with
| ScmNil -> ScmNil
| ScmPair (car, cdr) -> ScmPair (f car, scm_map f cdr)
| _ -> raise (X_syntax_error (sexpr, "Map expects a list"));;

let rec scm_zip f sexpr1 sexpr2 =
match sexpr1, sexpr2 with
| ScmNil, ScmNil -> ScmNil
| ScmPair (car1, cdr1), ScmPair (car2, cdr2) -> ScmPair (f car1 car2, scm_zip f cdr1 cdr2)
| _, _ ->
    let sepxrs = list_to_proper_list [ScmSymbol "sexpr1:"; sexpr1; ScmSymbol "sexpr2:"; sexpr2] in
    raise (X_syntax_error (sepxrs, "Zip expects 2 lists of equal length"));;

let rec scm_list_to_list = function
| ScmPair (hd, tl) -> hd::(scm_list_to_list tl)
| ScmNil -> []
| sexpr -> raise (X_syntax_error (sexpr, "Expected proper list"));;

(* added by me *)
let rec scm_improper_list_to_list = function
| ScmPair(ScmSymbol(hd), ScmSymbol(tl)) -> hd::tl::[]
| ScmPair (ScmSymbol(hd), tl) -> hd::(scm_improper_list_to_list tl)
| sexpr -> raise (X_syntax_error (sexpr, "Expected improper list"));;
(* ***************** *)

let rec scm_is_list = function
| ScmPair (hd, tl) -> scm_is_list tl
| ScmNil -> true
| _ -> false

let rec scm_list_length = function
| ScmPair (hd, tl) -> 1 + (scm_list_length tl)
| ScmNil -> 0
| sexpr -> raise (X_syntax_error (sexpr, "Expected proper list"));;

let rec untag expr =
let untag_vars vars = List.map (fun s -> ScmSymbol s) vars in
let untag_tagged_list tag exprs = list_to_proper_list (ScmSymbol tag::(List.map untag exprs)) in

let untag_lambda_opt vars var body =
let vars = match vars with
| [] -> ScmSymbol var
| _ -> list_to_improper_list (untag_vars (vars@[var])) in
list_to_proper_list ([ScmSymbol "lambda"; vars]@body) in

match expr with
| (ScmConst (ScmSymbol(_) as sexpr)
    | ScmConst (ScmNil as sexpr)
    | ScmConst (ScmPair (_, _) as sexpr)) -> list_to_proper_list [ScmSymbol "quote"; sexpr]
| ScmConst s -> s
| ScmVar (name) -> ScmSymbol(name)
| ScmIf (test, dit, ScmConst (ScmVoid)) -> untag_tagged_list "if" [test; dit]
| ScmIf (test, dit, dif) -> untag_tagged_list "if" [test; dit; dif]
| ScmSeq(exprs) -> untag_tagged_list "begin" exprs
| ScmSet (var, value) -> untag_tagged_list "set!" [var; value]
| ScmDef (var, value) -> untag_tagged_list "define" [var; value]
| ScmOr (exprs) -> untag_tagged_list "or" exprs
| ScmLambdaSimple (vars, ScmSeq(body)) ->
    let vars = list_to_proper_list (untag_vars vars) in
    let body = List.map untag body in
    list_to_proper_list ([ScmSymbol "lambda"; vars]@body)
| ScmLambdaSimple (vars, body) ->
    let vars = list_to_proper_list (untag_vars vars) in
    list_to_proper_list ([ScmSymbol "lambda"; vars; untag body])
| ScmLambdaOpt (vars, var, ScmSeq(body)) ->
    let body = List.map untag body in
    untag_lambda_opt vars var body
| ScmLambdaOpt (vars, var, body) ->
    let body = [untag body] in
    untag_lambda_opt vars var body
| ScmApplic(procedure, args) -> list_to_proper_list (List.map untag (procedure::args));;


let rec string_of_expr expr =
string_of_sexpr (untag expr)

let scm_number_eq n1 n2 =
match n1, n2 with
| ScmRational(numerator1, denominator1), ScmRational(numerator2, denominator2) ->
        numerator1 = numerator2 && denominator1 = denominator2
| ScmReal(real1), ScmReal(real2) -> abs_float(real1 -. real2) < 0.001
| _, _ -> false

let rec sexpr_eq s1 s2 =
match s1, s2 with
| (ScmVoid, ScmVoid) | (ScmNil, ScmNil)  -> true
| ScmBoolean(bool1), ScmBoolean(bool2) -> bool1 = bool2
| ScmChar(char1), ScmChar(char2) -> char1 = char2
| ScmString(string1), ScmString(string2) -> String.equal string1 string2
| ScmSymbol(symbol1), ScmSymbol(symbol2) -> String.equal symbol1 symbol2
| ScmNumber(number1), ScmNumber(number2) -> scm_number_eq number1 number2
| ScmVector(sexprs1), ScmVector(sexprs2) -> List.for_all2 sexpr_eq sexprs1 sexprs2
| ScmPair(car1, cdr1), ScmPair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
| _, _ -> false

let rec expr_eq e1 e2 =
  match e1, e2 with
  | ScmConst (sexpr1), ScmConst (sexpr2) -> sexpr_eq sexpr1 sexpr2
  | ScmVar (var1), ScmVar (var2) -> String.equal var1 var2
  | ScmIf (test1, dit1, dif1), ScmIf (test2, dit2, dif2) -> (expr_eq test1 test2) &&
                                            (expr_eq dit1 dit2) &&
                                              (expr_eq dif1 dif2)
  | (ScmSeq(exprs1), ScmSeq(exprs2) | ScmOr (exprs1), ScmOr (exprs2)) ->
        List.for_all2 expr_eq exprs1 exprs2
  | (ScmSet (var1, val1), ScmSet (var2, val2) | ScmDef (var1, val1), ScmDef (var2, val2)) ->
        (expr_eq var1 var2) && (expr_eq val1 val2)
  | ScmLambdaSimple (vars1, body1), ScmLambdaSimple (vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
  | ScmLambdaOpt (vars1, var1, body1), ScmLambdaOpt (vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
  | ScmApplic (e1, args1), ScmApplic (e2, args2) ->
     (expr_eq e1 e2) && (List.for_all2 expr_eq args1 args2)
  | _ -> false;;

module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
end;; 

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;

let rec tag_parse_expression sexpr =
let sexpr = macro_expand sexpr in
(* let a = raise (X_syntax_error(sexpr,"tag_parse")) in *)
match sexpr with
| ScmNil-> ScmConst(ScmNil)
| ScmBoolean(_) ->ScmConst(sexpr)
| ScmChar(_) -> ScmConst(sexpr)
| ScmNumber(_) -> ScmConst(sexpr)
| ScmString(_) -> ScmConst(sexpr)
| ScmPair(ScmSymbol("quote"),ScmPair(sexprs,ScmNil)) -> ScmConst(sexprs)
| ScmSymbol(str)-> make_var str
| ScmPair(ScmSymbol("if") ,sexprs) -> make_if_exp sexprs
| ScmPair(ScmSymbol("or") ,sexprs) -> make_or_exp sexprs
| ScmPair(ScmSymbol("lambda") ,sexprs) -> make_lambda_exp sexprs
| ScmPair(ScmSymbol("define") ,sexprs) -> make_define_exp sexprs
| ScmPair(ScmSymbol("set!") ,sexprs) -> make_set_exp sexprs
| ScmPair(ScmSymbol("begin") ,sexprs) -> make_begin_exp sexprs
| ScmPair(hd,tl) -> ScmApplic((tag_parse_expression hd), List.map tag_parse_expression (scm_list_to_list tl))
(* Implement tag parsing here *)
| _ -> raise (X_syntax_error (sexpr, "Sexpr structure not recognized"))
                                              

and make_var str =
    if List.mem str reserved_word_list then raise (X_reserved_word(str))
    else ScmVar(str)

and make_if_exp sexprs =
    match sexprs with
    | ScmPair(test,ScmPair(dit,ScmPair(dif , ScmNil))) -> ScmIf(tag_parse_expression test,tag_parse_expression dit ,tag_parse_expression dif)
    | ScmPair(test,ScmPair(dit,ScmNil)) -> ScmIf(tag_parse_expression test,tag_parse_expression dit , ScmConst(ScmVoid))
    | _ -> raise (X_syntax_error(sexprs ,"Wrong if_expr !"))

and make_or_exp sexprs =
    if (scm_is_list sexprs)==false then raise (X_syntax_error(sexprs,"Wrong orExpr"))
    else
    let lst = scm_list_to_list sexprs in
    let or_exp_len = List.length lst  in
    match or_exp_len with
    | 0 -> ScmConst(ScmBoolean(false))
    | 1 -> tag_parse_expression (List.hd lst)
    | _ -> ScmOr(List.map tag_parse_expression lst)

and make_lambda_exp sexprs = 
    match sexprs with
    | ScmPair(ScmSymbol(str),sexpr)-> ScmLambdaOpt([],str,let lst = scm_list_to_list sexpr in
                                                                  match (List.length lst) with
                                                                  | 0 -> raise (X_syntax_error (sexpr,"not proper"))
                                                                  | 1 -> tag_parse_expression (List.hd lst)
                                                                  | _ -> ScmSeq(List.map tag_parse_expression lst))
    
    | ScmPair(args,sexpr)-> begin
                            match (scm_is_list args) with
                            | true -> ScmLambdaSimple((List.map (fun sym -> match sym with 
                                                                            | ScmSymbol(str) -> str
                                                                            |_ -> raise (X_syntax_error (sexpr,"wrong syntax"))) 
                                                                    (scm_list_to_list args)),
                                                                (match (List.length (scm_list_to_list sexpr)) with
                                                                | 0 -> raise (X_syntax_error (sexpr,"wrong syntax"))
                                                                | 1 -> tag_parse_expression (List.hd (scm_list_to_list sexpr))
                                                                | _ -> ScmSeq(List.map tag_parse_expression (scm_list_to_list sexpr))))
                                                                  
                            | false -> ScmLambdaOpt(
                            (let lst = scm_improper_list_to_list args in
                            match (List.rev lst) with
                                | var::argus -> List.rev argus
                                | _ -> raise (X_syntax_error (sexpr,"wrong syntax")))
                            ,(let lst = scm_improper_list_to_list args in
                            match (List.rev lst) with
                                | var::argus -> var
                                | _ -> raise (X_syntax_error (sexpr,"wrong syntax")))
                            ,(let lst = scm_list_to_list sexpr in
                            match (List.length lst) with
                                | 0 -> raise (X_syntax_error (sexpr,"wrong syntax"))
                                | 1 -> tag_parse_expression (List.hd (scm_list_to_list sexpr))
                                | _ -> ScmSeq(List.map tag_parse_expression (scm_list_to_list sexpr))))
                            end
    | _ -> raise (X_syntax_error (sexprs,"not proper"))

and make_define_exp sexprs =
    match sexprs with
    | ScmPair(ScmSymbol(var) , body) -> begin
                                            match (List.length (scm_list_to_list body)) with 
                                            | 0 -> raise (X_syntax_error(sexprs,"syntax error"))
                                            | 1 -> ScmDef((if (List.mem var reserved_word_list) then raise (X_syntax_error(sexprs,"Expected variable on LHS of define"))
                                            else ScmVar(var)),(tag_parse_expression (List.hd (scm_list_to_list body))))
                                            | _ -> ScmDef((if (List.mem var reserved_word_list) then raise (X_syntax_error(sexprs,"Expected variable on LHS of define"))
                                            else ScmVar(var)),(tag_parse_expression (ScmPair(ScmSymbol("lambda"),ScmPair(ScmNil,body)))))
                                            end
    | _ -> raise (X_syntax_error(sexprs,"syntax error"))


and make_set_exp sexprs =
    match (scm_is_list sexprs) with
    | true -> begin
                let lst = scm_list_to_list sexprs in
                match (List.hd lst) with
                | ScmSymbol(str) -> ScmSet(tag_parse_expression (List.hd lst),
                                match (List.length (List.tl lst)) with
                                | 1 -> tag_parse_expression (List.hd (List.tl lst))
                                | _ -> raise (X_syntax_error(sexprs,"wrong syntax")))
                | _ -> raise (X_syntax_error((List.hd lst),"Expected variable on LHS of set!"))
            end
    | false -> raise (X_syntax_error(sexprs,"wrong syntax"))

and make_begin_exp sexprs = 
    match (scm_is_list sexprs) with
    | true -> begin
                let lst = scm_list_to_list sexprs in
                ScmSeq(List.map tag_parse_expression lst)
                end
    | false -> raise (X_syntax_error(sexprs,"wrong syntax"))

and macro_expand sexpr =
match sexpr with
(* Handle macro expansion patterns here *)
| ScmPair(ScmSymbol("and"), rest) -> make_and rest
| ScmPair(ScmSymbol("let"), rest) -> make_let rest
| ScmPair(ScmSymbol("let*"), rest) -> make_let_star rest
| ScmPair(ScmSymbol("letrec"), rest) -> make_letrec rest
| ScmPair(ScmSymbol("cond"), rest) -> make_cond rest
| ScmPair(ScmSymbol("define"), rest) -> make_define_macro rest
| _ -> sexpr

and make_define_macro rest = 
    ScmPair(ScmSymbol("define"),(match rest with
    | ScmPair(ScmPair(ScmSymbol(var) , args) , body) -> (ScmPair(ScmSymbol(var),(ScmPair(ScmPair(ScmSymbol("lambda"),ScmPair(args,body)),ScmNil))))
    | _ -> rest))

and make_cond rest =
    let newCond = expand_cond rest in
    newCond

and expand_cond expression =
    match expression with
    | ScmPair(ScmPair(test,ScmPair(ScmSymbol("=>"),body)),rest) -> arrow_cond test body rest
    | ScmPair(ScmPair(test,dit),rest) -> cond_rib1 test dit rest
    | _ -> raise (X_syntax_error(expression, "expand_cond error 404 "))

and cond_rib1 test dit rest =
    match rest with
    | ScmNil -> begin
                match test with 
                | ScmSymbol("else") -> begin
                                        (match (List.length (scm_list_to_list (macro_expand dit))) with
                                        | 0 -> raise (X_syntax_error(dit,"wrong syntax"))
                                        | 1 ->  (macro_expand (List.hd (scm_list_to_list (dit))))
                                        | _ -> ScmPair(ScmSymbol("begin"), (macro_expand dit)))
                                        end
                | _ -> begin
                        ScmPair(ScmSymbol("if"),
                            ScmPair(test,ScmPair((match (List.length (scm_list_to_list (macro_expand dit))) with 
                                                    | 0 -> raise (X_syntax_error(rest,"wrong syntax"))
                                                    | 1 -> (macro_expand (List.hd (scm_list_to_list (dit))))
                                                    | _ -> ScmPair(ScmSymbol("begin"),(macro_expand dit)))
                                                    ,ScmNil)))
                        end
                end
    | _ -> begin
            match test with
            | ScmSymbol("else") -> begin
                                    (match (List.length (scm_list_to_list (macro_expand dit))) with
                                        | 0 -> raise (X_syntax_error(rest,"wrong syntax"))
                                        | 1 -> (macro_expand (List.hd (scm_list_to_list (dit))))
                                        | _ -> ScmPair(ScmSymbol("begin"), (macro_expand dit)))
                                    end
            | _ -> begin 
                    ScmPair(ScmSymbol("if"),
                        ScmPair(test,
                            ScmPair((match (List.length (scm_list_to_list (macro_expand dit))) with 
                                    | 0 -> raise (X_syntax_error(rest,"wrong syntax"))
                                    | 1 -> (List.hd (scm_list_to_list (macro_expand dit)))
                                    | _ -> ScmPair(ScmSymbol("begin"),(macro_expand dit)))
                                    ,(macro_expand (ScmPair(ScmPair(ScmSymbol("cond"),rest),ScmNil))))))
                    end
            end

and arrow_cond test body rest = 
    match rest with
    | ScmNil -> begin
                macro_expand (ScmPair(ScmSymbol("let"),
                (ScmPair(ScmPair(ScmPair(ScmSymbol("value"),ScmPair((macro_expand test),ScmNil)),
                            ScmPair(ScmPair(ScmSymbol("f"),ScmPair(ScmPair(ScmSymbol("lambda"),ScmPair(ScmNil,ScmPair(body,ScmNil))),ScmNil)),
                            ScmPair(ScmPair(ScmSymbol("rest"),ScmNil),ScmNil))),
                ScmPair(ScmPair(ScmSymbol("if"),
                        ScmPair(ScmSymbol("value"),
                        ScmPair(ScmPair(ScmPair(ScmSymbol("f"),ScmNil),ScmPair(ScmSymbol("value"),ScmNil)),
                        ScmPair(ScmPair(ScmSymbol("rest"),ScmNil),ScmNil)))),ScmNil)))))
                end
    | _ -> begin
                macro_expand (ScmPair(ScmSymbol("let"),
                (ScmPair(ScmPair(ScmPair(ScmSymbol("value"),ScmPair((macro_expand test),ScmNil)),
                            ScmPair(ScmPair(ScmSymbol("f"),ScmPair(ScmPair(ScmSymbol("lambda"),ScmPair(ScmNil,(macro_expand body))),ScmNil)),
                            ScmPair(ScmPair(ScmSymbol("rest"),ScmPair(ScmPair(ScmSymbol("lambda"),ScmPair(ScmNil,(macro_expand (ScmPair(ScmPair(ScmSymbol("cond"),rest),ScmNil))))),ScmNil)),ScmNil))),
                ScmPair(ScmPair(ScmSymbol("if"),
                        ScmPair(ScmSymbol("value"),
                        ScmPair(ScmPair(ScmPair(ScmSymbol("f"),ScmNil),ScmPair(ScmSymbol("value"),ScmNil)),
                        ScmPair(ScmPair(ScmSymbol("rest"),ScmNil),ScmNil)))),ScmNil)))))
            end

and make_and rest =
    match rest with
    | ScmNil -> ScmBoolean(true)
    | ScmPair(expr, ScmNil) -> (macro_expand expr)
    | ScmPair(expr, res) -> ScmPair(ScmSymbol("if"), ScmPair((macro_expand expr), ScmPair((macro_expand (ScmPair(ScmSymbol("and"), res))),
                                 ScmPair(ScmBoolean(false), ScmNil))))
    | _ -> raise (X_syntax_error(rest, "syntax error"))

and make_let rest =
    match rest with
    | ScmPair(args,body) -> begin 
                            let argus = (List.map (fun arg -> match arg with
                            | ScmPair(ScmSymbol(str),value) ->  ScmSymbol(str)
                            | _ -> raise (X_syntax_error(arg,"wrong syntax"))) (scm_list_to_list args)) in

                            let bodies = (match (List.length (scm_list_to_list body)) with
                            | 0 -> raise (X_syntax_error(rest,"wrong syntax"))
                            | _ -> (macro_expand body)) in

                            let values = (List.map (fun arg -> match arg with
                            | ScmPair(ScmSymbol(str),ScmPair(value,ScmNil)) ->  (macro_expand value)
                            | _ -> raise (X_syntax_error(arg,"wrong syntax"))) (scm_list_to_list args)) in

                            ScmPair(ScmPair(ScmSymbol("lambda"),ScmPair((list_to_proper_list argus),bodies))
                            ,(list_to_proper_list values))
                            end
    | _ -> raise (X_syntax_error(rest,"wrong syntax"))

and make_let_star rest = 
    match rest with
    | ScmPair(args, body) -> begin
                                match (List.length (scm_list_to_list args)) with
                                | 0 -> (macro_expand (ScmPair(ScmSymbol("let"),ScmPair(ScmNil,body))))
                                | 1 -> (macro_expand (ScmPair(ScmSymbol("let"),ScmPair(args,body))))
                                | _ -> begin
                                        let head_args = ScmPair((List.hd (scm_list_to_list args)),ScmNil) in
                                        let tail_args = (list_to_proper_list (List.tl (scm_list_to_list args))) in
                                        let bod = (macro_expand (ScmPair(ScmSymbol("let*"),ScmPair(tail_args,body)))) in
                                        (macro_expand (ScmPair(ScmSymbol("let"),ScmPair(head_args,ScmPair(bod,ScmNil)))))
                                        end
                                end
    | _ -> raise (X_syntax_error(rest,"wrong syntax"))

and make_letrec rest = 
    match rest with
    | ScmPair(args,body) -> begin
                            let vars = (List.map (fun arg -> match arg with
                            | ScmPair(ScmSymbol(str),value) ->  ScmSymbol(str)
                            | _ -> raise (X_syntax_error(arg,"wrong syntax"))) (scm_list_to_list args)) in

                            let vals = (List.map (fun arg -> match arg with
                            | ScmPair(ScmSymbol(str),value) -> value
                            | _ -> raise (X_syntax_error(arg,"wrong syntax"))) (scm_list_to_list args)) in

                            let bod = body in

                            let new_vars = (list_to_proper_list (List.map (fun var -> ScmPair(var,ScmPair(ScmPair(ScmSymbol("quote"),
                                                                              ScmPair(ScmSymbol("whatever"),ScmNil)),ScmNil))) vars)) in
                            
                            let vals = (scm_zip (fun var value -> ScmPair(ScmSymbol("set!"),ScmPair(var,(macro_expand value)))) 
                                                                    (list_to_proper_list vars) (list_to_proper_list vals)) in
                            
                            let bod = (scm_append vals bod) in

                            (* let a = raise (X_syntax_error(bod,"sa")) in *)

                            (macro_expand (ScmPair(ScmSymbol("let"),ScmPair(new_vars,bod))))
                            end
                            
    | _ -> raise (X_syntax_error(rest,"wrong syntax"))



end;;