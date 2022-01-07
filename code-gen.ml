#use "semantic-analyser.ml";;

(* This module is here for you convenience only!
   You are not required to use it.
   you are allowed to change it. *)
module type CODE_GEN = sig
  (* This signature assumes the structure of the constants table is
     a list of key-value pairs:
     - The keys are constant values (Sexpr(x) or Void)
     - The values are pairs of:
       * the offset from the base const_table address in bytes; and
       * a string containing the byte representation (or a sequence of nasm macros)
         of the constant value
     For example: [(Sexpr(Nil), (1, "T_NIL"))]
   *)
  val make_consts_tbl : expr' list -> (sexpr * (int * string)) list

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)  
  val make_fvars_tbl : expr' list -> (string * int) list

  (* If you change the types of the constants and fvars tables, you will have to update
     this signature to match: The first argument is the constants table type, the second 
     argument is the fvars table type, and the third is an expr' that has been annotated 
     by the semantic analyser.
   *)
  val generate : (sexpr * (int * string)) list -> (string * int) list -> expr' -> string
end;;

module Code_Gen : CODE_GEN = struct



  (*****************************************************Constants Table********************************************************)
  let make_consts_tbl asts = 
    let lst_constants = List.map (fun x -> get_consts_lst x) asts in
    let lst_constants = [ScmVoid,Sexpr(ScmNil),Sexpr(ScmBoolean(false)),Sexpr(ScmBoolean(true))]@ (List.concat lst_constants) in
    let lst_constants = List.fold_left (fun a b -> if (List.mem b a) then a else a @ [b]) [] lst_constants in
    let final_table = make_constants_table 0 [] lst_constants in
    final_table;;

  (**************************)

  let rec get_constants expr' = 
    match expr' with
    | ScmConst' (x) -> [x]
    | ScmVar' (VarParam(v,minor))-> []
    | ScmVar' (VarBound(v,major, minor))-> []
    | ScmVar'(VarFree v1) -> []
    | ScmBoxGet'(var)-> []
    | ScmBoxSet'(var,value) -> (get_constants value)
    | ScmIf'(test,dit,dif) -> (get_constants test) @ (get_constants dit) @ (get_constants dif)
    | ScmSeq'(lst) -> let constants= List.map (fun(x)-> get_constants x) lst in 
                            List.concat constants
    | ScmSet'(var,value) -> (get_constants value)
    | ScmDef'(var,value) -> (get_constants value)
    | ScmOr'(lst) -> let constants= (List.map (fun(x)-> get_constants x) lst) in 
                            List.concat constants
    | ScmLambdaSimple'(args,body) -> (get_constants body) 
    | ScmLambdaOpt'(args,variable,body) -> (get_constants body) 
    | ScmApplic'(expr,args) -> let constants= (List.map (fun(x)-> get_constants x)) args in
                        (get_constants expr) @ List.concat (constants)
    | ScmApplicTP'(expr,args) -> let constants= (List.map (fun(x)-> get_constants x)) args in
                            (get_constants expr) @ List.concat (constants)
    | _ -> [];;

  let rec expand_constant lst = 
   match lst with
    | Sexpr(Symbol(str)):: tl -> (Sexpr(String(str)) :: [Sexpr(Symbol(str))]) @ (expand_constant tl)
    | Sexpr(Pair(x,y)) :: tl -> let expanded_car = expand_constant [Sexpr(x)] in
                          let expanded_cdr = expand_constant [Sexpr(y)] in 
                          (expanded_car @ expanded_cdr @
                          [Sexpr(x)] @ [Sexpr(y)] @ [Sexpr(Pair(x,y))]) @ (expand_constant tl) 
    | Sexpr(hd)::tl -> (hd) :: (expand_constant tl)
    | hd::tl -> hd :: (expand_constant tl)
    | _ ->[];;

  let get_consts_lst x = 
    let consts_lst = get_constants x in 
    let uniq_consts = List.fold_left (fun a b -> if (List.mem b a) then a else a@[b]) [] consts_lst in
    let expanded_lst = expand_constant uniq_consts in
    let uniq_expand_lst = List.fold_left (fun a b -> if (List.mem b a) then a else a@[b]) [] expanded_lst in
    uniq_expand_lst;;

(**************************)

  let rec make_constants_table index lst consts_lst= 
    match consts_lst with
      |[] -> lst
      |Void::tl -> make_constants_table (index + void_size) (lst @ [(Void,(index,"MAKE_VOID"))]) tl
      |Sexpr(Nil)::tl -> make_constants_table (index + nil_size) (lst @ [(Sexpr(Nil),(index,"MAKE_NIL"))]) tl
      |Sexpr(Bool(false))::tl -> make_constants_table (index + boolean_size) (lst @ [(Sexpr(Bool(false)),(index,"MAKE_BOOL(0)"))]) tl
      |Sexpr(Bool(true))::tl -> make_constants_table (index + boolean_size) (lst @ [(Sexpr(Bool(true)),(index,"MAKE_BOOL(1)"))]) tl
      |Sexpr(Char(str))::tl -> make_constants_table (index + char_size) (lst @ [(Sexpr(Char(str)),(index,"MAKE_LITERAL_CHAR(" ^ (string_of_int (int_of_char str)) ^ ")"))]) tl
      |Sexpr(String(str))::tl -> make_constants_table (index + (string_size (String.length str))) (lst @ [(Sexpr(String(str)),(index,"MAKE_LITERAL_STRING \""^str^"\""))]) tl
      |Sexpr(Number(Fraction (num1, num2)))::tl -> make_constants_table (index + rational_size) (lst @ [(Sexpr(Number(Fraction (num1, num2))),(index, "MAKE_LITERAL_RATIONAL(" ^ (string_of_int num1)^ "," ^ (string_of_int num2) ^")"))]) tl
      |Sexpr(Number(Float(num)))::tl -> make_constants_table (index + flonum_size) (lst @ [(Sexpr(Number(Float(num))),(index,"MAKE_LITERAL_FLOAT(" ^ (string_of_float num) ^")"))]) tl
      |Sexpr(Pair(x,y))::tl -> make_constants_table (index + pair_size) (lst @ [(Sexpr(Pair(x,y)),(index,"MAKE_LITERAL_PAIR(const_tbl+"^(string_of_int (constant_address (Sexpr(x)) lst)) ^", const_tbl+"^(string_of_int(constant_address (Sexpr(y)) lst))^")"))]) tl
      |Sexpr(Symbol(str))::tl -> make_constants_table (index + symbol_size) (lst @ [(Sexpr(Symbol(str))),(index,"MAKE_LITERAL_SYMBOL(const_tbl+"^ (string_of_int (constant_address (Sexpr(String(str))) lst)) ^")")]) tl;; 

  let rec constant_address x lst= 
    match lst with
      |[] -> -1
      |(a,(b,c))::tail-> if(a=x) then b else (constant_address x tail);;

  (*****************************************************FreeVar Table********************************************************)
  
  let make_fvars_tbl asts = raise X_not_yet_implemented;;
  
  (*****************************************************Code Generating********************************************************)  
  
  let generate consts fvars e = raise X_not_yet_implemented;;

end;;

