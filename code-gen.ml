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




  let make_consts_tbl asts = 
    let lst_constants = List.map (fun x -> get_consts_lst x) asts in
    let lst_constants = [ScmVoid,Sexpr(ScmNil),Sexpr(ScmBoolean(false)),Sexpr(ScmBoolean(true))]@ (List.concat lst_constants) in
    let lst_constants = List.fold_left (fun a b -> if (List.mem b a) then a else a @ [b]) [] lst_constants in

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

  let rec get_address_in_triplets x lst= 
    match lst with
      |[] -> -1
      |(a,b,c)::tail-> if(a=x) then b else (get_address_in_triplets x tail);;
 
 
 
 
 let rec handle_triple_string str=
  match str with
    | []-> ""
    | first::[] ->string_of_int (int_of_char first)
    | first::last -> string_of_int(int_of_char first) ^"," ^ handle_triple_string last;; 
 
 
 
 
 let rec make_triplets index lst_acc set_of_consts= 
  match set_of_consts with
      |[] -> lst_acc
      |Void::lst' -> make_triplets (index + void_size) (lst_acc @ [(Void, index, "MAKE_VOID")]) lst'
      |Sexpr(Nil)::lst' -> make_triplets (index + nil_size) (lst_acc @ [(Sexpr(Nil), index, "MAKE_NIL")]) lst'
      |Sexpr(Bool false)::lst' -> make_triplets (index + boolean_size) (lst_acc @ [(Sexpr(Bool false), index, "MAKE_BOOL(0)")]) lst'
      |Sexpr(Bool true)::lst' -> make_triplets (index + boolean_size) (lst_acc @ [(Sexpr(Bool true), index, "MAKE_BOOL(1)")]) lst'
      |Sexpr(Char x)::lst' -> make_triplets (index + char_size) (lst_acc @ [(Sexpr(Char x), index, "MAKE_LITERAL_CHAR(" ^ (string_of_int (int_of_char x)) ^ ")")]) lst'
      |Sexpr(String x)::lst' -> make_triplets (index + (string_size (String.length x)))
                                  (lst_acc @ [(Sexpr(String x), index, "MAKE_LITERAL_STRING \""^x^"\"")]) lst'
      |Sexpr(Number(Fraction (n1, d1)))::lst' -> make_triplets (index + rational_size) 
                                                (lst_acc @ [(Sexpr(Number(Fraction (n1, d1))), index, "MAKE_LITERAL_RATIONAL(" ^ (string_of_int n1)^ "," ^ (string_of_int d1) ^")")]) lst'
      |Sexpr(Number(Float x))::lst' -> make_triplets (index + flonum_size) 
                                        (lst_acc @ [(Sexpr(Number(Float x)), index, "MAKE_LITERAL_FLOAT(" ^ (string_of_float x) ^")")]) lst'
      |Sexpr(Pair(x,y))::lst' -> make_triplets (index + pair_size)
                                (lst_acc @ [(Sexpr(Pair(x,y)), index, "MAKE_LITERAL_PAIR(const_tbl+"^(string_of_int (get_address_in_triplets (Sexpr(x)) lst_acc)) ^", const_tbl+"^(string_of_int(get_address_in_triplets (Sexpr(y)) lst_acc))^")")]) lst'
      |Sexpr(Symbol(x))::lst' -> make_triplets (index + symbol_size)
                                  (lst_acc @ [(Sexpr(Symbol(x))), index, 
                                  "MAKE_LITERAL_SYMBOL(const_tbl+"^ (string_of_int (get_address_in_triplets (Sexpr(String x)) lst_acc)) ^")"]) lst';;

  (*****************************************************Constants Table********************************************************)
  
  let make_fvars_tbl asts = raise X_not_yet_implemented;;
  
  (*****************************************************FreeVar Table********************************************************)
  
  let generate consts fvars e = raise X_not_yet_implemented;;

end;;

