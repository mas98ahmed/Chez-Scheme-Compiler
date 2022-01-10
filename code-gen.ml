#use "semantic-analyser.ml";;

(* This module is here for you convenience only!
   You are not required to use it.
   you are allowed to change it. *)
exception X_this_should_not_happen;;

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
      | ScmSymbol(str):: tl -> (ScmString(str) :: [ScmSymbol(str)]) @ (expand_constant tl)
      | ScmPair(x,y) :: tl -> let expanded_car = expand_constant [x] in
                            let expanded_cdr = expand_constant [y] in 
                            (expanded_car @ expanded_cdr @
                            [x] @ [y] @ [ScmPair(x,y)]) @ (expand_constant tl)
      (* | ScmVector(lst)::tl -> (List.map (fun x -> expand_constant x) lst)@lst@(expand_constant tl) *)
      | hd::tl -> hd :: (expand_constant tl)
      | _ ->[];;
    
  let get_consts_lst x = 
    let consts_lst = get_constants x in 
    let uniq_consts = List.fold_left (fun a b -> if (List.mem b a) then a else a@[b]) [] consts_lst in
    let expanded_lst = expand_constant uniq_consts in
    let uniq_expand_lst = List.fold_left (fun a b -> if (List.mem b a) then a else a@[b]) [] expanded_lst in
    uniq_expand_lst;;


  let rec constant_address x lst= 
    match lst with
      |[] -> -1
      |(a,(b,c))::tail-> if(a=x) then b else (constant_address x tail);;

  let rec make_constants_table index lst consts_lst= 
    match consts_lst with
      | [] -> lst
      | ScmVoid::tl -> make_constants_table (index + 1) (lst @ [(ScmVoid,(index,"MAKE_VOID"))]) tl
      | ScmNil::tl -> make_constants_table (index + 1) (lst @ [(ScmNil,(index,"MAKE_NIL"))]) tl
      | ScmBoolean(false)::tl -> make_constants_table (index + 2) (lst @ [(ScmBoolean(false),(index,"MAKE_BOOL(0)"))]) tl
      | ScmBoolean(true)::tl -> make_constants_table (index + 2) (lst @ [(ScmBoolean(true),(index,"MAKE_BOOL(1)"))]) tl
      | ScmChar(str)::tl -> make_constants_table (index + 2) (lst @ [(ScmChar(str),(index,"MAKE_LITERAL_CHAR(" ^ (string_of_int (int_of_char str)) ^ ")"))]) tl
      | ScmString(str)::tl -> make_constants_table (index + 9 + (String.length str)) (lst @ [(ScmString(str),(index,"MAKE_LITERAL_STRING \""^str^"\""))]) tl
      | ScmNumber(ScmRational(num1, num2))::tl -> make_constants_table (index + 17) (lst @ [(ScmNumber(ScmRational (num1, num2)),(index, "MAKE_LITERAL_RATIONAL(" ^ (string_of_int num1)^ "," ^ (string_of_int num2) ^")"))]) tl
      | ScmNumber(ScmReal(num))::tl -> make_constants_table (index + 9) (lst @ [(ScmNumber(ScmReal(num)),(index,"MAKE_LITERAL_FLOAT(" ^ (string_of_float num) ^")"))]) tl
      (* | ScmVector(lst)::tl -> make_constants_table (index + 9 + ((List.length lst)*8)) (lst @ [(ScmSymbol(str)),(index,"MAKE_LITERAL_VECTOR(const_tbl+"^ (string_of_int (constant_address (ScmString(str)) lst)) ^")")]) tl *)
      | ScmPair(x,y)::tl -> make_constants_table (index + 17) (lst @ [(ScmPair(x,y),(index,"MAKE_LITERAL_PAIR(const_tbl+"^(string_of_int (constant_address x lst)) ^", const_tbl+"^(string_of_int(constant_address y lst))^")"))]) tl
      | ScmSymbol(str)::tl -> make_constants_table (index + 9) (lst @ [(ScmSymbol(str)),(index,"MAKE_LITERAL_SYMBOL(const_tbl+"^ (string_of_int (constant_address (ScmString(str)) lst)) ^")")]) tl;;

  (**************************)

  let make_consts_tbl asts = 
    let lst_constants = List.map (fun x -> get_consts_lst x) asts in
    let lst_constants = [ScmVoid;ScmNil;ScmBoolean(false);ScmBoolean(true)]@ (List.concat lst_constants) in
    let lst_constants = List.fold_left (fun a b -> if (List.mem b a) then a else a @ [b]) [] lst_constants in
    let final_table = make_constants_table 0 [] lst_constants in
    final_table;;


  (*****************************************************FreeVar Table********************************************************)

  let rec get_free_vars _expr' =
    match _expr' with
    | ScmConst' (_) -> []
    | ScmVar'(VarParam(var,minor))-> []
    | ScmVar'(VarBound(var,major,minor))-> []
    | ScmVar'(VarFree(var)) -> [var]
    | ScmBoxGet'(_)-> []
    | ScmBoxSet'(var,value) -> (get_free_vars value)
    | ScmIf'(test,dit,dif) -> (get_free_vars test)@(get_free_vars dit)@(get_free_vars dif)
    | ScmSeq'(lst) -> let free_vars = List.map (fun (x)->get_free_vars x) lst in
                    List.concat free_vars
    | ScmSet'(var,value) ->begin 
                        match var with
                        | VarFree(name) -> [name]@(get_free_vars value) 
                        | _ -> (get_free_vars value) 
                        end
    | ScmDef'(var,value) -> begin 
                        match var with
                        | VarFree(name) -> [name]@(get_free_vars value) 
                        | _ -> (get_free_vars value) 
                          end
    | ScmOr'(lst) -> let free_vars = List.map (fun (x)->get_free_vars x) lst in
                            List.concat free_vars 
    | ScmLambdaSimple'(args,body) -> (get_free_vars body) 
    | ScmLambdaOpt'(args,variable,body) -> (get_free_vars body) 
    | ScmApplic'(expr,args) -> (get_free_vars expr) @ List.concat (List.map (fun (x)->get_free_vars x) args)
    | ScmApplicTP'(expr,args) -> (get_free_vars expr) @ List.concat (List.map (fun (x)->get_free_vars x) args)
    | _ -> [] ;;
 
 
  let primitive_names_to_labels =[
  (* Type queries *)
  "boolean?" ; "flonum?"; "rational?" ;
  "pair?"; "null?"; "char?"; "string?";
  "procedure?"; "symbol?";
  (* String procedures *)
  "string-length"; "string-ref"; "string-set!";
  "make-string"; "symbol->string";
  (* Type conversions *)
  "char->integer"; "integer->char"; "exact->inexact";
  (* Identity test *)
  "eq?";
  (* Arithmetic ops *)
  "+"; "*"; "/"; "="; "<";
  (* Additional rational numebr ops *)
  "numerator"; "denominator"; "gcd";
  (* you can add yours here *)
  "car"; "cdr";"set-car!";"set-cdr!"; "cons";"apply" ] ;;

  let rec add_index_Free_var lst_free_vars index = 
    match lst_free_vars with
    |[]-> []
    |hd::tl-> (hd,index):: add_index_Free_var tl (index+1) ;;

  let make_fvars_tbl asts = 
    let free_vars_lst = List.concat (List.map (fun(x) -> get_free_vars x) asts) in
    let free_vars_lst = List.fold_left (fun a b -> if (List.mem b a) then a else a@[b]) [] free_vars_lst in
    let free_vars_lst = primitive_names_to_labels @ free_vars_lst in
    let free_vars_table = add_index_Free_var free_vars_lst 0 in
    free_vars_table;;
  
  (*****************************************************Code Generating********************************************************)  
  let label_counter= (ref 0);;
  let applictp_counter= (ref 0);;
 
  let increase_unique_label_tp counter=
      counter := !counter + 1; counter;;

  let unique_label_tp label=
        label ^ (string_of_int(!(increase_unique_label_tp applictp_counter)));;

  let increase_unique_label counter=
      counter := !counter + 1; counter;;
  
  let unique_label label=
      label ^ (string_of_int(!(increase_unique_label label_counter)));;
 
 
 
 
 
   
  let const_address x consts_tbl=
    let (a,(b,c)) = (List.find (fun (a,(b,c))-> (expr_eq (ScmConst(a)) (ScmConst(x)))) consts_tbl)  in 
      "const_tbl+" ^ (string_of_int b);;
    
  
  
  
  
  let rec fvar_address x fvars_tbl= 
        match fvars_tbl with
        |[] -> -1
        |(a,b)::tail-> if(String.equal a x) then b else (fvar_address x tail) 
        ;;
  
  
  let override_frame_Applictp applic_tp_label =
  
    let asm_code= "mov r8, [rbp+3*8] ;r8= old number of args" ^ "\n" ^
                  "add r8, 3 ; ( add 3 to it (num of args,env,ret addres))" ^ "\n" ^
                  "shl r8, 3 ; ( (make it (n+3) *8 so now if we add it to rbp we get the start of previous frame and we start override" ^ "\n"^
                  "add r8, rbp ; r8 = ARG(n-1), that mean r9 points to the top of stack in where we should overide" ^ "\n"^
                  "mov r9, [rsp+2*8] ; r9 is the counter of the loop so we make it equal to new arg number+3" ^ "\n"^ 
                  "add r9, 3 ; adding 3 (num of args, env,ret addres)" ^ "\n"^
                  "mov r10, [rbp] ;r10= old rbp, we save old rbp before overiding loop" ^ "\n"^
                  applic_tp_label^": ;( in this loop we overrite the stack from down to top) the loop continue while rcx!=0" ^ "\n"^
                  " mov r11, [rsp+8*(r9-1)] ; r11 = the first value of the new frame" ^ "\n"^
                  " mov [r8], r11 ; put it in [r9] ( overiding) " ^ "\n"^
                  " sub r8, 8 ; r9=r9-8 (8 is the size of every cell in stack )" ^ "\n"^
                  " dec r9 ; r9=r9-1 " ^ "\n"^
                  " cmp r9, 0 ; " ^ "\n"^
                  " jne " ^applic_tp_label ^ "\n" ^ 

                  "mov rbp, r10 ;Make rbp points to old rbp (exists in r10)" ^ "\n"^
                  "add r8,8 ;" ^ "\n"^ 
                  "mov rsp, r8 ; " ^ "\n"^
                  "CLOSURE_CODE rdi,rax ; " ^ "\n"^
                  "jmp rdi"^"\n" in
  asm_code;; 
    
  
  
  let get_major_0_array_code register_ = 
    let loop_start_label= unique_label  "loop_start" in
    let loop_finish_label= unique_label  "loop_finish" in
    let asm_code="xor r12, r12" ^ "\n"^
    "mov r12, qword [rbp + 8 * 3] ; r12=number of args"^"\n"^ 
    "mov rbx, r12 ; rbx= number of args"^ "\n"^
    "mov r10, r12" ^ "\n"^
    "shl r10, 3" ^ "\n"^
    "push rbx" ^ "\n" ^
    "MALLOC "^register_^", r10 ; allocate memory" ^ "\n" ^ 
    "pop rbx" ^ "\n" ^
    "cmp r12, 0" ^ "\n"^ 
    "je "^loop_finish_label^"\n"^ 
    loop_start_label^":"^"\n"^
    " mov r12, qword [rbp+(3+rbx)*WORD_SIZE] ; getting arg number rbx-1" ^"\n"^ 
    " mov ["^ register_ ^ " + 8 * (rbx-1)], r12 ; putting the arg in the array" ^ "\n"^
    " dec rbx " ^ "\n" ^
    " cmp rbx, 0" ^ "\n"^ 
    " jne "^loop_start_label^"\n"^
    loop_finish_label^":"^"\n" in
    asm_code;;
  
  let get_extend_env_code register_ env_major =
    let loop_start_label= unique_label  "extend_loop_start" in
    let loop_finish_label= unique_label  "extend_loop_finish" in
    let asm_code= "MALLOC " ^ register_ ^ ", "^(string_of_int ((env_major + 1)*8))^" ; allocate \n"^
    "mov rbx, " ^ (string_of_int env_major) ^ " ; here rbx=prevEnvSize" ^ "\n"^ 
    "mov r9, rbx"^"\n"^
    "cmp r9,0" ^ "\n"^
    "je "^loop_finish_label^ "\n" ^
    "mov r12, qword [rbp + 8 * 2]" ^" ; here r12 ponits to tha majors array (prevEnv)" ^ "\n" ^ 
    loop_start_label^":"^"\n"^
    " mov r9, qword[r12 + 8 * (rbx - 1)]"^"\n"^ 
    " mov qword[" ^ register_ ^ " + 8 * rbx],r9" ^ "\n" ^
    " dec rbx " ^ "\n"^
    " cmp rbx, 0" ^ "\n"^
    " jne "^loop_start_label^"\n"^
    loop_finish_label^":"^"\n" in
    asm_code;;
  
  
  
  let get_shift_eq_loop_code=
    let loop_start_label= unique_label  "shift_loop_start" in
    let asm_code= loop_start_label ^": " ^ "\n" ^
    " mov r10, [rsp + rdx*8]" ^ "\n" ^
    " mov qword[rsp + (rdx-1)*8], r10 " ^ "\n" ^
    " inc rdx" ^ "\n" ^
    " dec r8" ^ "\n" ^
    " cmp r8, 0" ^ "\n"^
    " jne "^loop_start_label^ "\n" in
    asm_code;; 
  
  
  
  let get_opt_args_lst_code args_len= 
    let loop_start_label= unique_label  "optArgs_loop_start" in
    let asm_code=" xor r15,r15" ^ "\n" ^
    " xor r8, r8" ^ "\n" ^
    " sub r8, "^ args_len ^ "\n" ^
    " add r8, [rsp+2*8] ; now r8= the size of opr params " ^ "\n" ^
    " mov r9, SOB_NIL_ADDRESS" ^ "\n"^
    loop_start_label^":" ^ "\n" ^
    " mov r10, [rsp + 8*(r8 + " ^ args_len ^") + 2*8]" ^ "\n" ^
    " MAKE_PAIR (r15, r10, r9)" ^"\n"^ (* her we make the list, element by element*)
    " mov r9, r15" ^ "\n"^
    " dec r8 " ^ "\n" ^ 
    " cmp r8, 0" ^ "\n"^
    " jne "^loop_start_label^ "\n" in
    asm_code;; 
  
  
  let get_shift_noteq_loop_code args_len_inc=
    let loop_start_label= unique_label  "shifArgs_loop_start" in
    let finish_shift_label= unique_label  "finish_shift" in
    let asm_code= " xor r8, r8" ^ "\n" ^
    " sub r8, " ^ args_len_inc ^ "\n" ^
    " add r8, [rsp+2*8]" ^ "\n" ^
    " mov r10, r8" ^ "\n" ^
    " cmp r8,0 " ^ "\n"^ (* if number of optparams=1 no need to shif *)
    " je " ^ finish_shift_label ^ "\n" ^
    (* here r10 have number of opt args and we need to shift*) 
    " xor r8, r8" ^ "\n" ^
    " sub r8, r10"^ "\n" ^
    " add r8, [rsp+2*8]" ^ "\n" ^
    " add r8, 3" ^ "\n" ^ (* here r8 = number of args+3-number of opt args, and this is the loop times number *)
    " mov r12, [rsp+2*8]" ^ "\n" ^ (*here r12 have number of args *) 
    loop_start_label ^ ":" ^ "\n" ^
    " mov r14, [rsp + (r8-3)*8 + 8*2]" ^ "\n"^
    " mov qword[rsp + r12*8 + 8*2 ], r14" ^ "\n"^ 
    " dec r12" ^ "\n" ^
    " dec r8" ^ "\n" ^
    " cmp r8, 0" ^ "\n"^
    " jne "^loop_start_label ^ "\n" ^
    " shl r10, 3" ^ "\n" ^
    " add rsp, r10" ^ "\n" ^ (* fixing rsp to be rsp+ numOfOptArgs*8 and in fact this is the number of cells that we shifted *)
    finish_shift_label ^ ":" ^ "\n" in
    asm_code;;
  
 
 let rec generate_code env consts_tbl fvars_tbl expr' =
    match expr' with 
    | ScmConst'(x) -> "mov rax,"^ (const_address x consts_tbl ) ^ "\n" 
    | ScmVar'(VarParam(var,minor))-> "mov rax, qword [rbp + 8*(4 + " ^ (string_of_int(minor))^ ")]" ^ "\n"
    | ScmVar'(VarBound(var,major,minor))-> "mov rax, qword [rbp + 8*2]" ^ "\n" ^
                                          "mov rax, qword [rax + 8*" ^ (string_of_int(major)) ^ "]" ^ "\n" ^ 
                                          "mov rax, qword [rax + 8*" ^ (string_of_int(minor)) ^ "]" ^ "\n"
    | ScmVar'(VarFree(var)) -> "mov rax, qword [fvar_tbl+"^ string_of_int(fvar_address var fvars_tbl)^"* WORD_SIZE ]" ^ "\n"
    | ScmBox'(var) -> (generate_code env consts_tbl fvars_tbl (ScmVar'(var))) ^
                      "MALLOC r8, 8 \n"^
                      "mov [r8], rax \n"^
                      "mov rax,r8 \n"
    | ScmBoxGet'(var)-> (generate_code env consts_tbl fvars_tbl (ScmVar'(var))) ^ "\n" 
                        ^ "mov rax, qword [rax]"^ "\n"
    | ScmBoxSet'(var,value) ->(generate_code env consts_tbl fvars_tbl value) ^ "\n" ^ 
                              "push rax" ^ "\n" ^ 
                              (generate_code env consts_tbl fvars_tbl (ScmVar'(var))) ^ "\n" ^ 
                              "pop qword [rax]" ^ "\n" ^
                              "mov rax, SOB_VOID_ADDRESS" ^ "\n"
    | ScmIf'(test,dit,dif) -> let lelse= (unique_label  "lelse") in
                              let lexit= (unique_label  "lexit") in
                              (generate_code env consts_tbl fvars_tbl test)^"\n"^
                              "cmp rax, SOB_FALSE_ADDRESS"^"\n"^
                              "je "^lelse^"\n"^
                              (generate_code env consts_tbl fvars_tbl dit) ^ "\n"^
                              "jmp " ^ lexit ^ "\n"^
                              lelse ^ ":\n" ^
                              (generate_code env consts_tbl fvars_tbl dif) ^ "\n"^
                              lexit ^ ":" ^ "\n"
    | ScmSeq'(lst) -> (String.concat "\n" (List.map (fun (x)-> (generate_code env consts_tbl fvars_tbl x)) lst)) 
    | ScmSet'(var,value) -> begin 
                            match var with
                            |(VarParam(var1, minor))-> (generate_code env consts_tbl fvars_tbl value ) ^ "\n" ^
                            "mov qword [rbp + 8* (4 + "^ (string_of_int minor) ^ ")], rax" ^ "\n"^
                            "mov rax, SOB_VOID_ADDRESS" ^ "\n"
                            |(VarBound(var1,major,minor))-> (generate_code env consts_tbl fvars_tbl value )^"\n"^ 
                            "mov rbx, qword [rbp + 8 * 2]"^"\n"^
                            "mov rbx, qword [rbx + 8 * "^(string_of_int major)^"]"^"\n"^
                            "mov qword [rbx + 8 * "^(string_of_int minor)^"], rax"^"\n"^
                            "mov rax, SOB_VOID_ADDRESS" ^ "\n"
                            |(VarFree(var1)) -> (generate_code env consts_tbl fvars_tbl value )^"\n"^ 
                            "mov qword [fvar_tbl + WORD_SIZE*"^ string_of_int(fvar_address var1 fvars_tbl )^"], rax"^"\n"^
                            "mov rax, SOB_VOID_ADDRESS" ^ "\n"
                            end
    | ScmDef'(var,value) -> begin 
                            match var with 
                            |VarFree(var1) ->(generate_code env consts_tbl fvars_tbl value) ^ "\n" ^ 
                            "mov qword [fvar_tbl + WORD_SIZE*" ^ string_of_int(fvar_address var1 fvars_tbl )^"], rax"^"\n"^
                            "mov rax, SOB_VOID_ADDRESS"
                            | _ -> "" 
                            end
    | ScmOr'(lst) ->  let or_lexit = (unique_label  "lexit") in
                      (String.concat ("\n" ^ "cmp rax, SOB_FALSE_ADDRESS" ^ "\n" ^ "jne " ^ or_lexit^"\n") (List.map (fun (x)-> (generate_code env consts_tbl fvars_tbl x)) lst)) ^
                      "\n" ^ or_lexit ^ ":\n" 
    | ScmApplic'(expr,args) -> (String.concat "" (List.map (fun (x)-> (generate_code env consts_tbl fvars_tbl x)^ "\npush rax\n" ) (List.rev args))) ^ "\n" ^
                          "push "^(string_of_int (List.length args)) ^ "\n" ^
                          (generate_code env consts_tbl fvars_tbl expr) ^ "\n" ^
                          "CLOSURE_ENV rbx,rax \n" ^ 
                          "push rbx\n" ^ 
                          "CLOSURE_CODE rax,rax \n" ^ 
                          "call rax \n" ^ 
                          "add rsp, 8*1 \n" ^
                          "pop rbx \n" ^
                          "shl rbx, 3 \n" ^
                          "add rsp, rbx \n"    
    | ScmApplicTP'(expr,args)-> (String.concat "" (List.map (fun (x)-> (generate_code env consts_tbl fvars_tbl x)^ "\npush rax\n" ) (List.rev args))) ^ "\n" ^
                          "push "^(string_of_int (List.length args)) ^ "\n" ^
                          (generate_code env consts_tbl fvars_tbl expr) ^ "\n" ^ 
                          "CLOSURE_ENV rbx,rax \n" ^
                          "push rbx " ^"\n" ^ 
                          "push qword [rbp + 8 * 1] "^"\n"^
                          (override_frame_Applictp (unique_label_tp  "overrideFrame")) ^ "\n" ^                        
                          "mov rbp, r10 ;Make rbp points to old rbp (exists in r10)" ^ "\n"^
                          "add r8,8 ;" ^ "\n"^ 
                          "mov rsp, r8 ; " ^ "\n"^
                          "CLOSURE_CODE rdi,rax ; " ^ "\n"^
                          "jmp rdi"^"\n"^
                          "CLOSURE_CODE rbx,rax ; rbx now points to the proc clousre code, its in rax since the last generate call was with proc" ^ "\n"^
                          "jmp rbx ; make the application, jumping to the code" ^"\n"   
    | ScmLambdaSimple'(vars,body) ->  let lcode_label= unique_label  "Lcode" in
                                      let lcont_label= unique_label  "Lcont" in
                                      (get_extend_env_code "r13" env) ^ "\n" ^ (* after extinding env, major 0 is empty*)
                                      (get_major_0_array_code "r11" ) ^ "\n" ^
                                      "mov qword [r13],r11 ; putting the array in the first major,"^ "\n" ^
                                      "MAKE_CLOSURE(rax, r13, " ^ lcode_label ^ " ) " ^ "\n" ^
                                      "jmp " ^ lcont_label ^ "\n" ^
                                      lcode_label^":" ^"\n" ^
                                      " push rbp"^"\n"^
                                      " mov rbp, rsp"^"\n "^ 
                                      (generate_code (env+1) consts_tbl fvars_tbl body) ^"\n"^
                                      " leave" ^ "\n" ^
                                      " ret" ^ "\n" ^ 
                                      lcont_label^":"^"\n" 
    | ScmLambdaOpt'(args, opt, body) -> let loopsh_start_label= unique_label  "shift_loop_start" in
                                        let pre_lcont_label= unique_label "pre_lcont_label" in
                                        let lcode_label= unique_label  "LcodeOpt" in
                                        let lcont_label= unique_label  "LcontOpt" in
                                        let argsnum_greater_than_argslen_label= unique_label  "argsnum_greater_than_argslen" in
                                        let args_len= string_of_int (List.length args) in
                                        let args_len_inc= string_of_int ((List.length args)+1) in
                                        (get_extend_env_code "r13" env)^ "\n" ^ (* after extinding env, major 0 is empty*)
                                        (get_major_0_array_code "r11" ) ^ "\n" ^
                                        "mov qword [r13],r11 ; putting the array in the first major,"^ "\n" ^
                                        "MAKE_CLOSURE(rax, r13, "^lcode_label^" ) " ^ "\n" ^
                                        "jmp " ^ lcont_label ^ "\n" ^
                                        lcode_label ^": " ^ "\n" ^
                                        "xor rcx, rcx" ^ "\n" ^
                                        "add rcx, [rsp + 8*2]" ^ "\n" ^
                                        "cmp rcx, "^args_len ^"; here rcx= num of args" ^ "\n" ^
                                        "jne " ^ argsnum_greater_than_argslen_label ^ "\n" ^
                                        "xor r8, r8" ^ "\n" ^
                                        "add r8, 3" ^ "\n" ^
                                        "add r8, " ^ args_len ^ "\n" ^
                                        "xor rdx, rdx " ^ "\n" ^
                                        loopsh_start_label ^": " ^ "\n" ^
                                        " mov r10, [rsp + rdx*8]" ^ "\n" ^
                                        " mov qword[rsp + (rdx-1)*8], r10 " ^ "\n" ^
                                        " inc rdx" ^ "\n" ^
                                        " dec r8" ^ "\n" ^
                                        " cmp r8, 0" ^ "\n"^
                                        " jne "^loopsh_start_label^ "\n"  ^ "\n" ^
                                        "sub rsp, 8 ; fixing rsp" ^ "\n"^ 
                                        "mov qword[rsp+2*8], " ^ args_len_inc ^ " ; adding 1 to argnum in the stack" ^ "\n" ^
                                        "mov qword[rsp + 2*8 + 8*" ^args_len_inc ^ "], SOB_NIL_ADDRESS" ^ "\n" ^
                                        "jmp " ^ pre_lcont_label ^ "\n" ^
                                        argsnum_greater_than_argslen_label ^": " ^ "\n" ^ 
                                        " "^(get_opt_args_lst_code args_len) ^ "\n" ^ (*we save the list pointer in r15 *)
                                        " "^(get_shift_noteq_loop_code args_len_inc) ^ "\n" ^
                                        " "^ "mov qword[rsp+ 2*8], " ^ args_len_inc ^ "\n" ^
                                        " "^ "mov qword[rsp+ 2*8 + 8*" ^ args_len_inc ^ "], r15 ; here we put the list af opt args as the last arg" ^ "\n" ^
                                        pre_lcont_label ^ ":" ^ "\n" ^
                                        "   "^ "push rbp"^"\n"^
                                        "   "^ "mov rbp, rsp"^"\n "^ 
                                        "   "^ (generate_code (env+1) consts_tbl fvars_tbl body) ^ "\n"^
                                        "   "^"leave" ^ "\n" ^
                                        "   "^"ret" ^ "\n" ^
                                        lcont_label ^ ": " ^ "\n" ;;

  let generate consts fvars e = generate_code 0 consts fvars e;;
end;;

