(* semantic-analyser.ml
 * The semantic analysis phase of the compiler
 *
 * Programmer: Mayer Goldberg, 2021
 *)

#use "tag-parser.ml";;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;

type var' = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | ScmConst' of sexpr
  | ScmVar' of var'
  | ScmBox' of var'
  | ScmBoxGet' of var'
  | ScmBoxSet' of var' * expr'
  | ScmIf' of expr' * expr' * expr'
  | ScmSeq' of expr' list
  | ScmSet' of var' * expr'
  | ScmDef' of var' * expr'
  | ScmOr' of expr' list
  | ScmLambdaSimple' of string list * expr'
  | ScmLambdaOpt' of string list * string * expr'
  | ScmApplic' of expr' * (expr' list)
  | ScmApplicTP' of expr' * (expr' list);;


let var_eq v1 v2 =
match v1, v2 with
  | VarFree (name1), VarFree (name2) -> String.equal name1 name2
  | VarBound (name1, major1, minor1), VarBound (name2, major2, minor2) ->
    major1 = major2 && minor1 = minor2 && (String.equal name1 name2)
  | VarParam (name1, index1), VarParam (name2, index2) ->
       index1 = index2 && (String.equal name1 name2)
  | _ -> false

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | ScmConst' (sexpr1), ScmConst' (sexpr2) -> sexpr_eq sexpr1 sexpr2
  | ScmVar' (var1), ScmVar' (var2) -> var_eq var1 var2
  | ScmIf' (test1, dit1, dif1), ScmIf' (test2, dit2, dif2) -> (expr'_eq test1 test2) &&
                                            (expr'_eq dit1 dit2) &&
                                              (expr'_eq dif1 dif2)
  | (ScmSeq' (exprs1), ScmSeq' (exprs2) | ScmOr' (exprs1), ScmOr' (exprs2)) ->
        List.for_all2 expr'_eq exprs1 exprs2
  | (ScmSet' (var1, val1), ScmSet' (var2, val2) | ScmDef' (var1, val1), ScmDef' (var2, val2)) ->
        (var_eq var1 var2) && (expr'_eq val1 val2)
  | ScmLambdaSimple' (vars1, body1), ScmLambdaSimple' (vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) && (expr'_eq body1 body2)
  | ScmLambdaOpt' (vars1, var1, body1), ScmLambdaOpt' (vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) && (expr'_eq body1 body2)
  | ScmApplic' (e1, args1), ScmApplic' (e2, args2) ->
     (expr'_eq e1 e2) && (List.for_all2 expr'_eq args1 args2)
  | ScmApplicTP' (e1, args1), ScmApplicTP' (e2, args2) ->
      (expr'_eq e1 e2) && (List.for_all2 expr'_eq args1 args2)
  | ScmBox' (v1), ScmBox' (v2) -> var_eq v1 v2
  | ScmBoxGet' (v1), ScmBoxGet' (v2) -> var_eq v1 v2
  | ScmBoxSet' (v1, e1), ScmBoxSet' (v2, e2) -> (var_eq v1 v2) && (expr'_eq e1 e2)
  | _ -> false;;


module type SEMANTIC_ANALYSIS = sig
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
  val run_semantics : expr -> expr'
end;; (* end of module type SEMANTIC_ANALYSIS *)

module Semantic_Analysis : SEMANTIC_ANALYSIS = struct

  let rec lookup_in_rib name = function
    | [] -> None
    | name' :: rib ->
       if name = name'
       then Some(0)
       else (match (lookup_in_rib name rib) with
             | None -> None
             | Some minor -> Some (minor + 1));;

  let rec lookup_in_env name = function
    | [] -> None
    | rib :: env ->
       (match (lookup_in_rib name rib) with
        | None ->
           (match (lookup_in_env name env) with
            | None -> None
            | Some(major, minor) -> Some(major + 1, minor))
        | Some minor -> Some(0, minor));;

  let tag_lexical_address_for_var name params env = 
    match (lookup_in_rib name params) with
    | None ->
       (match (lookup_in_env name env) with
        | None -> VarFree name
        | Some(major, minor) -> VarBound(name, major, minor))
    | Some minor -> VarParam(name, minor);;

  (* run this first! *)
  let annotate_lexical_addresses pe = 
   let rec run pe params env = begin
      match pe with
      | ScmConst(sexpr) -> ScmConst'(sexpr)
      | ScmVar(str) -> ScmVar'((tag_lexical_address_for_var str params env))
      | ScmIf(test,dit,dif) -> ScmIf'((run test params env),(run dit params env),(run dif params env))
      | ScmSeq(exprs) -> ScmSeq'(List.map (fun x -> (run x params env)) exprs)
      | ScmSet(ScmVar(var),expr) -> ScmSet'((tag_lexical_address_for_var var params env),(run expr params env))
      | ScmDef(ScmVar(var),value) -> ScmDef'(VarFree(var),(run value params env))
      | ScmOr(exprs) -> ScmOr'(List.map (fun x -> (run x params env)) exprs)
      | ScmLambdaSimple(args,body) -> ScmLambdaSimple'(args,(run body args (params::env)))
      | ScmLambdaOpt(args,variable,body) -> ScmLambdaOpt'(args,variable,(run body (args@[variable]) (params::env)))
      | ScmApplic(expr,exprs) -> ScmApplic'((run expr params env),(List.map (fun x -> run x params env) exprs))
      | _ -> raise X_this_should_not_happen
      end
   in 
   run pe [] [];;

  let rec rdc_rac s =
    match s with
    | [e] -> ([], e)
    | e :: s ->
       let (rdc, rac) = rdc_rac s
       in (e :: rdc, rac)
    | _ -> raise X_this_should_not_happen;;
  
  (* run this second! *)
  let annotate_tail_calls pe =
   let rec run pe in_tail =
      match pe with
      | ScmConst'(e) -> pe
      | ScmVar'(e) -> pe
      | ScmBox'(e) -> pe
      | ScmBoxGet'(e) -> pe
      | ScmBoxSet'(e1,e2) -> pe
      | ScmIf'(test,dit,dif) -> ScmIf'((run test false),(run dit in_tail),(run dif in_tail))
      | ScmSeq'(lst) -> begin
                        let first = (List.rev (List.tl (List.rev lst))) in
                        let last  = (List.hd (List.rev lst)) in
                        ScmSeq'((List.map (fun x -> (run x false)) first)@[(run last in_tail)] )
                        end
      | ScmSet'(var,value) -> ScmSet'(var, (run value false))
      | ScmDef'(var,value) -> ScmDef'(var, (run value in_tail))
      | ScmOr'(lst) -> begin
                        let first = (List.rev (List.tl (List.rev lst))) in
                        let last  = (List.hd (List.rev lst)) in
                        ScmOr'((List.map (fun x -> (run x false)) first)@[(run last in_tail)] )
                        end
      | ScmLambdaSimple'(args,body) -> ScmLambdaSimple'(args,(run body true))
      | ScmLambdaOpt'(args,variable,body) -> ScmLambdaOpt'(args,variable,(run body true))
      | ScmApplic'(expr,exprs) ->begin 
                                match in_tail with
                                | true -> ScmApplicTP'((run expr false),(List.map (fun x -> (run x false)) exprs))
                                | false -> ScmApplic'((run expr false),(List.map (fun x -> (run x false)) exprs))
                                end
      | _ -> raise X_this_should_not_happen
   in 
   run pe false;;

  (* boxing *)
(* ********************************************************************************************************************************************************** *)
(* reads *)
  let find_reads name enclosing_lambda expr =
    let rec find name enclosing_lambda expr = 
      match expr with
      | ScmConst'(sexpr) -> []
      | ScmVar'(arg) -> begin
                        match arg with
                        | VarParam(var,minor) -> if var = name then [enclosing_lambda] else []
                        | VarBound(var,major,minor) -> if var = name then [enclosing_lambda] else []
                        | _ -> []
                        end
      | ScmIf'(test,dit,dif) -> ((find name enclosing_lambda test)@(find name enclosing_lambda dit)@(find name enclosing_lambda dif))
      | ScmSeq'(lst) -> (List.fold_left (fun acc curr -> acc@(find name enclosing_lambda curr)) [] lst)
      | ScmSet'(var,value) -> (find name enclosing_lambda value)
      | ScmDef'(var,value) -> (find name enclosing_lambda value)
      | ScmOr'(lst) -> (List.fold_left (fun acc curr -> acc@(find name enclosing_lambda curr)) [] lst)
      | ScmLambdaSimple'(args,body) -> (find_reads_lambda name enclosing_lambda expr)
      | ScmLambdaOpt'(args,varaiable,body) -> (find_reads_lambda name enclosing_lambda expr)
      | ScmApplic'(expr,exprs) -> ((find name enclosing_lambda expr)@(List.fold_left (fun acc curr -> acc@(find name enclosing_lambda curr)) [] exprs))
      | ScmApplicTP'(expr,exprs) -> ((find name enclosing_lambda expr)@(List.fold_left (fun acc curr -> acc@(find name enclosing_lambda curr)) [] exprs))
      | _ -> []

    and find_reads_lambda name enclosing_lambda expr = 
      match expr with
      | ScmLambdaSimple'(args,body) -> if (List.mem name args) then [] 
        else (if (List.length (find name enclosing_lambda body)) > 0 then ([enclosing_lambda]@(find name expr body))
              else [])
      | ScmLambdaOpt'(args,variable,body) -> if (List.mem name (args@[variable])) then [] 
        else (if (List.length (find name enclosing_lambda body)) > 0 then ([enclosing_lambda]@(find name expr body))
              else []) 
      | _ ->[]
  
(* ********************************************************************************************************************************************************** *)
(* writes *)

  let find_writes name enclosing_lambda expr =
    let rec find name enclosing_lambda expr = 
      match expr with
      | ScmConst'(sexpr) -> []
      | ScmVar'(arg) -> []
      | ScmIf'(test,dit,dif) -> ((find name enclosing_lambda test)@(find name enclosing_lambda dit)@(find name enclosing_lambda dif))
      | ScmSeq'(lst) -> (List.fold_left (fun acc curr -> acc@(find name enclosing_lambda curr)) [] lst)
      | ScmSet'(arg,value) -> begin
                              match arg with
                              | VarParam(var,minor) -> if var = name then [enclosing_lambda] else []
                              | VarBound(var,major,minor) -> if var = name then [enclosing_lambda] else []
                              | _ -> []
                              end
      | ScmDef'(var,value) -> (find name enclosing_lambda value)
      | ScmOr'(lst) -> (List.fold_left (fun acc curr -> acc@(find name enclosing_lambda curr)) [] lst)
      | ScmLambdaSimple'(args,body) -> (find_writes_lambda name enclosing_lambda expr)
      | ScmLambdaOpt'(args,varaiable,body) -> (find_writes_lambda name enclosing_lambda expr)
      | ScmApplic'(expr,exprs) -> ((find name enclosing_lambda expr)@(List.fold_left (fun acc curr -> acc@(find name enclosing_lambda curr)) [] exprs))
      | ScmApplicTP'(expr,exprs) -> ((find name enclosing_lambda expr)@(List.fold_left (fun acc curr -> acc@(find name enclosing_lambda curr)) [] exprs))
      | _ -> []

    and find_writes_lambda name enclosing_lambda expr = 
      match expr with
      | ScmLambdaSimple'(args,body) -> if (List.mem name args) then [] 
        else (if (List.length (find name enclosing_lambda body)) > 0 then ([enclosing_lambda]@(find name expr body))
              else [])
      | ScmLambdaOpt'(args,variable,body) -> if (List.mem name (args@[variable])) then [] 
        else (if (List.length (find name enclosing_lambda body)) > 0 then ([enclosing_lambda]@(find name expr body))
              else []) 
      | _ ->[]  in
      find name enclosing_lambda expr


  let rec box_set expr = 
    match expr with
    | ScmConst'(sexpr) -> ScmConst'(sexpr)
    | ScmVar'(arg) -> ScmVar'(arg)
    | ScmIf'(test,dit,dif) -> ScmIf'((box_set test),(box_set dit),(box_set dif))
    | ScmSeq'(lst) -> ScmSeq'((List.map (fun x -> (box_set x)) lst))
    | ScmSet'(var,value) -> ScmSet'((box_set var),(box_set value))
    | ScmDef'(var,value) -> ScmDef'(((box_set var),(box_set value)))
    | ScmOr'(lst) -> ScmOr'((List.map (fun x -> (box_set x)) lst))
    | ScmLambdaSimple'(args,body) -> handle_lambda expr
    | ScmLambdaOpt'(args,varaiable,body) -> handle_lambda expr
    | ScmApplic'(expr,exprs) -> ScmApplic'((box_set expr),((List.map (fun x -> (box_set x)) exprs))) 
    | ScmApplicTP'(expr,exprs) -> ScmApplicTP'((box_set expr),((List.map (fun x -> (box_set x)) exprs)))
    | _ -> raise X_this_should_not_happen

    and handle_lambda expr =
      match expr with
      | ScmLambdaOpt(args,variable,body) -> begin
          (List.fold (fun acc cur -> if (check_boxing curr expr) then acc@[curr] else acc) [] (args@[variable])) in
          make_box_body args_to_box expr
                                            end
      | ScmLambdaSimple(args,body) -> begin
          let args_to_box = (List.fold (fun acc cur -> if (check_boxing curr expr) then acc@[curr] else acc) [] args) in
          make_box_body args_to_box expr
                                      end
      | _ -> raise X_this_should_not_happen
    
    and check_boxing name expr =
      let read = find_reads name expr expr in
      let write = find_writes name expr expr in
      if (List.length read) <> (List.length write) then true
      else (if (expr'_eq (List.hd (List.rev read)) (List.hd (List.rev write))) then false else true)

    and make_box_body args_box expr = raise X_not_yet_implemented

  let run_semantics expr =
    box_set
      (annotate_tail_calls
         (annotate_lexical_addresses expr))

end;; (* end of module Semantic_Analysis *)
