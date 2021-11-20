
(* reader.ml
 * A skeleton for the reader for the 2021-2022 course on compiler-construction
 *)

#use "pc.ml";;

let rec gcd a b =
  match (a, b) with
  | (0, b) -> b
  | (a, 0) -> a
  | (a, b) -> gcd b (a mod b);;

type scm_number =
  | ScmRational of (int * int)
  | ScmReal of float;;

type sexpr =
  | ScmVoid
  | ScmNil
  | ScmBoolean of bool
  | ScmChar of char
  | ScmString of string
  | ScmSymbol of string
  | ScmNumber of scm_number
  | ScmVector of (sexpr list)
  | ScmPair of (sexpr * sexpr);;

module type READER = sig
    val nt_sexpr : sexpr PC.parser
end;; (* end of READER signature *)

module Reader : READER = struct
open PC;;

let unitify nt = pack nt (fun _ -> ());;

let rec nt_whitespace str =
  const (fun ch -> ch <= ' ') str
and nt_end_of_line_or_file str =
  let nt1 = unitify (char '\n') in
  let nt2 = unitify nt_end_of_input in
  let nt1 = disj nt1 nt2 in
  nt1 str
and nt_line_comment str = 
  let nt1 = char ';' in
  let nt2 = diff nt_any nt_end_of_line_or_file in
  let nt2 = star nt2 in
  let nt1 = caten nt1 (caten nt2 nt_end_of_line_or_file) in
  let nt1 =  unitify nt1 in
  nt1 str
and nt_paired_comment str = 
  let nt1 = char '{' in
  let nt2 = disj_list[unitify nt_char; 
                      unitify nt_string; 
                      nt_comment] in
  let nt2' = disj nt2 (unitify (one_of "{}")) in
  let nt3 = diff nt_any nt2' in
  let nt3 = disj (unitify nt3) nt2 in
  let nt3 = star nt3 in
  let nt4 = char '}' in
  let nt1 = unitify (caten nt1 (caten nt3 nt4))in
  nt1 str
and nt_sexpr_comment str = 
  let comment = caten (word "#;") nt_sexpr in
  let comment = unitify comment in
  comment str
and nt_comment str =
  disj_list
    [nt_line_comment;
     nt_paired_comment;
     nt_sexpr_comment] str
and nt_skip_star str =
  let nt1 = disj (unitify nt_whitespace) nt_comment in
  let nt1 = unitify (star nt1) in
  nt1 str
and make_skipped_star (nt : 'a parser) =
  let nt1 = caten nt_skip_star (caten nt nt_skip_star) in
  let nt1 = pack nt1 (fun (_, (e, _)) -> e) in
  nt1
and nt_int str = 
  let sign = disj_list [word "-";word "+";nt_epsilon] in
  let number = caten sign nt_integer_part in
  let number = pack number (fun (sign,num) -> int_of_string(list_to_string(sign@num))) in
  number str
and nt_frac str = 
  let integer_part = pack nt_int (fun i -> string_to_list(string_of_int(i))) in
  let whitespace = star nt_whitespace in 
  let int_whitespace =caten integer_part whitespace in
  let divide = (char '/') in
  let divide  = caten int_whitespace divide in
  let divide = caten divide whitespace in
  let divide_number = caten divide nt_integer_part in
  let frac_number = pack divide_number (fun ((((i,_),_),_),n) ->
                                    let a = int_of_string(list_to_string(i)) in
                                    let b = int_of_string(list_to_string(n)) in
                                    ScmRational(a/(gcd a b),b/(gcd a b))) in
  frac_number str
and nt_integer_part str = 
  let r = range '0' '9' in
  let r = plus r in
  r str
and nt_mantissa str = 
  let r = range '0' '9' in
  let r = plus r in
  r str
and nt_exponent str = 
  let exp_token = disj_list [word "e";word "E";word "*10^";word "*10**"] in
  let int_num = nt_int in
  let exp = caten exp_token int_num in
  let exp = pack exp (fun (_,a)-> a) in
  exp str
and float_a str = 
  let int_part = nt_integer_part in
  let point = caten int_part (char '.') in
  let mantissa = pack (star nt_mantissa) (fun e -> match e with 
                                                    | [] -> []
                                                    | a::s -> a) in
  let mantissa = caten point mantissa in 
  let exponent = star nt_exponent in
  let f_a = caten mantissa exponent in
  let f_a = pack f_a (fun (((i,_),m),exp) -> match exp with
                                        | [] ->float_of_string(list_to_string(i@['.']@m))
                                        | e::s ->let a = float_of_string(list_to_string(i@['.']@m)) in
                                              let b =float_of_int(e) in
                                              a*.(10.**b)) in
  f_a str

and float_b str =
  let point = char '.' in
  let mantissa = caten point nt_mantissa in
  let exponent = star nt_exponent in
  let f_b = caten mantissa exponent in
  let f_b = pack f_b (fun ((_,i),exp) -> match exp with
                                        | [] ->float_of_string(list_to_string(['0';'.']@i))
                                        | e::s ->let a = float_of_string(list_to_string(['0';'.']@i)) in
                                              let b =float_of_int(e) in
                                              a*.(10.**b)) in
  f_b str

and float_c str = 
  let int_part = nt_int in
  let exponent = nt_exponent in
  let f_c = caten int_part exponent in
  let f_c = pack f_c (fun (i,exp) ->
                                  let a = float_of_int(i) in
                                  let b = float_of_int(exp) in
                                  a*.(10.**b)) in
  f_c str
and nt_float str = 
  let sign = disj_list [(word "-");(word "+");nt_epsilon] in
  let nt1 = pack float_a (fun f -> string_to_list(string_of_float(f))) in
  let nt2 = pack float_b (fun f -> string_to_list(string_of_float(f))) in
  let nt3 = pack float_c (fun f -> string_to_list(string_of_float(f))) in
  let nt1 = caten sign (disj_list [nt1;nt2;nt3]) in
  let nt1 = pack nt1 (fun (s,f) -> ScmReal(float_of_string(list_to_string(s@f)))) in
  nt1 str
and nt_number str =
  let nt1 = nt_float in
  let nt2 = nt_frac in
  let nt3 = pack nt_int (fun n -> ScmRational(n, 1)) in
  let nt1 = disj nt1 (disj nt2 nt3) in
  let nt1 = pack nt1 (fun r -> ScmNumber r) in
  let nt1 = not_followed_by nt1 nt_symbol_char in
  nt1 str
and nt_boolean str = 
  let nt_t = word_ci "#t" in
  let nt_t = pack nt_t (fun _ -> true) in
  let nt_f = word_ci "#f" in
  let nt_f = pack nt_f (fun _ -> false) in
  let nt = disj nt_t nt_f in
  let nt = pack nt (fun b -> ScmBoolean (b)) in
  nt str
and nt_char_simple str = 
  let ch_simp = const (fun ch -> ch > ' ')  in
  let ch_simp = not_followed_by ch_simp ch_simp in
  ch_simp str
and make_named_char char_name ch = 
  let ch_name = pack (word_ci char_name) (fun _ -> ch) in
  ch_name 
and nt_char_named str =
  let nt1 =
    disj_list [(make_named_char "newline" '\n');
               (make_named_char "page" '\012');
               (make_named_char "return" '\r');
               (make_named_char "space" ' ');
               (make_named_char "tab" '\t')] in
  nt1 str
and nt_char_hex str = 
  let num_range = range '0' '9' in
  let letter_range = range 'a' 'z' in
  let range = disj num_range letter_range in
  range str
and nt_hex_char str = 
  let prefix = word "x" in
  let r = plus (disj_list [range '0' '9';range 'a' 'f'])  in
  let r = caten prefix r in
  let r = pack r (fun (x,h) -> char_of_int(int_of_string(list_to_string(['0']@x@h)))) in
  r str
and nt_char str = 
  let prefix = word "#\\" in
  let prefix = caten prefix (disj_list [nt_char_named;nt_char_simple;nt_hex_char]) in
  let prefix = caten prefix nt_epsilon in
  let prefix = pack prefix (fun ((_,ch),_) -> ScmChar(ch)) in
  prefix str
and nt_symbol_char str =
  let r = disj_list [range '0' '9';range_ci 'a' 'z';char '!';
                    char '$';char '^';char '*';char '-';
                    char '_';char '=';char '+';char '<';
                    char '>';char '?';char '/';char ':'] in
  r str
and nt_symbol str =
  let nt1 = plus nt_symbol_char in
  let nt1 = pack nt1 list_to_string in
  let nt1 = pack nt1 (fun name -> ScmSymbol name) in
  let nt1 = diff nt1 nt_number in
  nt1 str
and string_literal_char str = 
  let out = disj_list [char '\\';char '~';char '\"'] in
  let c = pack (diff nt_any out) (fun a -> a) in
  c str
and string_meta_char str = 
  let meta = disj_list [pack (word "\\\"") (fun _-> '\"');
                        pack (word "\\t") (fun _-> '\t') ;
                        pack (word "\\\\") (fun _-> '\\');
                        pack (word "\\r") (fun _-> '\r');
                        pack (word "\\n") (fun _-> '\n');
                        pack (word "~~") (fun _-> '~');
                        pack (word "\\f") (fun _-> '\012')] in
  meta str
and string_hex_char str = 
  let prefix = caten (word "\\") (word "x") in
  let r = plus (disj_list [range '0' '9';range 'a' 'f'])  in
  let r = caten (caten prefix r) (char ';')  in
  let r = pack r (fun (((_,x),h),_) -> char_of_int(int_of_string(list_to_string(['0']@x@h)))) in
  r str
and string_interpolated str = 
  let prefix = pack (word "~{") (fun _-> ScmVoid) in
  let whitespace = pack nt_skip_star (fun _-> ScmVoid) in
  let postfix = pack (word "}") (fun _-> ScmVoid) in
  let state = caten (caten (caten (caten prefix whitespace) nt_sexpr) whitespace) postfix in
  let state = pack state (fun ((((_,_),sexpr),_),_) -> List.fold_right (fun hd tl -> ScmPair(hd,tl))
                                              [ScmSymbol ("format");ScmString("~a");sexpr] ScmNil) in
  state str
and string_char str =
  let state = disj_list [string_literal_char;string_meta_char;string_hex_char] in
  state str
and nt_string str =
  let qot = char '\"' in
  let normal_string = pack (plus string_char) (fun a -> list_to_string a)in (*(fun lst -> List.old_left (fun hd tl -> hd^tl) "" lst)*)
  let normal_string = pack normal_string (fun s -> ScmString(s)) in
  let dis = disj normal_string string_interpolated in
  let nt = star dis in
  let nt = caten (caten qot nt) qot in
  let nt = pack nt (fun ((_,exprs),_) -> match exprs with
                                          | [] -> ScmString("")
                                          | a::[]-> a
                                          | _ -> ScmPair(ScmSymbol("string-append"),List.fold_right (fun hd tl -> ScmPair(hd,tl))
                                                  exprs ScmNil)) in
  nt str
and nt_vector str =
  let nt1 = word "#(" in
  let nt2 = caten nt_skip_star (char ')') in
  let nt2 = pack nt2 (fun _ -> ScmVector []) in
  let nt3 = plus nt_sexpr in
  let nt4 = char ')' in
  let nt3 = caten nt3 nt4 in
  let nt3 = pack nt3 (fun (sexprs, _) -> ScmVector sexprs) in
  let nt2 = disj nt2 nt3 in
  let nt1 = caten nt1 nt2 in
  let nt1 = pack nt1 (fun (_, sexpr) -> sexpr) in
  nt1 str
and proper_list str = 
  let nt1 = word "(" in
  let nt2 = caten nt_skip_star (char ')') in
  let nt2 = pack nt2 (fun _ -> ScmNil) in
  let nt3 = plus nt_sexpr in
  let nt4 = char ')' in
  let nt3 = caten nt3 nt4 in
  let nt3 = pack nt3 (fun (sexprs, _) ->  List.fold_right (fun hd tl -> ScmPair(hd,tl))
                                                            sexprs ScmNil) in
  let nt2 = disj nt2 nt3 in
  let nt1 = caten nt1 nt2 in
  let nt1 = pack nt1 (fun (_, sexpr) -> sexpr) in
  nt1 str
and improper_list str =
  let nt1 = word "(" in
  let nt2 = plus nt_sexpr in
  let dot = char '.' in
  let nt4 = nt_sexpr in
  let nt5 = char ')' in
  let nt1 = caten (caten (caten (caten (caten (caten nt1 nt2) nt_skip_star) dot) nt_skip_star) nt4) nt5 in
  let nt1 = pack nt1 (fun ((((((_,sexprs),_),dot),_),sexpr), _) ->  List.fold_right (fun hd tl -> ScmPair(hd,tl))
                                                            sexprs sexpr) in
  nt1 str
and nt_list str = 
  let result = disj proper_list improper_list in
  result str
and qouted str = 
  let q = char '\'' in
  let nt = nt_sexpr in
  let nt = pack (caten q nt) (fun (_,sexpr) -> List.fold_right (fun hd tl -> ScmPair(hd,tl))
                                              ([ScmSymbol ("quote")]@[sexpr]) ScmNil) in
  nt str
and quasiquote str =
  let q = char '`' in
  let nt = nt_sexpr in
  let nt = pack (caten q nt) (fun (_,sexpr) -> List.fold_right (fun hd tl -> ScmPair(hd,tl))
                                              ([ScmSymbol ("quasiquote")]@[sexpr]) ScmNil) in
  nt str
and unquote str =
  let q = char ',' in
  let nt = nt_sexpr in
  let nt = pack (caten q nt) (fun (_,sexpr) -> List.fold_right (fun hd tl -> ScmPair(hd,tl))
                                              ([ScmSymbol ("unquote")]@[sexpr]) ScmNil) in
  nt str
and unquote_spliced str =
  let q = word ",@" in
  let nt = nt_sexpr in
  let nt = pack (caten q nt) (fun (_,sexpr) -> List.fold_right (fun hd tl -> ScmPair(hd,tl))
                                              ([ScmSymbol ("unquote-splicing")]@[sexpr]) ScmNil) in
  nt str
and nt_quoted_forms str = 
  let result = disj_list [qouted;quasiquote;unquote;unquote_spliced] in
  result str
and nt_sexpr str =
  let nt1 =
    disj_list [nt_number; nt_boolean; nt_char; nt_symbol;
               nt_string; nt_vector; nt_list; nt_quoted_forms] in
  let nt1 = make_skipped_star nt1 in
  nt1 str;;

end;; (* end of struct Reader *)

let rec string_of_sexpr = function
  | ScmVoid -> "#<void>"
  | ScmNil -> "()"
  | ScmBoolean(false) -> "#f"
  | ScmBoolean(true) -> "#t"
  | ScmChar('\n') -> "#\\newline"
  | ScmChar('\r') -> "#\\return"
  | ScmChar('\012') -> "#\\page"
  | ScmChar('\t') -> "#\\tab"
  | ScmChar(' ') -> "#\\space"
  | ScmChar(ch) ->
     if (ch < ' ')
     then let n = int_of_char ch in
          Printf.sprintf "#\\x%x" n
     else Printf.sprintf "#\\%c" ch
  | ScmString(str) ->
     Printf.sprintf "\"%s\""
       (String.concat ""
          (List.map
             (function
              | '\n' -> "\\n"
              | '\012' -> "\\f"
              | '\r' -> "\\r"
              | '\t' -> "\\t"
              | ch ->
                 if (ch < ' ')
                 then Printf.sprintf "\\x%x;" (int_of_char ch)
                 else Printf.sprintf "%c" ch)
             (string_to_list str)))
  | ScmSymbol(sym) -> sym
  | ScmNumber(ScmRational(0, _)) -> "0"
  | ScmNumber(ScmRational(num, 1)) -> Printf.sprintf "%d" num
  | ScmNumber(ScmRational(num, -1)) -> Printf.sprintf "%d" (- num)
  | ScmNumber(ScmRational(num, den)) -> Printf.sprintf "%d/%d" num den
  | ScmNumber(ScmReal(x)) -> Printf.sprintf "%f" x
  | ScmVector(sexprs) ->
     let strings = List.map string_of_sexpr sexprs in
     let inner_string = String.concat " " strings in
     Printf.sprintf "#(%s)" inner_string
  | ScmPair(ScmSymbol "quote",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf "'%s" (string_of_sexpr sexpr)
  | ScmPair(ScmSymbol "quasiquote",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf "`%s" (string_of_sexpr sexpr)
  | ScmPair(ScmSymbol "unquote",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf ",%s" (string_of_sexpr sexpr)
  | ScmPair(ScmSymbol "unquote-splicing",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf ",@%s" (string_of_sexpr sexpr)
  | ScmPair(car, cdr) ->
     string_of_sexpr' (string_of_sexpr car) cdr
and string_of_sexpr' car_string = function
  | ScmNil -> Printf.sprintf "(%s)" car_string
  | ScmPair(cadr, cddr) ->
     let new_car_string =
       Printf.sprintf "%s %s" car_string (string_of_sexpr cadr) in
     string_of_sexpr' new_car_string cddr
  | cdr ->
     let cdr_string = (string_of_sexpr cdr) in
     Printf.sprintf "(%s . %s)" car_string cdr_string;;