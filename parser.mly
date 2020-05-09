%{

module S = Syntax
module T = Type

module IdMap = Map.Make(S.Id)
;;

module IdSet = Set.Make(S.Id)
;;

type handler_clause =
  | Return of S.Id.t * S.expr
  | Operation of S.op_clause

(* let cur_tyvar_index = ref 0 *)
(* ;; *)

let tyvar_env = ref IdMap.empty
;;

(* let gen_fresh_tyvar () = *)
(*   cur_tyvar_index := !cur_tyvar_index + 1; *)
(*   !cur_tyvar_index *)
(* ;; *)

let init () =
  tyvar_env := IdMap.empty
;;

let lookup_bound_tyvar m tyvar =
  match IdMap.find_opt tyvar m with
  | Some x -> x
  | None ->
     let msg =
       Printf.sprintf
         "Type variable \"%s\" is not bound in the type signature of the effect operation"
         tyvar
     in
     raise @@ S.Error msg
;;

(* let lookup_or_assign_tyvar tyvar = *)
(*   match StrMap.find_opt tyvar !tyvar_env with *)
(*   | None -> let x = gen_fresh_tyvar () in *)
(*             tyvar_env := StrMap.add tyvar x !tyvar_env; *)
(*             x *)
(*   | Some x -> x *)
(* ;; *)

let make_tyvar_env tyvars =
  let rec iter m cur_id ids = function
    | [] -> (List.rev ids, m)
    | x::xs ->
       if IdMap.mem x m then
         let msg = "Type variable \"" ^ x ^ "\" is quantified twice" in
         raise @@ S.Error msg
       else
         let ids' = cur_id :: ids in
         iter (IdMap.add x cur_id m) (cur_id+1) ids' xs
  in
  iter IdMap.empty 0 [] tyvars
;;

let make_ty_sig tyvars (dom_ty, codom_ty) =
  let (ids, m) = make_tyvar_env tyvars in
  let dom_ty = dom_ty @@ lookup_bound_tyvar m in
  let codom_ty = codom_ty @@ lookup_bound_tyvar m in
  (T.TyvarSet.of_list ids, dom_ty, codom_ty)
;;

let fun_with_params params e =
  List.fold_right (fun x f -> S.EFun (x, f)) params e
;;

let check_pattern_vars vars =
  ignore @@
    List.fold_left
      (fun s x ->
        if IdSet.mem x s then
          let msg =
            Printf.sprintf
              "The same variable \"%s\" appears twice or more times in a pttern"
              x
          in
          raise @@ S.Error msg
        else
          IdSet.add x s)
      IdSet.empty vars
;;

%}

%token <string> ID
%token FUN
%token RIGHT_ARROW DOUBLE_RIGHT_ARROW
%token LET IN REC
%token EQUAL
%token DOUBLE_SEMICOLON
%token LEFT_PAREN
%token RIGHT_PAREN
%token COMMA
%token MATCH EFFECT HANDLE WITH RETURN
%token INT STRING BOOL FLOAT
%token SINGLE_QUOTE COLON DOT
%token VERTICAL_BAR
%token LEFT_BRACE RIGHT_BRACE
%token PLUS MINUS ASTERISK SLASH PERCENT CARET DOUBLE_VERTICAL_BAR DOUBLE_AMPERSAND
%token LESS LESS_EQUAL GREAT GREAT_EQUAL LESS_GREAT
%token SEMICOLON
%token INL INR
%token LEFT_SQ_BRACKET RIGHT_SQ_BRACKET DOUBLE_COLON
%token EOF

%token <int> LITERAL_INT
%token <float> LITERAL_FLOAT
%token TRUE
%token FALSE
%token <string> LITERAL_STRING

%nonassoc below_SEMICOLON
%right SEMICOLON
%nonassoc above_SEMICOLON
%right DOUBLE_COLON
%right DOUBLE_VERTICAL_BAR
%right DOUBLE_AMPERSAND
%left EQUAL LESS LESS_EQUAL GREAT GREAT_EQUAL LESS_GREAT
%right CARET
%left PLUS MINUS
%left ASTERISK SLASH PERCENT


%start <Syntax.decl option> main

%%

main:
  | x = top_level { init (); x () }

top_level:
  | d = decl; DOUBLE_SEMICOLON { fun () -> Some d }
  | EOF { fun () -> None }

decl:
  | e = expr { DExpr e }
  | LET; x = ID; params = param_list; EQUAL; e = expr
    { DLet (x, fun_with_params params e) }
  | LET; REC; x = ID; y = ID; params = param_list; EQUAL; e = expr
    { S.DLet (x, S.ELetRec (x, y, fun_with_params params e, S.EId x)) }
  | EFFECT; op_name = ID; COLON; t = ty_signature { S.DEff (op_name, t) }

expr:
  | e1 = expr; SEMICOLON; e2 = expr { S.EApp (S.EApp (S.EId ";", e1), e2) }
  | LET; x = ID; params = param_list; EQUAL; e1 = expr; IN; e2 = expr_below_semi
    { S.ELet (x, fun_with_params params e1, e2) }
  | LET; REC; x = ID; y = ID; params = param_list; EQUAL; e1 = expr; IN; e2 = expr_below_semi
    { S.ELetRec (x, y, fun_with_params params e1, e2) }
  | FUN; params = nonempty_param_list; RIGHT_ARROW; e = expr_below_semi
    { fun_with_params params e }
  | HANDLE; e = expr; WITH; h = handler_expr { S.EHandle (e, h) }
  | LEFT_PAREN; f = expr; COMMA; s = expr; RIGHT_PAREN { S.EPair (f, s) }
  | INL; e = binary_op_expr { S.EInl e }
  | INR; e = binary_op_expr { S.EInr e }
  | MATCH; e = expr; WITH; m = match_clause { EMatch (e, m) }
  | e = binary_op_expr { e }

expr_below_semi:
  | e = expr { e } %prec below_SEMICOLON

list_expr:
  | { [] }
  | e = expr { [e] }
  | e = list_elem_expr; SEMICOLON; es = list_expr { e::es }

list_elem_expr:
  | e = expr { e } %prec above_SEMICOLON

binary_op_expr:
  | e1 = binary_op_expr; op = binary_op; e2 = binary_op_expr
    { EApp (EApp (EId op, e1), e2) }
  | e = app_expr { e }

app_expr:
  | e1 = app_expr; e2 = simple_expr { S.EApp (e1, e2) }
  | e = simple_expr { e }

simple_expr:
  | x = ID { S.EId x }
  | c = const_expr { S.EConst c }
  | LEFT_SQ_BRACKET; es = list_expr; RIGHT_SQ_BRACKET { S.EList es }
  | LEFT_PAREN; e = expr; RIGHT_PAREN { e }

const_expr:
  | FALSE { S.CBool false }
  | TRUE { S.CBool true }
  | i = LITERAL_INT { S.CInt i }
  | s = LITERAL_STRING { S.CStr s }
  | f = LITERAL_FLOAT { S.CFloat f }

handler_expr:
  | LEFT_BRACE; c = separated_nonempty_list(VERTICAL_BAR, handler_clause); RIGHT_BRACE
    {
      let ret, ops =
        List.fold_left
          (fun acc -> function
            | Return _ when (Option.is_some @@ fst acc) ->
               let msg = "Return clauses have to be single in a handler" in
               raise @@ S.Error msg
            | Return (x, e) -> (Some (x, e), snd acc)
            | Operation op -> (fst acc, op :: (snd acc)))
          (None, []) c
      in
      let ret =
        Option.fold ~none:("x", S.EId "x") ~some:(fun x -> x) ret
      in
      ignore @@
        List.fold_left
          (fun s { S.op_name; _ } ->
            if IdSet.mem op_name s then
              let msg = "Operation clauses with the same name \"" ^ op_name ^
                          "\" have to be signle in a handler"
              in
              raise @@ S.Error msg
            else IdSet.add op_name s)
          IdSet.empty ops;
      (ret, ops)
    }

handler_clause:
  | RETURN; x = ID; RIGHT_ARROW; e = expr { Return (x, e) }
  | op_name = ID; op_arg_var = ID; op_cont_var = ID; RIGHT_ARROW; op_body = expr
    {
      check_pattern_vars [op_arg_var; op_cont_var];
      let open S in Operation { op_name; op_arg_var; op_cont_var; op_body }
    }

match_clause:
  | LEFT_PAREN; x = ID; COMMA; y = ID; RIGHT_PAREN; RIGHT_ARROW; e = expr_below_semi
    {
      check_pattern_vars [x; y];
      S.MPair (x, y, e)
    }
  | INL; x = ID; RIGHT_ARROW; ex = expr; VERTICAL_BAR; INR; y = ID; RIGHT_ARROW; ey = expr_below_semi
    { S.MInj (x, ex, y, ey) }
  | LEFT_SQ_BRACKET; RIGHT_SQ_BRACKET; RIGHT_ARROW; en = expr; VERTICAL_BAR;
    x = ID; DOUBLE_COLON; xs = ID; RIGHT_ARROW; ec = expr_below_semi
    {
      check_pattern_vars [x; xs];
      S.MList (en, x, xs, ec)
    }

param_list:
  | xs = ID* { xs }

nonempty_param_list:
  | xs = ID+ { xs }

%inline binary_op:
  | PLUS { "+" }
  | MINUS { "-" }
  | ASTERISK { "*" }
  | SLASH { "/" }
  | PERCENT { "%" }
  | CARET { "^" }
  | DOUBLE_VERTICAL_BAR { "||" }
  | DOUBLE_AMPERSAND { "&&" }
  | EQUAL { "=" }
  | LESS_GREAT { "<>" }
  | LESS { "<" }
  | LESS_EQUAL { "<=" }
  | GREAT { ">" }
  | GREAT_EQUAL { ">=" }
  | DOUBLE_COLON { "::" }

ty_signature:
  | tyvars = tyvar+; DOT; ty_sig = ty_signature_mono
    { make_ty_sig tyvars ty_sig }
  | ty_sig = ty_signature_mono
    { make_ty_sig [] ty_sig }

ty_signature_mono:
  | dom_ty = ty_mono; DOUBLE_RIGHT_ARROW; codom_ty = ty_mono
    { (dom_ty, codom_ty) }

ty_mono:
  | t1 = ty_mono; ASTERISK; t2 = ty_fun
    { fun l -> T.TyProd (t1 l, t2 l) }
  | t = ty_fun { t }

ty_fun:
  | t1 = ty_simple; RIGHT_ARROW; t2 = ty_fun
    { fun l -> T.TyFun (t1 l, t2 l) }
  | t = ty_simple { t }

ty_simple:
  | t = ty_const { fun _ -> T.TyBase t }
  | var = tyvar { fun l -> T.TyVar (l var) }

ty_const:
  | INT { T.TyInt }
  | BOOL { T.TyBool }
  | STRING { T.TyStr }
  | FLOAT { T.TyFloat }

tyvar:
  | SINGLE_QUOTE; x = ID { x }
