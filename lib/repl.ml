let rec read_eval_print lexbuf env tyenv =
  let resume msg =
    print_endline msg;
    Lexing.flush_input lexbuf;
    read_eval_print lexbuf env tyenv
  in
  try
    print_string "# ";
    flush stderr;
    flush stdout;
    match Parser.main Lexer.main lexbuf with
    | None -> print_endline "Termianted."
    | Some d ->
      let tyenv', tysc = Typing.type_decl tyenv d in
      let env', v_opt = Eval.eval_decl env d in
      let msg =
        let tysc_str = Type.string_of_tysc tysc in
        match d with
        | DExpr _ ->
          Printf.sprintf "val - : %s = %s" tysc_str
            (Syntax.string_of_value @@ Option.get v_opt)
        | DLet (x, _) ->
          Printf.sprintf "val %s : %s = %s" x tysc_str
            (Syntax.string_of_value @@ Option.get v_opt)
        | DEff (op_name, _) ->
          Printf.sprintf "effect %s : %s defined" op_name tysc_str
      in
      print_endline msg;
      read_eval_print lexbuf env' tyenv'
  with
  | Syntax.Error msg -> resume @@ "Syntax error: " ^ msg
  | Eval.Error msg -> resume @@ "Run-time error: " ^ msg
  | Typing.Error msg -> resume @@ "Typing error: " ^ msg
  | Parsing.Parse_error -> resume @@
    Printf.sprintf
      "Paring error: line %d, column %d--%d"
      lexbuf.lex_curr_p.pos_lnum
      lexbuf.lex_start_p.pos_cnum
      lexbuf.lex_curr_p.pos_cnum
;;

let env, tyenv =
  let open Option in
  let open Type in
  let open Syntax in
  let open Eval in
  let raise_err msg = raise @@ Eval.Error msg in
  let arity_of (_, ty) =
    let rec iter = function
      | TyFun (_, t) -> 1 + iter t
      | TyVar _
      | TyVarFixed _
      | TyBase _
      | TyProd _
      | TySum _
      | TyList _
        -> 0
    in
    iter ty
  in
  let rec value_rep_of_op apply err rev_args arity =
    if arity = 0 then
      match apply (List.rev rev_args) with Some v -> v | None -> err ()
    else
      VFun (fun v -> return @@
             value_rep_of_op apply err (v::rev_args) (arity - 1))
  in
  let add_ops apply err ty =
    let arity = arity_of ty in
    List.fold_left (fun (env, tyenv) (x, op) ->
        let v = value_rep_of_op
            (fun vs -> apply op vs)
            (fun () -> err x)
            []
            arity
        in
        (Env.add x v env, Env.add x ty tyenv))
  in
  let add_const_ops apply =
    let capply op vs =
      let cvs_opt =
        List.fold_right
          (fun v cvs_opt ->
             bind cvs_opt (fun cvs ->
                 match v with VConst cv -> some @@ cv :: cvs
                            | VFun _
                            | VPair _
                            | VInl _ | VInr _
                            | VNil | VCons _
                              -> none))
          vs (some [])
      in
      bind cvs_opt
        (fun cvs ->
           let res = apply op cvs in
           Option.map (fun cv -> VConst cv) res)
    in
    add_ops capply
  in
  let pair_env = (Env.empty, Env.empty)
  in
  (* ops of int -> int -> int *)
  let pair_env = add_const_ops
      (fun op -> function
           [CInt i1; CInt i2] -> some @@ CInt (op i1 i2) | _ -> none)
      (fun x ->
         raise_err @@ "Operator \"" ^ x ^ "\" can be applied only to integers")
      (tysc_of_ty @@
       TyFun (TyBase TyInt, TyFun (TyBase TyInt, TyBase TyInt)))
      pair_env
      [("+", (+)); ("-", (-)); ("*", ( * )); ("/", (/)); ("%", (mod))]
  in
  (* ops of float -> float -> float *)
  let pair_env = add_const_ops
      (fun op -> function
           [CFloat f1; CFloat f2] -> some @@ CFloat (op f1 f2) | _ -> none)
      (fun x ->
         raise_err @@ "Operator \"" ^ x ^ "\" can be applied only to \
                                           floating numbers")
      (tysc_of_ty @@
       TyFun (TyBase TyFloat, TyFun (TyBase TyFloat, TyBase TyFloat)))
      pair_env
      [("+.", (+.)); ("-.", (-.)); ("*.", ( *. )); ("/.", (/.));]
  in
  (* ops of bool -> bool -> bool *)
  let pair_env = add_const_ops
      (fun op -> function
         | [CBool b1; CBool b2] -> some @@ CBool (op b1 b2)
         | _ -> none)
      (fun x ->
         raise_err @@ "Operator \"" ^ x ^ "\" can be applied only to Booleans")
      (tysc_of_ty @@
       TyFun (TyBase TyBool, TyFun (TyBase TyBool, TyBase TyBool)))
      pair_env
      [("&&", (&&)); ("||", (||))]
  in
  (* ops of string *)
  let pair_env =
    (* concatenation *)
    let pair_env =
      add_const_ops
        (fun op -> function
             [CStr s1; CStr s2] -> some @@ CStr (op s1 s2) | _ -> none)
        (fun x ->
           raise_err @@ "Operator \"" ^ x ^ "\" can be applied only to strings")
        (tysc_of_ty @@
         TyFun (TyBase TyStr, TyFun (TyBase TyStr, TyBase TyStr)))
        pair_env
        [("^", (^))]
    in
    (* substring *)
    let pair_env =
      add_const_ops
        (fun op -> function
             [CStr s; CInt start; CInt len] ->
             (try some @@ CStr (op s start len) with _ -> none)
           | _ -> none)
        (fun x -> raise_err @@ "Invlida use of \"" ^ x ^ "\"")
        (tysc_of_ty
           (TyFun (TyBase TyStr,
                   TyFun (TyBase TyInt,
                          TyFun (TyBase TyInt, TyBase TyStr)))))
        pair_env
        [("str_sub", String.sub)]
    in
    (* length *)
    let pair_env =
      add_const_ops
        (fun op -> function [CStr s] -> some @@ CInt (op s) | _ -> none)
        (fun x ->
           raise_err @@ "Function \"" ^ x ^ "\" can be applied only to strings")
        (tysc_of_ty (TyFun (TyBase TyStr, TyBase TyInt)))
        pair_env
        [("str_len", String.length)]
    in
    pair_env
  in
  (* cons *)
  let pair_env =
    let tyvar0 = fresh_tyvar () in
    add_ops
      (fun op -> function [v1; v2] -> some @@ op v1 v2 | _ -> none)
      (fun _ -> assert false)
      (closing Env.empty @@
       TyFun (tyvar0, TyFun (TyList tyvar0, TyList tyvar0)))
      pair_env
      ["::",  (fun v1 v2 -> VCons (v1, v2))]
  in
  (* comparison operators *)
  let pair_env =
    let op f v1 v2 = VConst (CBool (f v1 v2)) in
    let tyvar0 = fresh_tyvar () in
    add_ops
      (fun op -> function [v1; v2] -> (try some @@ op v1 v2 with _ -> none)
                        | _ -> none)
      (fun x ->
         raise_err @@ "Incomparable objects were comapred by \"" ^ x ^ "\"")
      (closing Env.empty @@
       TyFun (tyvar0, TyFun (tyvar0, TyBase TyBool)))
      pair_env
      ["=",  op (=);
       "<>", op (<>);
       "<",  op (<);
       "<=", op (<=);
       ">",  op (>);
       ">=", op (>=);
      ]
  in
  (* sequential composition *)
  let pair_env =
    let tyvar0 = fresh_tyvar () in
    let tyvar1 = fresh_tyvar () in
    add_ops
      (fun op -> function [v1; v2] -> some @@ op v1 v2 | _ -> none)
      (fun _ -> assert false)
      (closing Env.empty @@
       TyFun (tyvar0, TyFun (tyvar1, tyvar1)))
      pair_env
      [";", (fun _ v2 -> v2)]
  in
  pair_env
;;
