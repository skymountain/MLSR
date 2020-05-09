let rec read_eval_print lexbuf env tyenv =
  let resume msg =
    print_endline msg;
    read_eval_print lexbuf env tyenv
  in
  try
    flush stderr;
    flush stdout;
    match Parser.main Lexer.main lexbuf with
    | None -> print_endline "Termianted."
    | Some d ->
      let tyenv', msg = Typing.type_decl tyenv d in
      print_endline msg;
      let env', v_opt = Eval.eval_decl env d in
      Option.fold
        ~none:()
        ~some:(fun v -> print_endline @@ Syntax.stringify_value v)
        v_opt;
      read_eval_print lexbuf env' tyenv'
  with
  | Syntax.Error msg -> resume @@ "Syntax error: " ^ msg
  | Eval.Error msg -> resume @@ "Run-time error: " ^ msg
  | Typing.Error msg -> resume @@ "Typing error: " ^ msg
  | Parsing.Parse_error -> resume "Paring error"
;;

let env, tyenv =
  let open Option in
  let open Type in
  let open Syntax in
  let open Eval in
  let raise_err msg = raise @@ Eval.Error msg in
  let add_bin_ops
      err apply (* : 'a -> value -> value -> value option *) ty =
    List.fold_left (fun (env, tyenv) (x, op) ->
        let v = VFun (fun v1 -> return @@ VFun (fun v2 ->
            match apply op v1 v2 with Some v -> RVal v | None -> err x))
        in
        (Env.add x v env, Env.add x ty tyenv))
  in
  let add_const_bin_ops err apply (* : 'a -> const -> const -> value option *) =
    add_bin_ops err
      (fun op v1 v2 ->
         match v1, v2 with VConst c1, VConst c2 -> apply op c1 c2 | _ -> none)
  in
  let pair_env = (Env.empty, Env.empty) in
  (* ops of int -> int -> int *)
  let pair_env = add_const_bin_ops
      (fun x ->
         raise_err @@ "Operator \"" ^ x ^ "\" can be applied only to integers")
      (fun op c1 c2 -> match c1, c2 with
           CInt i1, CInt i2 -> some @@ VConst (CInt (op i1 i2)) | _ -> none)
      (tyscheme_of_mono @@
       TyFun (TyBase TyInt, TyFun (TyBase TyInt, TyBase TyInt)))
      pair_env
      [("+", (+)); ("-", (-)); ("*", ( * )); ("/", (/)); ("%", (mod))]
  in
  (* ops of int -> int -> bool *)
  let pair_env = add_const_bin_ops
      (fun x ->
         raise_err @@ "Operator \"" ^ x ^ "\" can be applied only to integers")
      (fun op c1 c2 -> match c1, c2 with
           CInt i1, CInt i2 -> some @@ VConst (CBool (op i1 i2)) | _ -> none)
      (tyscheme_of_mono @@
       TyFun (TyBase TyInt, TyFun (TyBase TyInt, TyBase TyBool)))
      pair_env
      [("<", (<)); ("<=", (<=)); (">", (>)); (">=", (>=))]
  in
  (* ops of bool -> bool -> bool *)
  let pair_env = add_const_bin_ops
      (fun x ->
         raise_err @@ "Operator \"" ^ x ^ "\" can be applied only to Booleans")
      (fun op c1 c2 -> match c1, c2 with
           CBool b1, CBool b2 -> some @@ VConst (CBool (op b1 b2)) | _ -> none)
      (tyscheme_of_mono @@
       TyFun (TyBase TyBool, TyFun (TyBase TyBool, TyBase TyBool)))
      pair_env
      [("&&", (&&)); ("||", (||))]
  in
  (* ops of string -> string -> string *)
  let pair_env = add_const_bin_ops
      (fun x ->
         raise_err @@ "Operator \"" ^ x ^ "\" can be applied only to strings")
      (fun op c1 c2 -> match c1, c2 with
           CStr s1, CStr s2 -> some @@ VConst (CStr (op s1 s2)) | _ -> none)
      (tyscheme_of_mono @@
       TyFun (TyBase TyStr, TyFun (TyBase TyStr, TyBase TyStr)))
      pair_env
      [("^", (^))]
  in
  (* cons *)
  let pair_env =
    let tyvar0 = fresh_tyvar () in
    add_bin_ops
      (fun _ -> assert false)
      (fun op v1 v2 -> try some @@ op v1 v2 with _ -> none)
      (closing Env.empty @@ TyFun (tyvar0, TyFun (TyList tyvar0, TyList tyvar0)))
      pair_env
      ["::",  (fun v1 v2 -> VCons (v1, v2))]
  in
  (* comparison operators *)
  let pair_env =
    let tyvar0 = fresh_tyvar () in
    add_bin_ops
      (fun x ->
         raise_err @@ "Incomparable objects were comapred by \"" ^ x ^ "\"")
      (fun op v1 v2 -> try some @@ op v1 v2 with _ -> none)
      (closing Env.empty @@ TyFun (tyvar0, TyFun (tyvar0, TyBase TyBool)))
      pair_env
      ["=",  (fun v1 v2 -> VConst (CBool (v1 = v2)));
       "<>", (fun v1 v2 -> VConst (CBool (v1 <> v2)));]
  in
  (* sequential composition *)
  let pair_env =
    let tyvar0 = fresh_tyvar () in
    let tyvar1 = fresh_tyvar () in
    add_bin_ops
      (fun _ -> assert false)
      (fun op v1 v2 -> some @@ op v1 v2)
      (closing Env.empty @@ TyFun (tyvar0, TyFun (tyvar1, tyvar1)))
      pair_env
      [";", (fun _ v2 -> v2)]
  in
  pair_env
;;

let _ = read_eval_print
    (Lexing.from_channel stdin) (env, Env.empty) (tyenv, Env.empty)
;;
