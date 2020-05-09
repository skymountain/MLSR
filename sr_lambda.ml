let rec read_eval_print lexbuf env tyenv =
  let resume msg =
    print_endline msg;
    read_eval_print lexbuf env tyenv
  in
  try
    print_string "# ";
    flush stderr;
    flush stdout;
    match Parser.main Lexer.main lexbuf with
    | None -> print_endline "Termianted."
    | Some d ->
      let tyenv', typing_msg = Typing.type_decl tyenv d in
      let env', v_opt = Eval.eval_decl env d in
      print_endline @@
        Option.fold v_opt
          ~none:typing_msg
          ~some:(fun v ->
              Printf.sprintf "val %s = %s"
                typing_msg
                (Syntax.stringify_value v));
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
      (tyscheme_of_mono @@
       TyFun (TyBase TyInt, TyFun (TyBase TyInt, TyBase TyInt)))
      pair_env
      [("+", (+)); ("-", (-)); ("*", ( * )); ("/", (/)); ("%", (mod))]
  in
  (* ops of int -> int -> bool *)
  let pair_env = add_const_ops
      (fun op -> function
           [CInt i1; CInt i2] -> some @@ CBool (op i1 i2) | _ -> none)
      (fun x ->
         raise_err @@ "Operator \"" ^ x ^ "\" can be applied only to integers")
      (tyscheme_of_mono @@
       TyFun (TyBase TyInt, TyFun (TyBase TyInt, TyBase TyBool)))
      pair_env
      [("<", (<)); ("<=", (<=)); (">", (>)); (">=", (>=))]
  in
  (* ops of bool -> bool -> bool *)
  let pair_env = add_const_ops
      (fun op -> function
         | [CBool b1; CBool b2] -> some @@ CBool (op b1 b2)
         | _ -> none)
      (fun x ->
         raise_err @@ "Operator \"" ^ x ^ "\" can be applied only to Booleans")
      (tyscheme_of_mono @@
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
        (tyscheme_of_mono @@
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
        (tyscheme_of_mono
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
        (tyscheme_of_mono (TyFun (TyBase TyStr, TyBase TyInt)))
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
    let tyvar0 = fresh_tyvar () in
    add_ops
      (fun op -> function [v1; v2] -> (try some @@ op v1 v2 with _ -> none)
                        | _ -> none)
      (fun x ->
         raise_err @@ "Incomparable objects were comapred by \"" ^ x ^ "\"")
      (closing Env.empty @@
       TyFun (tyvar0, TyFun (tyvar0, TyBase TyBool)))
      pair_env
      ["=",  (fun v1 v2 -> VConst (CBool (v1 = v2)));
       "<>", (fun v1 v2 -> VConst (CBool (v1 <> v2)));]
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

let _ =
  let arg_specs = [
    ("--disable-signature-restriction",
     Arg.Clear Typing.check_SR,
     "Disable checking if type signatures of effect operations follow \
      signature restriction");
  ]
  in
  let doc = "An interpreter of mini ML with \
             let-polymorphism, algebraic effect handlers, and \
             signature restriction"
  in
  Arg.parse arg_specs ignore doc;
  read_eval_print
    (Lexing.from_channel stdin) (env, Env.empty) (tyenv, Env.empty)
;;
