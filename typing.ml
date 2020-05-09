module S = Syntax
module T = Type

exception Error of string
;;

let type_const = function
  | S.CInt _ -> T.TyInt
  | S.CBool _ -> T.TyBool
  | S.CStr _ -> T.TyStr
  | S.CFloat _ -> T.TyFloat
  | S.CUnit -> T.TyUnit
;;

let constraints_of_subst s =
  List.map (fun (x, ty) -> (T.TyVar x, ty)) @@ T.TyvarMap.bindings s
;;

let constraints_of_subst_list ss =
  List.flatten @@ List.map constraints_of_subst ss
;;

let solve =
  let rec solve = function
    | (T.TyVar _ as t1), (T.TyVar _ as t2)
    | (T.TyBase _ as t1), (T.TyBase _ as t2)
    | (T.TyVarFixed _ as t1), (T.TyVarFixed _ as t2)
      when t1 = t2 -> T.TyvarMap.empty
    | (T.TyVar x, ty) when not @@ T.TyvarSet.mem x (T.free_tyvars ty) ->
      T.TyvarMap.singleton x ty
    | (ty, T.TyVar x) when not @@ T.TyvarSet.mem x (T.free_tyvars ty) ->
      T.TyvarMap.singleton x ty
    | TyFun (t11, t12), TyFun (t21, t22)
    | TyProd (t11, t12), TyProd (t21, t22)
    | TySum (t11, t12), TySum (t21, t22)
      ->
      let s1 = solve (t11, t21) in
      let t12 = T.subst_ty s1 t12 in
      let t22 = T.subst_ty s1 t22 in
      let s2 = solve (t12, t22) in
      T.TyvarMap.union (fun _ _ _ -> assert false) s1 s2
    | TyList t1, TyList t2 -> solve (t1, t2)
    | ((  T.TyVar _
        | T.TyBase _
        | T.TyVarFixed _
        | T.TyFun _
        | T.TyProd _
        | T.TySum _
        | T.TyList _
       ) as t1), (_ as t2) ->
      let msg = Printf.sprintf "Types \"%s\" and \"%s\" cannot be unified"
          (T.stringify_mono_ty t1) (T.stringify_mono_ty t2)
      in
      raise @@ Error msg
  in
  List.fold_left (fun s (ty1, ty2) ->
      let ty1 = T.subst_ty s ty1 in
      let ty2 = T.subst_ty s ty2 in
      let s' = solve (ty1, ty2) in
      let s = T.subst_subst ~by:s' ~target:s in
      T.TyvarMap.union (fun _ _ _ -> assert false) s s')
    T.TyvarMap.empty
;;

let rec type_expr ((var_env, op_env) as env) = function
  | S.EId x -> begin
      match Env.find_opt x var_env with
      | Some ty_scheme -> (T.instantiate ty_scheme, T.TyvarMap.empty)
      | None -> raise @@ Error (Printf.sprintf "Variable \"%s\" is not defined" x)
    end
  | S.EConst c -> (TyBase (type_const c), T.TyvarMap.empty)
  | S.ELet (x, e1, e2) ->
    let ty1, s1 = type_expr env e1 in
    let var_env' = T.subst_tyenv s1 var_env in
    let ty_scheme1 = T.closing var_env' ty1 in
    let ty2, s2 = type_expr (Env.add x ty_scheme1 var_env', op_env) e2 in
    let s = solve @@ constraints_of_subst_list [s1; s2] in
    (T.subst_ty s ty2, s)
  | S.ELetRec (x, y, e1, e2) ->
    let arg_ty = T.fresh_tyvar () in
    let ret_ty = T.fresh_tyvar () in
    let fun_ty = T.TyFun (arg_ty, ret_ty) in
    let ty1, s1 =
      let var_env' =
        Env.add y (T.tyscheme_of_mono arg_ty) @@
        Env.add x (T.tyscheme_of_mono fun_ty) @@
        var_env
      in
      type_expr (var_env', op_env) e1
    in
    let s1 = solve @@ (ret_ty, ty1) :: (constraints_of_subst s1) in
    let fun_ty' = T.subst_ty s1 fun_ty in
    let var_env' = T.subst_tyenv s1 var_env in
    let fun_ty_scheme = T.closing var_env' fun_ty' in
    let ty2, s2 = type_expr (Env.add x fun_ty_scheme var_env', op_env) e2 in
    let s = solve @@ constraints_of_subst_list [s1; s2] in
    (T.subst_ty s ty2, s)
  | S.EFun (x, e) ->
    let arg_ty = Type.fresh_tyvar () in
    let ret_ty, s =
      let var_env' = Env.add x (T.tyscheme_of_mono arg_ty) var_env in
      type_expr (var_env', op_env) e in
    let fun_ty = T.TyFun (T.subst_ty s arg_ty, ret_ty) in
    (fun_ty, s)
  | S.EApp (e1, e2) ->
    let fun_ty, s1 = type_expr env e1 in
    let arg_ty, s2 = type_expr env e2 in
    let ret_ty = T.fresh_tyvar () in
    let c =
      (fun_ty, T.TyFun (arg_ty, ret_ty)) ::
      (constraints_of_subst_list [s1; s2])
    in
    let s = solve c in
    (T.subst_ty s ret_ty, s)
  | S.EPair (e1, e2) ->
    let fst_ty, s1 = type_expr env e1 in
    let snd_ty, s2 = type_expr env e2 in
    let s = solve @@ constraints_of_subst_list [s1; s2] in
    (T.subst_ty s (TyProd (fst_ty, snd_ty)), s)
  | S.EHandle (e, ((ret_x, ret_body), ops)) ->
    let handled_ty, s1 = type_expr env e in
    let ret_ty, s2 =
      let var_env' = Env.add ret_x (T.tyscheme_of_mono handled_ty) var_env in
      type_expr (var_env', op_env) ret_body in
    let s3 = type_handler env ret_ty ops in
    let s = solve @@ constraints_of_subst_list [s1; s2; s3] in
    (T.subst_ty s ret_ty, s)
  | S.EInl e ->
    let left_ty, s = type_expr env e in
    let right_ty = T.fresh_tyvar () in
    (T.TySum (left_ty, right_ty), s)
  | S.EInr e ->
    let right_ty, s = type_expr env e in
    let left_ty = T.fresh_tyvar () in
    (T.TySum (left_ty, right_ty), s)
  | S.EList es ->
    let elem_ty = T.fresh_tyvar () in
    let c = List.fold_left (fun c e ->
        let ty, s = type_expr env e in
        (elem_ty, ty) :: ((constraints_of_subst s) @ c)) [] es
    in
    let s = solve c in
    (T.TyList (T.subst_ty s elem_ty), s)
  | S.EMatch (e, m) ->
    let mty, sm = type_expr env e in
    match m with
    | MPair (x, y, e) ->
      let x_ty = T.fresh_tyvar () in
      let y_ty = T.fresh_tyvar () in
      let cty, sc =
        let var_env' =
          Env.add x (T.tyscheme_of_mono x_ty) @@
          Env.add y (T.tyscheme_of_mono y_ty) @@
          var_env
        in
        type_expr (var_env', op_env) e
      in
      let c =
        (T.TyProd (x_ty, y_ty), mty) ::
        (constraints_of_subst_list [sm; sc])
      in
      let s = solve c in
      (T.subst_ty s cty, s)
    | MInj (x, ex, y, ey) ->
      let x_ty = T.fresh_tyvar () in
      let y_ty = T.fresh_tyvar () in
      let x_cty, x_sc =
        let var_env' = Env.add x (T.tyscheme_of_mono x_ty) var_env in
        type_expr (var_env', op_env) ex
      in
      let y_cty, y_sc =
        let var_env' = Env.add y (T.tyscheme_of_mono y_ty) var_env in
        type_expr (var_env', op_env) ey
      in
      let c = (x_cty, y_cty) :: (T.TySum (x_ty, y_ty), mty) ::
              (constraints_of_subst_list [sm; x_sc; y_sc]) in
      let s = solve c in
      (T.subst_ty s x_cty, s)
    | MList (en, x, xs, ec) ->
      let elem_ty = T.fresh_tyvar () in
      let n_cty, n_sc = type_expr env en in
      let c_cty, c_sc =
        let var_env' =
          Env.add x (T.tyscheme_of_mono elem_ty) @@
          Env.add xs (T.tyscheme_of_mono (T.TyList elem_ty)) @@
          var_env
        in
        type_expr (var_env', op_env) ec
      in
      let c = (n_cty, c_cty) :: (T.TyList elem_ty, mty) ::
              (constraints_of_subst_list [sm; n_sc; c_sc]) in
      let s = solve c in
      (T.subst_ty s n_cty, s)

and type_handler env ret_ty ops =
  let constraints = List.map (type_operation_clause env ret_ty) ops in
  solve (List.flatten constraints)

and type_operation_clause (var_env, op_env) ret_ty
    { op_name; op_arg_var; op_cont_var; op_body } =
    match T.OpMap.find_opt op_name op_env with
    | None ->
      raise @@ Error
        (Printf.sprintf "Effect operation \"%s\" is not declared" op_name)
    | Some ty_sig ->
      let fixed_tyvars, dom_ty, codom_ty = T.instantiate_ty_sig ty_sig in
      let arg_ty = T.tyscheme_of_mono dom_ty in
      let cont_ty = T.tyscheme_of_mono @@ T.TyFun (codom_ty, ret_ty) in
      let op_body_ty, s =
        let var_env' =
          Env.add op_arg_var arg_ty @@
          Env.add op_cont_var cont_ty @@
          var_env
        in
        type_expr (var_env', op_env) op_body
      in
      let free_fixed_tyvars =
        T.TyvarSet.inter fixed_tyvars (T.free_tyvars op_body_ty)
      in
      if T.TyvarSet.is_empty free_fixed_tyvars then
        (ret_ty, op_body_ty) :: (constraints_of_subst s)
      else
        raise @@
        Error "Type varaibles bound in an operation clause cannot be escaped"
;;

let signature_restriction =
  let rec tyvars_at_pos = function
    | T.TyVar x -> T.TyvarSet.singleton x
    | T.TyVarFixed _ -> assert false
    | T.TyBase _ -> T.TyvarSet.empty
    | T.TyFun (arg_ty, ret_ty) ->
      T.TyvarSet.union (tyvars_at_neg arg_ty) (tyvars_at_pos ret_ty)
    | T.TyProd (ty1, ty2) | T.TySum (ty1, ty2) ->
      T.TyvarSet.union (tyvars_at_pos ty1) (tyvars_at_pos ty2)
    | T.TyList ty -> tyvars_at_pos ty
  and tyvars_at_neg = function
    | T.TyVar _ | TyBase _ -> T.TyvarSet.empty
    | T.TyVarFixed _ -> assert false
    | T.TyFun (arg_ty, ret_ty) ->
      T.TyvarSet.union (tyvars_at_pos arg_ty) (tyvars_at_neg ret_ty)
    | T.TyProd (ty1, ty2) | T.TySum (ty1, ty2) ->
      T.TyvarSet.union (tyvars_at_neg ty1) (tyvars_at_neg ty2)
    | T.TyList ty -> tyvars_at_neg ty
  in
  let rec tyvars_at_nonstrict_pos = function
    | T.TyVar _  | T.TyBase _ -> T.TyvarSet.empty
    | T.TyVarFixed _ -> assert false
    | T.TyFun (arg_ty, ret_ty) ->
      T.TyvarSet.union
        (tyvars_at_neg arg_ty)
        (tyvars_at_nonstrict_pos ret_ty)
    | T.TyProd (ty1, ty2) | T.TySum (ty1, ty2) ->
      T.TyvarSet.union
        (tyvars_at_nonstrict_pos ty1)
        (tyvars_at_nonstrict_pos ty2)
    | T.TyList ty -> tyvars_at_nonstrict_pos ty
  in
  fun (tyvars, dom_ty, codom_ty) ->
    let dom_sat = T.TyvarSet.disjoint
      tyvars (tyvars_at_nonstrict_pos dom_ty)
    in
    let codom_sat = T.TyvarSet.disjoint
      tyvars (tyvars_at_neg codom_ty)
    in
    if (not dom_sat) && (not codom_sat) then
      Some "both of the domain and codomain types"
    else if not dom_sat then
      Some "the domain type"
    else if not codom_sat then
      Some "the codomain type"
    else
      None
;;

let check_closed_tyenv (var_env, op_env) =
  assert (T.TyvarSet.is_empty @@ T.free_tyvars_in_tyenv var_env);
  assert (T.TyvarSet.is_empty @@ T.free_tyvars_in_openv op_env)
;;

let type_decl ((var_env, op_env) as env) =
  check_closed_tyenv env;
  function
  | S.DExpr e ->
    let ty, _ = type_expr env e in
    let ty_scheme = T.closing var_env ty in
    let msg = Printf.sprintf "- : %s" (T.stringify_ty_scheme ty_scheme) in
    (env, msg)
  | S.DLet (x, e) ->
    let ty, _ = type_expr env e in
    let ty_scheme = T.closing var_env ty in
    let msg = Printf.sprintf "%s : %s" x (T.stringify_ty_scheme ty_scheme) in
    let env' = (Env.add x ty_scheme var_env, op_env) in
    (env', msg)
  | S.DEff (op_name, ((tyvars, dom_ty, codom_ty) as ty_sig)) ->
    match signature_restriction ty_sig with
    | Some blame ->
      let msg = Printf.sprintf
          "The type siganture does not follow the signature restriction on %s"
          blame
      in
      raise @@ Error msg
    | None ->
      let msg = Printf.sprintf "Effect operation \"%s\" is defined" op_name in
      let ty_scheme = T.closing var_env @@
        T.instantiate (tyvars, T.TyFun (dom_ty, codom_ty))
      in
      let env' =
        (Env.add op_name ty_scheme var_env, Env.add op_name ty_sig op_env)
      in
      (env', msg)
;;
