open Option
open Syntax

exception Error of string
;;

let err s = raise @@ Error s
;;

let rec ( let* ) res f =
  match res with
  | RVal v -> f v
  | RCont (id, v, cont) -> RCont (id, v, (fun v -> let* v' = cont v in f v'))
;;

let return v = RVal v
;;

let val_of_res = function
  | RVal v -> v
  | RCont _ -> err "Uncaught continuation"
;;

let rec eval_expr ((var_env, op_env) as env) = function
  | EId x -> return @@ Env.find x var_env
  | EConst c -> return @@ VConst c
  | ELet (x, e1, e2) ->
    let* v1 = eval_expr env e1 in
    eval_expr (Env.add x v1 var_env, op_env) e2
  | ELetRec (x, y, e1, e2) ->
    let rec fixed_point () =
      VFun (fun yv ->
          let var_env' =
            Env.add y yv @@
            Env.add x (fixed_point ()) @@
            var_env
          in
          eval_expr (var_env', op_env) e1)
    in
    let v1 = fixed_point () in
    eval_expr (Env.add x v1 var_env, op_env) e2
  | EFun (x, e) ->
    return @@ VFun (fun v -> eval_expr (Env.add x v var_env, op_env) e)
  | EApp (e1, e2) ->
    begin
      let* v1 = eval_expr env e1 in
      let* v2 = eval_expr env e2 in
      match v1 with
      | VConst c ->
        err @@
          "Constant \"" ^ (Syntax.stringify_const c) ^ "\" cannot be applied"
      | VFun f -> f v2
      | VPair _ | VInl _ | VInr _ | VNil | VCons _ ->
        err @@
          Printf.sprintf "\"%s\" cannot be applied" @@ stringify_value v1
    end
  | EHandle (e, (ret, ops)) -> handle env ret ops @@ eval_expr env e
  | EPair (e1, e2) ->
    let* v1 = eval_expr env e1 in
    let* v2 = eval_expr env e2 in
    return @@ VPair (v1, v2)
  | EInl e -> let* v = eval_expr env e in return @@ VInl v
  | EInr e -> let* v = eval_expr env e in return @@ VInr v
  | EList es -> eval_expr_list env [] es
  | EMatch (e, m) ->
    let* v = eval_expr env e in
    match v, m with
    | VPair (v1, v2), MPair (x, y, e) ->
      let var_env' =
        Env.add x v1 @@
        Env.add y v2 @@
        var_env
      in
      eval_expr (var_env', op_env) e
    | VInl v, MInj (x, e, _, _) -> eval_expr (Env.add x v var_env, op_env) e
    | VInr v, MInj (_, _, y, e) -> eval_expr (Env.add y v var_env, op_env) e
    | VNil, MList (e, _, _, _) -> eval_expr env e
    | VCons (v, vs), MList (_, x, xs, e) ->
      let var_env' =
        Env.add x v @@
        Env.add xs vs @@
        var_env
      in
      eval_expr (var_env', op_env) e
    | _, _ ->
      err "Found mismatch between a matched value and a pattern"

and eval_expr_list env vs = function
  | [] -> return @@ List.fold_left (fun acc v -> VCons (v, acc)) VNil vs
  | e::es -> let* v = eval_expr env e in eval_expr_list env (v::vs) es

and handle ((var_env, op_env) as env) ret ops = function
  | RVal v -> let x, body = ret in eval_expr (Env.add x v var_env, op_env) body
  | RCont (op_id, v, cont) -> begin
    let r =
      List.find_opt
        (fun { op_name; _ } ->
           Option.fold ~none:false ~some:((=) op_id) @@
           Env.find_opt op_name op_env)
        ops
    in
    match r with
    | None -> RCont (op_id, v, (fun v -> handle env ret ops @@ cont v))
    | Some { op_arg_var; op_cont_var; op_body; _ } ->
      let var_env' =
        Env.add op_arg_var v @@
        Env.add op_cont_var (VFun cont) @@
        var_env
      in
      eval_expr (var_env', op_env) op_body
  end
;;

let eval_decl (((var_env : value Env.t), (op_env : int Env.t)) as env) =
  function
  | DExpr e ->
    (env, some @@ val_of_res @@ eval_expr env e)
  | DLet (x, e) ->
    let v = val_of_res @@ eval_expr env e in
    let env' = (Env.add x v var_env, op_env) in
    (env', some v)
  | DEff (op_name, _) ->
    let op_id = OpId.fresh_op_id () in
    let f = VFun (fun v -> RCont (op_id, v, return)) in
    let env' = (Env.add op_name f var_env, Env.add op_name op_id op_env) in
    (env', none)
;;
