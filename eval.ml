open Option
open Syntax

exception Error of string
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
  | RCont _ -> raise @@ Error "Uncaught continuation"
;;

let rec eval_expr ((var_env, op_env) as env) = function
  | EId x -> return @@ Env.find x var_env
  | EConst c -> return @@ VConst c
  | EFun (x, e) ->
    return @@ VFun (fun v -> eval_expr (Env.add x v var_env, op_env) e)
  | EApp (e1, e2) ->
    begin
      let* v1 = eval_expr env e1 in
      let* v2 = eval_expr env e2 in
      match v1 with
      | VConst c ->
        let msg =
          "Constant \"" ^ (Syntax.stringify_const c) ^ "\" cannot be applied"
        in
        raise @@ Error msg
      | VPair _ ->
        let msg = "Pairs cannot be applied" in
        raise @@ Error msg
      | VFun f -> f v2
    end
  | EPair (e1, e2) ->
    let* v1 = eval_expr env e1 in
    let* v2 = eval_expr env e2 in
    return @@ VPair (v1, v2)
  | EHandle (e, (ret, ops)) -> handle env ret ops @@ eval_expr env e

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
