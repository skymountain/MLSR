exception Error of string
;;

module Id = struct
  type t = string
  [@@deriving show]
  let compare = String.compare
end
;;

module OpId = struct
  type t = int
  [@@deriving show]
  let compare = compare

  let fresh_op_id =
    let cur_op_id = ref 0 in
    fun () ->
      cur_op_id := !cur_op_id + 1;
      !cur_op_id
end
;;



type const =
  | CBool of bool
  | CInt of int
  | CStr of string
  | CFloat of float
[@@deriving show]
;;

type return_clause = Id.t * expr
and op_clause = {
  op_name: Id.t;
  op_arg_var: Id.t;
  op_cont_var: Id.t;
  op_body: expr
}
and handler = return_clause * op_clause list
and expr =
  | EId of Id.t
  | EConst of const
  | EFun of Id.t * expr
  | EApp of expr * expr
  | EPair of expr * expr
  | EHandle of expr * handler
[@@deriving show]
;;

type decl =
  | DExpr of expr
  | DLet of Id.t * expr
  | DEff of Id.t * Type.ty_sig
;;

type value =
  | VConst of const
  | VFun of cont
  | VPair of value * value
and res =
  | RVal of value
  | RCont of OpId.t * value * cont
  (* | RCont of cont *)
and cont = value -> res
;;

(* type cont = { *)
(*   cont_effect: Id.t; *)
(*   cont_arg: value; *)
(*   cont_cont: value -> value; *)
(* } *)
;;



let stringify_const = function
  | CBool true -> "true"
  | CBool false -> "false"
  | CInt i -> string_of_int i
  | CStr s -> "\"" ^ s ^ "\""
  | CFloat f -> string_of_float f
;;

let rec stringify_value = function
  | VConst c -> stringify_const c
  | VFun _ -> "<fun>"
  | VPair (v1, v2) ->
    "(" ^ stringify_value v1 ^ ", " ^ stringify_value v2 ^ ")"
;;
