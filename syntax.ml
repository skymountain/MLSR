exception Error of string
;;

let err s = raise @@ Error s
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
  | CUnit
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
  | ELet of Id.t * expr * expr
  | ELetRec of Id.t * Id.t * expr * expr
  | EHandle of expr * handler
  | EPair of expr * expr
  | EInl of expr
  | EInr of expr
  | EList of expr list
  | EMatch of expr * match_clause
and match_clause =
  | MPair of Id.t * Id.t * expr
  | MInj of Id.t * expr * Id.t * expr
  | MList of expr * Id.t * Id.t * expr
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
  | VInl of value
  | VInr of value
  | VNil
  | VCons of value * value
and res =
  | RVal of value
  | RCont of OpId.t * value * cont
and cont = value -> res
;;

let string_of_const = function
  | CBool true -> "true"
  | CBool false -> "false"
  | CInt i -> string_of_int i
  | CStr s -> "\"" ^ s ^ "\""
  | CFloat f -> string_of_float f
  | CUnit -> "()"
;;

let rec string_of_value = function
  | VConst c -> string_of_const c
  | VFun _ -> "<fun>"
  | VPair (v1, v2) ->
    "(" ^ string_of_value v1 ^ ", " ^ string_of_value v2 ^ ")"
  | VInl v -> Printf.sprintf "inl %s" @@ string_of_value v
  | VInr v -> Printf.sprintf "inr %s" @@ string_of_value v
  | VNil -> "[]"
  | VCons (v1, v2) ->
    Printf.sprintf "(%s) :: %s" (string_of_value v1) (string_of_value v2)
;;
