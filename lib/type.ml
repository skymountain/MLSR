module Tyvar = struct
  type t = int
  let compare = compare
end
;;

module TyvarMap = struct
  include Map.Make(Tyvar)
  let keys m = List.map fst @@ bindings m
end
;;

module TyvarSet = Set.Make(Tyvar)
;;

module OpMap = Map.Make(String)
;;

type bty =
  | TyInt
  | TyBool
  | TyStr
  | TyFloat
  | TyUnit
[@@deriving show]
;;

type ty =
  | TyBase of bty
  | TyVar of int
  | TyVarFixed of int
  | TyFun of ty * ty
  | TyProd of ty * ty
  | TySum of ty * ty
  | TyList of ty
[@@deriving show]
;;

type ty_scheme = TyvarSet.t * ty
;;

type ty_sig = TyvarSet.t * ty * ty
;;


let cur_tyvar_id = ref 0
;;

let incr_tyvar_id () =
  cur_tyvar_id := !cur_tyvar_id + 1
;;

let fresh_tyvar () =
  incr_tyvar_id ();
  TyVar !cur_tyvar_id
;;

let fresh_fixed_tyvar () =
  incr_tyvar_id ();
  TyVarFixed !cur_tyvar_id
;;

let tysc_of_ty ty = (TyvarSet.empty, ty)
;;

let rec ftv_ty = function
  | TyBase _ -> TyvarSet.empty
  | TyVar x | TyVarFixed x -> TyvarSet.singleton x
  | TyFun (t1, t2) | TyProd (t1, t2) | TySum (t1, t2) ->
    TyvarSet.union (ftv_ty t1) (ftv_ty t2)
  | TyList t -> ftv_ty t
;;

let rec fixed_ftv_ty = function
  | TyBase _ | TyVar _ -> TyvarSet.empty
  | TyVarFixed x -> TyvarSet.singleton x
  | TyFun (t1, t2) | TyProd (t1, t2) | TySum (t1, t2) ->
    TyvarSet.union (fixed_ftv_ty t1) (fixed_ftv_ty t2)
  | TyList t -> fixed_ftv_ty t
;;

let check_validity_of_tysc (tyvars, ty) =
  assert (TyvarSet.disjoint tyvars (fixed_ftv_ty ty))
;;

let check_validity_of_subst s =
  TyvarMap.iter
    (fun tyvar ty -> assert (not @@ TyvarSet.mem tyvar (ftv_ty ty)))
    s
;;

let _ftv_tysc f ((tyvars, ty) as tysc) =
  check_validity_of_tysc tysc;
  TyvarSet.diff (f ty) tyvars
;;

let _ftv_tyenv f tyenv =
  Env.fold (fun _ tysc tyvars ->
      TyvarSet.union (f tysc) tyvars)
    tyenv TyvarSet.empty
;;

let ftv_tysc = _ftv_tysc ftv_ty
;;

let ftv_tyenv = _ftv_tyenv ftv_tysc
;;

let ftv_openv openv =
  OpMap.fold
    (fun _ (tyvars, dom, codom) set ->
       let dom_codom = TyvarSet.union (ftv_ty dom) (ftv_ty codom) in
       TyvarSet.union set (TyvarSet.diff dom_codom tyvars))
    openv TyvarSet.empty
;;

let ftv_subst s =
  TyvarMap.fold (fun _ ty set ->
      TyvarSet.union set @@ ftv_ty ty)
    s TyvarSet.empty
;;

let closing tyenv ty =
  let fvs_ty = ftv_ty ty in
  let fvs_tyenv = ftv_tyenv tyenv in
  let ffvs_ty = fixed_ftv_ty ty in
  (TyvarSet.diff fvs_ty (TyvarSet.union ffvs_ty fvs_tyenv), ty)
;;

let rec subst_ty s ty = match ty with
  | TyVar x ->
    Option.fold ~none:ty ~some:(fun ty -> ty) @@ TyvarMap.find_opt x s
  | TyVarFixed x ->
    assert (not @@ TyvarMap.mem x s);
    ty
  | TyBase _ -> ty
  | TyFun (arg, ret) -> TyFun (subst_ty s arg, subst_ty s ret)
  | TyProd (fs, sn) -> TyProd (subst_ty s fs, subst_ty s sn)
  | TySum (l, r) -> TySum (subst_ty s l, subst_ty s r)
  | TyList t -> TyList (subst_ty s t)
;;

let subst_subst ~by ~target =
  let s = TyvarMap.map (fun ty -> subst_ty by ty) target in
  check_validity_of_subst s;
  s
;;

let subst_tyenv s tyenv =
  let dom =
    TyvarSet.of_list @@ TyvarMap.fold (fun x _ l -> x::l) s []
  in
  let codom =
    TyvarMap.fold
      (fun _ ty set -> TyvarSet.union (ftv_ty ty) set)
      s TyvarSet.empty
  in
  Env.map
    (fun (tyvars, ty) ->
       assert (TyvarSet.disjoint tyvars dom);
       assert (TyvarSet.disjoint tyvars codom);
       (tyvars, subst_ty s ty))
    tyenv
;;

let renaming_subst tyvars tyvar_gen =
  TyvarSet.fold
    (fun x s -> TyvarMap.add x (tyvar_gen ()) s)
    tyvars
    TyvarMap.empty
;;

let instantiate ((tyvars, ty) as tysc) =
  check_validity_of_tysc tysc;
  subst_ty (renaming_subst tyvars fresh_tyvar) ty
;;

let instantiate_ty_sig (tyvars, dom_ty, codom_ty) =
  let s = renaming_subst tyvars fresh_fixed_tyvar in
  (ftv_subst s, subst_ty s dom_ty, subst_ty s codom_ty)
;;

let string_of_bty = function
  | TyInt -> "int"
  | TyBool -> "bool"
  | TyStr -> "string"
  | TyFloat -> "float"
  | TyUnit -> "unit"
;;

let preference_of_ty_cnstr = function
  | TyVar _ | TyBase _ | TyVarFixed _ -> 0
  | TyList _ -> -1
  | TyProd _ -> -2
  | TySum _ -> -3
  | TyFun _ -> -4
;;


(* Wrap with paranthesises only when type constructors of subcompoents
   are assigned lower prefeference *)
let rec _string_of_ty bound_m free_m =
  let find x =
    match TyvarMap.find_opt x bound_m with
    | None -> TyvarMap.find x free_m
    | Some letter -> letter
  in
  let paren p s =
    let format : ('a->'b, unit, string) format = if p then "(%s)" else "%s" in
    Printf.sprintf format s
  in
  let self ty = _string_of_ty bound_m free_m ty in
  fun ty ->
    let p = preference_of_ty_cnstr ty in
    match ty with
    | TyVar x ->
      Printf.sprintf "'%s" @@ find x
    | TyVarFixed x -> Printf.sprintf "@%s" @@ find x
    | TyBase b -> string_of_bty b
    | TyFun (arg, ret) ->
      (* right-associative *)
      let arg_str = paren (preference_of_ty_cnstr arg <= p) (self arg) in
      let ret_str = paren (preference_of_ty_cnstr ret < p) (self ret) in
      Printf.sprintf "%s -> %s" arg_str ret_str
    | TyProd (f, s) ->
      (* left-associative *)
      let fst_str = paren (preference_of_ty_cnstr f < p) (self f) in
      let snd_str = paren (preference_of_ty_cnstr s <= p) (self s) in
      Printf.sprintf "%s * %s" fst_str snd_str
    | TySum (l, r) ->
      (* left-associative *)
      let left_str = paren (preference_of_ty_cnstr l < p) (self l) in
      let right_str = paren (preference_of_ty_cnstr r <= p) (self r) in
      Printf.sprintf "%s + %s" left_str right_str
    | TyList t ->
      let str = paren (preference_of_ty_cnstr t < p) (self t) in
      Printf.sprintf "%s list" @@ str
;;

let string_of_tysc =
  let n = 26 in
  let a = int_of_char 'a' in
  let letter idx =
    let rec iter buf idx =
      Buffer.add_char buf @@ char_of_int (a + (idx mod n));
      let next = idx - n in
      if next < 0 then Buffer.contents buf
      else iter buf next
    in
    iter (Buffer.create 3) idx
  in
  let make_tyvar_map tyvars alphabet_start_idx =
    fst @@
    TyvarSet.fold (fun x (m, cur) ->
        (TyvarMap.add x (letter cur) m, cur + 1))
      tyvars
      (TyvarMap.empty, alphabet_start_idx)
  in
  fun ((tyvars, ty) as tysc) ->
    check_validity_of_tysc tysc;
    let bound_map = make_tyvar_map tyvars 0 in
    let free_map = make_tyvar_map
        (TyvarSet.diff (ftv_ty ty) tyvars)
        (TyvarMap.cardinal bound_map)
    in
    _string_of_ty bound_map free_map ty
;;

let string_of_ty ty = string_of_tysc (TyvarSet.empty, ty)
;;

let string_of_subst s =
  List.rev @@
  TyvarMap.fold (fun x ty acc ->
      let str =
        Printf.sprintf "TyVar %s |-> %s" (string_of_int x) (show_ty ty)
      in
      str :: acc)
    s []
;;
