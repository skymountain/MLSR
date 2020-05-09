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

type mono_ty =
  | TyBase of bty
  | TyVar of int
  | TyVarFixed of int
  | TyFun of mono_ty * mono_ty
  | TyProd of mono_ty * mono_ty
  | TySum of mono_ty * mono_ty
  | TyList of mono_ty
[@@deriving show]
;;

type ty_scheme = TyvarSet.t * mono_ty
;;

type ty_sig = TyvarSet.t * mono_ty * mono_ty
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

let tyscheme_of_mono ty = (TyvarSet.empty, ty)
;;

let rec free_tyvars = function
  | TyBase _ -> TyvarSet.empty
  | TyVar x | TyVarFixed x -> TyvarSet.singleton x
  | TyFun (t1, t2) | TyProd (t1, t2) | TySum (t1, t2) ->
    TyvarSet.union (free_tyvars t1) (free_tyvars t2)
  | TyList t -> free_tyvars t
;;

let rec free_fixed_tyvars = function
  | TyBase _ | TyVar _ -> TyvarSet.empty
  | TyVarFixed x -> TyvarSet.singleton x
  | TyFun (t1, t2) | TyProd (t1, t2) | TySum (t1, t2) ->
    TyvarSet.union (free_fixed_tyvars t1) (free_fixed_tyvars t2)
  | TyList t -> free_fixed_tyvars t
;;

let check_validity_of_ty_scheme (tyvars, ty) =
  assert (TyvarSet.disjoint tyvars (free_fixed_tyvars ty))
;;

let check_validity_of_subst s =
  TyvarMap.iter
    (fun tyvar ty -> assert (not @@ TyvarSet.mem tyvar (free_tyvars ty)))
    s
;;

let _free_tyvars_in_ty_scheme f ((tyvars, ty) as ty_scheme) =
  check_validity_of_ty_scheme ty_scheme;
  TyvarSet.diff (f ty) tyvars
;;

let _free_tyvars_in_tyenv f tyenv =
  Env.fold (fun _ ty_scheme tyvars ->
      TyvarSet.union (f ty_scheme) tyvars)
    tyenv TyvarSet.empty
;;

let free_tyvars_in_ty_scheme =
  _free_tyvars_in_ty_scheme free_tyvars
;;

let free_tyvars_in_tyenv =
  _free_tyvars_in_tyenv free_tyvars_in_ty_scheme
;;

let free_fixed_tyvars_in_ty_scheme =
  _free_tyvars_in_ty_scheme free_fixed_tyvars
;;

let free_fixed_tyvars_in_tyenv =
  _free_tyvars_in_tyenv free_fixed_tyvars_in_ty_scheme
;;

let free_tyvars_in_openv openv =
  OpMap.fold
    (fun _ (tyvars, dom, codom) set ->
       let dom_codom = TyvarSet.union (free_tyvars dom) (free_tyvars codom) in
       TyvarSet.union set (TyvarSet.diff dom_codom tyvars))
    openv TyvarSet.empty
;;

let free_tyvars_in_subst s =
  TyvarMap.fold (fun _ ty set ->
      TyvarSet.union set @@ free_tyvars ty)
    s TyvarSet.empty
;;

let closing tyenv ty =
  let fvs_ty = free_tyvars ty in
  let fvs_tyenv = free_tyvars_in_tyenv tyenv in
  let ffvs_ty = free_fixed_tyvars ty in
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
      (fun _ ty set -> TyvarSet.union (free_tyvars ty) set)
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

let instantiate ((tyvars, ty) as ty_scheme) =
  check_validity_of_ty_scheme ty_scheme;
  subst_ty (renaming_subst tyvars fresh_tyvar) ty
;;

let instantiate_ty_sig (tyvars, dom_ty, codom_ty) =
  let s = renaming_subst tyvars fresh_fixed_tyvar in
  (free_tyvars_in_subst s, subst_ty s dom_ty, subst_ty s codom_ty)
;;

let stringify_bty = function
  | TyInt -> "int"
  | TyBool -> "bool"
  | TyStr -> "string"
  | TyFloat -> "float"
  | TyUnit -> "unit"
;;

let rec stringify_ty bound_m free_m =
  let find x =
    match TyvarMap.find_opt x bound_m with
    | None -> TyvarMap.find x free_m
    | Some letter -> letter
  in
  let self ty = stringify_ty bound_m free_m ty in
  function
  | TyVar x ->
    Printf.sprintf "'%s" @@ find x
  | TyVarFixed x -> Printf.sprintf "@%s" @@ find x
  | TyBase b -> stringify_bty b
  | TyFun (arg, ret) ->
    Printf.sprintf "(%s) -> (%s)" (self arg) (self ret)
  | TyProd (f, s) ->
    Printf.sprintf "(%s) * (%s)" (self f) (self s)
  | TySum (l, r) ->
    Printf.sprintf "(%s) + (%s)" (self l) (self r)
  | TyList t -> Printf.sprintf "(%s) list" @@ self t
;;

let stringify_ty_scheme =
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
  fun ((tyvars, ty) as ty_scheme) ->
    check_validity_of_ty_scheme ty_scheme;
    let bound_map = make_tyvar_map tyvars 0 in
    let free_map = make_tyvar_map
        (TyvarSet.diff (free_tyvars ty) tyvars)
        (TyvarMap.cardinal bound_map)
    in
    stringify_ty bound_map free_map ty
;;

let stringify_mono_ty ty = stringify_ty_scheme (TyvarSet.empty, ty)
;;

let stringify_subst s =
  List.rev @@
  TyvarMap.fold (fun x ty acc ->
      let str =
        Printf.sprintf "TyVar %s |-> %s" (string_of_int x) (show_mono_ty ty)
      in
      str :: acc)
    s []
;;
