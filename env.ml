module Env = Map.Make(String)
;;

type 'a t = 'a Env.t
;;

let empty = Env.empty
;;

let find = Env.find
;;

let find_opt = Env.find_opt
;;

let add = Env.add
;;

let fold = Env.fold
;;
