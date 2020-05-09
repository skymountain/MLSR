let cur_op_id = ref 0
;;

let fresh_op () =
  cur_op_id := !cur_op_id + 1;
  !cur_op_id
;;
