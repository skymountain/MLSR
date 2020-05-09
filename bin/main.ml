open Mlsr

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
  Repl.read_eval_print
    (Lexing.from_channel stdin) (Repl.env, Env.empty) (Repl.tyenv, Env.empty)
;;
