open OUnit2
open Option
module M = Mlsr

let rec last = function
  | [] -> raise @@ Invalid_argument "last"
  | x::[] -> x
  | _::xs -> last xs
;;

let parse_decl = M.Parser.main M.Lexer.main
;;

let parse_decls =
  let rec iter lexbuf = match parse_decl lexbuf with
    | Some d -> d :: (iter lexbuf)
    | None -> []
  in
  fun s -> iter @@ Lexing.from_string s
;;

let process_decls f env ds =
  let _, res =
    List.fold_left
      (fun (env, res) d ->
         let env', r = f env d in
         (env', r :: res))
      (env, []) ds
  in
  List.rev res
;;

let eval_decls = process_decls M.Eval.eval_decl
;;

let type_decls = process_decls M.Typing.type_decl
;;

let env = (M.Repl.env, M.Env.empty)
;;

let tyenv = (M.Repl.tyenv, M.Env.empty)
;;

let test (msg, expr, expected_res, expected_ty) =
  msg >:: (fun _ ->
      let ds = parse_decls @@ expr ^ ";;" in

      let real_ty = last @@ type_decls tyenv ds in
      assert_equal expected_ty (M.Type.string_of_tysc real_ty);

      let real_res = last @@ eval_decls env ds in
      assert_equal true (is_some real_res);
      assert_equal expected_res (M.Syntax.string_of_value @@ get real_res);
      ()
    )
;;

let test_ty_failure (msg, expr) =
  msg >:: (fun _ ->
      let ds = parse_decls @@ expr ^ ";;" in
      try
        ignore @@ type_decls tyenv ds;
        assert_failure
          "Expected a typing error happens but no exception was raised"
      with
      | M.Typing.Error _ -> ()
    )
;;

let test_syntax_failure (msg, expr) =
  msg >:: (fun _ ->
      try
        ignore @@ parse_decls @@ expr ^ ";;";
        assert_failure
          "Expected a sytnax error happens but no exception was raised"
      with
      | M.Syntax.Error _ -> ()
    )
;;

let test_cont_failure (msg, expr) =
  msg >:: (fun _ ->
      let ds = parse_decls @@ expr ^ ";;" in
      ignore @@ type_decls tyenv ds;
      assert_raises (M.Eval.Error "Uncaught continuation")
        (fun () -> eval_decls env ds);
      ()
    )
;;


(* Test spec: lists of ("name", "program", "evaluation result", "type") *)

let function_tests = "functions" >::: List.map test [
    ("id",
     "fun x -> x",
     "<fun>",
     "'a -> 'a");
    ("let-id",
     "let id = fun x -> x",
     "<fun>",
     "'a -> 'a");
    ("id (int, bool)",
     "let id = fun x -> x;; (id 1, id true)",
     "(1, true)",
     "int * bool");
    ("K",
     "fun x y -> x",
     "<fun>",
     "'a -> 'b -> 'a");
    ("S",
     "fun x y z -> x z (y z)",
     "<fun>",
     "('a -> 'b -> 'c) -> ('a -> 'b) -> 'a -> 'c");
    ("id2",
     "(fun x -> x) (fun x -> x)",
     "<fun>",
     "'a -> 'a");
    ("succ",
     "fun x -> x + 1",
     "<fun>",
     "int -> int");
    ("succ5",
     "let f x = let rec g _ = x + 1 in g 2 in f 5",
     "6",
     "int");
    ("fact",
     "let rec fact n = if n = 0 then 1 else n * fact (n - 1) in fact 10",
     "3628800",
     "int");
    ("map",
     "let rec map f l = match l with [] -> [] | x::xs -> (f x) :: (map f xs);; \
      let succ x = x + 1;; \
      let not b = if b then false else true;; \
      (map succ [1;2], map not [true; false])",
     "([2; 3], [false; true])",
     "int list * bool list");
  ]
;;

let pair_tests = "paris" >::: List.map test [
    ("pair1",
     "(1+1, true)",
     "(2, true)",
     "int * bool");
    ("pair-left",
     "((1, true), 0.)",
     "((1, true), 0.)",
     "int * bool * float");
    ("pair-right",
     "(1, (true, 0.))",
     "(1, (true, 0.))",
     "int * (bool * float)");
    ("pair-apply",
     "let f x = match x with (x, y) -> x y",
     "<fun>",
     "('a -> 'b) * 'a -> 'b");
    ("pair-match",
     "let f x = match x with (x, y) -> x y;; \
      f ((fun x -> x), 1)",
     "1", "int");
  ]
;;

let inj_tests = "injections" >::: List.map test [
    ("inl",
     "inl (1+1)",
     "inl 2",
     "int + 'a");
    ("inr",
     "inr (fun x -> x)",
     "inr <fun>",
     "'b + ('a -> 'a)");
    ("inj-match",
     "let f x = match x with inl x -> x * 10 | inr y -> y true",
     "<fun>",
     "int + (bool -> int) -> int");
  ]
;;

let list_tests = "lists" >::: List.map test [
    ("empty list",
     "[]",
     "[]",
     "'a list");
    ("cons int",
     "1 :: []",
     "[1]",
     "int list");
    ("cons id",
     "let id x = x;; [id;id]",
     "[<fun>; <fun>]",
     "('a -> 'a) list");
    ("list-match",
     "let rec f x = match x with [] -> \"nil\" | x :: xs -> x ^ (f xs);; \
      f [\"a\"; \"b\"; \"c\"]",
     "\"abcnil\"",
     "string");
  ]
;;

let primitive_tests = "primitive functions" >::: List.map test [
    (* integers *)
    "+", "1 + 2", "3", "int";
    "-", "6 - 4", "2", "int";
    "*", "4 * 5", "20", "int";
    "-", "7 / 2 ", "3", "int";
    "%", "11 % 3", "2", "int";

    (* floats *)
    "+.", "1.1 +. 2.4", "3.5", "float";
    "-.", "5.8 -. 1.7", "4.1", "float";
    "*.", "4.2 *. 2.", "8.4", "float";
    "/.", "4.5 /. 1.5 ", "3.", "float";

    (* Booleans *)
    "&&", "true && false", "false", "bool";
    "||", "false || true", "true", "bool";
    "if", "if 1 = 2 then 3 else 4", "4", "int";

    (* strings *)
    "^", "\"foo\" ^ \"bar\"", "\"foobar\"", "string";
    "str_len", "str_len \"foo\"", "3", "int";
    "str_sub", "str_sub \"foobar\" 1 3", "\"oob\"", "string";

    (* lists *)
    "[]", "[]", "[]", "'a list";
    "::", "1 :: 2 :: []", "[1; 2]", "int list";
    "list lit", "[1.; 2.; 3.]", "[1.; 2.; 3.]", "float list";

    (* comparison *)
    "=", "1 = 2", "false", "bool";
    "<>", "1 <> 2", "true", "bool";
    ">", "1.1 > 1.1", "false", "bool";
    ">=", "1.1 >= 1.1", "true", "bool";
    "<", "\"foo\" < \"bar\"", "false", "bool";
    "<=", "\"foo\" <= \"bar\"", "false", "bool";

    (* sequential composition *)
    ";", "1; (fun x -> x)", "<fun>", "'a -> 'a";
    "fun;", "fun x -> x; x", "<fun>", "'a -> 'a";
  ]
;;

let effect_tests = "effects & handlers" >::: List.map test [
    ("fail",
     "effect fail : 'a . unit => 'a;; fail",
     "<fun>",
     "unit -> 'a");
    ("fail-handle",
     "effect fail : 'a . unit => 'a;; \
      handle fail () with { return x -> 0 | fail x k -> 1 }",
     "1", "int");
    ("select",
     "effect select : 'a . 'a list => 'a;; select",
     "<fun>",
     "'a list -> 'a");
    ("multiple bounded type varaibles",
     "effect op : 'a 'b . 'a * 'b => 'a + 'b;; op",
     "<fun>",
     "'a * 'b -> 'a + 'b");
    ("parse",
     "effect parse : 'a . string -> (('a * string) + unit) => 'a;; parse",
     "<fun>",
     "(string -> 'a * string + unit) -> 'a");
    ("neg-in-dom",
     "effect op : 'a . (unit -> 'a) -> unit => unit;; op",
     "<fun>",
     "((unit -> 'a) -> unit) -> unit");

    ("select-handle",
     "effect select : 'a . 'a list => 'a;; \
      handle 1 - select [1; 2; 3] with { \
        return x -> inr (x = 0) \
      | select x k -> match x with [] -> inl () | x :: _ -> k x \
      }",
     "inr true", "unit + bool");

    ("fail-select",
     "effect select : 'a . 'a list => 'a;; \
      effect fail : 'a . unit => 'a;; \
      let rec map f l = match l with [] -> [] | x::xs -> (f x) :: (map f xs);; \
      let rec append l m = match l with [] -> m | x::xs -> x :: (append xs m);; \
      let rec flatten l = match l with [] -> [] | x::xs -> append x (flatten xs);; \
      handle let x = select [10;20;30] in \
             let y = select [5;0;2] in \
             if y = 0 then fail () else x / y \
      with { \
        return x -> [x] \
      | fail x k -> [] \
      | select x k -> flatten (map k x) \
      }",
     "[2; 5; 4; 10; 6; 15]", "int list");

    ("fail-select-nested",
     "effect select : 'a . 'a list => 'a;; \
      effect fail : 'a . unit => 'a;; \
      let rec map f l = match l with [] -> [] | x::xs -> (f x) :: (map f xs);; \
      let rec append l m = match l with [] -> m | x::xs -> x :: (append xs m);; \
      let rec flatten l = match l with [] -> [] | x::xs -> append x (flatten xs);; \
      handle handle let x = select [10;20;30] in \
             let y = select [5;0;2] in \
             if y = 0 then fail () else x / y \
      with { return x -> [x] | fail x k -> [] } \
      with { return x -> x | select x k -> flatten (map k x) }",
     "[2; 5; 4; 10; 6; 15]", "int list");

    ("select-fail-nested",
     "effect select : 'a . 'a list => 'a;; \
      effect fail : 'a . unit => 'a;; \
      let rec map f l = match l with [] -> [] | x::xs -> (f x) :: (map f xs);; \
      let rec append l m = match l with [] -> m | x::xs -> x :: (append xs m);; \
      let rec flatten l = match l with [] -> [] | x::xs -> append x (flatten xs);; \
      handle handle let x = select [10;20;30] in \
             let y = select [5;0;2] in \
             if y = 0 then fail () else x / y \
      with { return x -> [x] | select x k -> flatten (map k x) } \
      with { return x -> x | fail x k -> [] }",
     "[]", "int list");
  ]
;;

let effect_ty_fail_tests = "effects & handlers (typing failure)" >:::
  List.map test_ty_failure [
    ("get_id",
     "effect get_id : 'a . unit => 'a -> 'a");
    ("SR-dom",
     "effect op : 'a . ('a -> unit) -> unit => unit");
    ("SR-codom",
     "effect op : 'a . unit => 'a -> unit");
    ("Local type variable escaping 1",
     "effect op : 'a . 'a => 'a;; \
      handle 42 with { return x -> x | op x k -> x }");
    ("Local type variable escaping 2",
     "effect op : 'a . 'a => 'a;; \
      handle 42 with { return x -> x | op x k -> k }");
  ]
;;

let effect_syntax_fail_tests = "effects & handlers (sytnax failure)" >:::
  List.map test_syntax_failure [
    ("SR-not-bound 1",
     "effect op : 'a => 'a");
    ("SR-not-bound 2",
     "effect op : 'a . 'a * 'b => 'a");
  ]
;;

let effect_cont_fail_tests = "effects & handlers (continuation failure)" >:::
  List.map test_cont_failure [
    ("cont 1", "effect op : unit => unit;; op ()");
    ("cont 2", "effect op : 'a . 'a => 'a;; op 1");
    ("cont 3",
     "effect op : 'a . 'a => 'a;; \
      (handle (fun x y -> op (x+y)) 1 with { return x -> x | op x k -> k x }) 2");
  ]
;;



let main () =
  run_test_tt_main @@ test_list [
    function_tests;
    pair_tests;
    inj_tests;
    list_tests;
    primitive_tests;
    effect_tests;
    effect_ty_fail_tests;
    effect_syntax_fail_tests;
    effect_cont_fail_tests;
  ]
;;

let _ = main ()
;;
