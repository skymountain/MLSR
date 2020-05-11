# MLSR  #

MLSR is an interpreter of a functional programming language that supports
let-polymorphism, Hindley-Milner type inference, and polymorphic algebraic
effects and handlers with *signature restriction*, which is a methodology to
restrict type interfaces of algebraic effects for type-safe handling of
polymorphic effects.  MLSR is a polymorphic effectful call-by-value (CBV)
language, but it does not need to enforce value restriction&mdash;which is
another approach to reconciling polymorphism and computational effects in CBV
languages (or fragments) and is adopted by other many ML-like languages
including OCaml, Standard ML, Koka, etc.&mdash;thanks to the signature
restriction.  The details including formalization and metatheory are found at:

* Taro Sekiyama Tsukada Takeshi, Atsushi Igarashi: Signature restriction for
  polymorphic algebraic effects.  Conditionally accepted at ICFP 2020.
  https://arxiv.org/abs/2003.08138

This artifact expects all effect operations follow the signature restriction (as
in Sections 4 & 5 of our paper), and does _not_ support the type-and-effect
system to reconcile safe and unsafe effects (i.e., operations that do and do not
follow the signature restriction) in a type-safe manner (Section 6).


## Getting started

### Requirements

* `ocaml` (>= 4.10)
* `opam` (>= 2.0)
* `dune` (>= 2.5)
* `menhir`
* `ppx_deriving` (>= 4.4.1)

### Building from source code

```bash
$ dune build
$ ./_build/install/default/bin/mlsr
```

### Installation via opam

```bash
$ opam install .
$ mlsr
```

### Tips

#### User-firendly interface

Our interpreter does not support user-friendly line editing and input history
search directly, but one can make use of such features via
[rlwrap](https://github.com/hanslub42/rlwrap).

```bash
$ rlwrap mlsr
```

#### Disabling signature restriction

Checking the signature restriction can be disabled by specifying the option
`--disable-signature-restriction` in starting up the interpreter.  Note that
this option makes type-unsafe programs well typed badly; see
[below](#disabling-the-signature-restriction-unsafe) for detail.

```bash
$ mlsr --disable-signature-restriction
```

#### Running tests

The following command will run all of the tests in the directory `test`.

```bash
$ dune runtest
```

## Syntax

The syntax of MLSR is given by the following BNF.  We write `A*` for (possibly
empty) lists of elements in the class `A`.  (For example, `x*` represent
sequences of variables.)  `\mid` is replaced by `|` in program code.  Texts
surrounded by `(*` and `*)` are just comments.  We may emphasize nonterminal
symbols by wrapping them with `__` (e.g., `__integers__`for integer literals).

```
Term variables ::= x, y, z, f, g, k, op, etc.
Type variables ::= 'a, 'b, 'c, etc.

Top-level ::= ED ;; | VD ;; | e ;;

Effect declarations ED ::= effect op : 'a* . T1 => T2

Types T ::= 'a         (* Type variables *)
          | BT         (* Base types *)
          | T1 -> T2   (* Function types *)
          | T1 * T2    (* Product types *)
          | T1 + T2    (* Sum types *)
          | T list     (* List types *)

Base Types BT ::= bool | int | string | float | unit

Variable declarations VD ::= let x y* = e | let rec f x y* = e

Expressions e ::= x
                | c
                | fun x y* -> e | e1 e2 |
                | let x y* = e1 in e2 | let rec f x y* = e1 in e2
                | ( e1 , e2 ) | inl e | inr e | [ e1 ; ... ; en ]
                | match e with p
                | if e1 then e2 else e3 | e1 ; e2
                | handle e with { return x -> x ( \mid o )* }

Constants c ::= () | true | false | __integers__ | __floating-point numbers__ | __strings__
               | __primitive operations__   (* see the examples below for detail *)

Pattern clauses p ::= ( x , y ) -> e
                  | inl x -> e1 \mid inr y -> e2
                  | [ ] -> e1 \mid x :: y -> e2

Operation clauses o ::= op x k -> e
```

## Examples

The following examples can also be found at `example.mlsr` in the root
directory.

### Functions

```ocaml
# let plus42 = fun x -> x + 42;;
val plus42 : int -> int = <fun>

# plus42 1;;
val - : int = 43

# let plus42 x = x + 42;;
val plus42 : int -> int = <fun>

# plus42 3;;
val - : int = 45
```

```ocaml
# let rec fact n = if n = 0 then 1 else n * fact (n - 1);;
val fact : int -> int = <fun>

# fact 10;;
val - : int = 3628800
```

### Let-polymorphism

```ocaml
# let id x = x;;
val id : 'a -> 'a = <fun>

# id true;;
val - : bool = true

# id 0;;
val - : int = 0

# let f x = x in (f true, f 0);;
val - : bool * int = (true, 0)
```

MLSR is free from the value restriction.
``` ocaml
# let f = id id in (f "foo", f 1);;
val - : string * int = ("foo", 1)
```
The value restriction does not accept the expression above because
`f` could not have a polymorphic type under it.

### Pairs, injections, and lists

```ocaml
# let x = (1, "foo");;
val x : int * string = (1, "foo")

# match x with (y, z) -> y + str_len z;;  (* str_len returns the length of a string *)
val - : int = 4
```

```ocaml
# let f x = match x with inl x -> x = 0 | inr y -> y;;
val f : int + bool -> bool = <fun>

# f (inl 5);;
val - : bool = false

# f (inr true);;
val - : bool = true
```

```ocaml
# let rec length x = match x with [] -> 0 | y::ys -> 1 + length ys;;
val length : 'a list -> int = <fun>

# length [true];;
val - : int = 1

# length [1;2;3];;
val - : int = 3
```

### Algebraic effect handlers

To invoke effects in MLSR, we first need to declare effect operations.

```ocaml
(* Declares effect operation select,
   which can be referred to as a variable of polymorphic type 'a list -> 'a *)

# effect select : 'a . 'a list => 'a;;
effect select : 'a list -> 'a defined

# select;;
val - : 'a list -> 'a = <fun>

(* The following expression is well typed
   but its evaluation terminates at the "Uncaught continuation" error as expected *)

# select [1;2;3];;
Run-time error: Uncaught continuation
```

Effect operations are handled by `handle`&ndash;`with` expressions.  For example, the
following code handles `select` and returns the head of a given list as a result
of the call to `select`.

```ocaml
# handle 42 + select [1;2;3] with {
    return x -> x
  | select x k -> (match x with [] -> -1 | y::ys -> k y)
  };;
val - : int = 43
```

The return clause handles the evaluation result of the handled expression.

```ocaml
# handle 42 with { return x -> x * 10 };;
val - : int = 420
```

Continuations given to the operation clause are wrapped by the handler installed
at the `handle`&ndash;`with` expression.  For example, in the following code, the
continuation `k` is invoked with the head of the argument list (i.e., `1`) and
then the continuation will perform the remaining computation (`42 + 1`) and pass
the result to the return clause.  Thus, the final result is `430`.

```ocaml
# handle 42 + select [1;2;3] with {
    return x -> x * 10
  | select x k -> (match x with [] -> -1 | y::ys -> k y)
  };;
val - : int = 430
```

We also can collect all of the values computed with elements in the list.

```ocaml
# let rec map f l = match l with [] -> [] | x::xs -> (f x) :: (map f xs);;
val map : ('a -> 'b) -> 'a list -> 'b list = <fun>

# let rec append l m = match l with [] -> m | x::xs -> x :: (append xs m);;
val append : 'a list -> 'a list -> 'a list = <fun>

# let rec flatten l = match l with [] -> [] | x::xs -> append x (flatten xs);;
val flatten : 'a list list -> 'a list = <fun>

# handle 42 + select [1;2;3] with { return x -> [x] | select x k -> flatten (map k x) };;
val - : int list = [43; 44; 45]
```

In the operation clause, `x` is assigned type `'a list` where `'a` is a locally
assigned type variable and must not be escaped from the operation clause.

```ocaml
# handle 42 with { return x -> x | select x k -> x };;
Typing error: Type variables bound in an operation clause cannot be escaped
```

Handlers can deal with two or more operation clauses.
```ocaml
# effect fail : 'a. unit => 'a;;
effect fail : unit -> 'a defined

# let f xs ys = handle
      let x = select xs in
      let y = select ys in
      if y = 0 then fail () else x / y
    with {
      return z -> [z]
    | select x k -> flatten (map k x)
    | fail x k -> []
    };;
val f : int list -> int list -> int list = <fun>

# f [42; 12; 6] [3;2;0];;
val - : int list = [14; 21; 4; 6; 2; 3]
```

### Signature restriction

By default MLSR checks if a declared effect follows the signature restriction
for ensuring type safety.  For example, the following `get_id`, which is an
example used in [our paper](https://arxiv.org/abs/2003.08138), is rejected
because it invalidates the signature restriction.
```ocaml
# effect get_id : 'a. unit => 'a -> 'a;;
Typing error: The type signature does not follow the signature restriction on the codomain type
```

In general, the signature restriction requires quantified type variables (`'a`
above) not to appear (1) at a non-strictly positive position in the domain type
(`unit` above) nor (2) at a negative position in the codomain type (`'a -> 'a`
above).  See [the paper](https://arxiv.org/abs/2003.08138) for detail.

#### Disabling the signature restriction (unsafe)

We can disable the signature restriction by giving option
`--disable-signature-restriction` to `mlsr`. Then, we can find the (ab)use of
`get_id` gives rise to an undesired run-time error (as expected).

```bash
$ mlsr --disable-signature-restriction
```

```ocaml
# effect get_id : 'a. unit => 'a -> 'a;;
effect get_id is defined

# handle let f = get_id () in f 2; (f true) && false with {
    return x -> x
  | get_id x k -> k (fun y -> k (fun z -> y); y)
  };;
Run-time error: Operator "&&" can be applied only to Booleans
```

Here, `f true` is expected to return a Boolean, but at run-time
it may return integer `2` for the lack of any restriction.

### Complete list of primitive functions

```ocaml
(* Integers *)
# 1 + 2;;
# 6 - 4;;
# 4 * 5;;
# 7 / 2;;    (* n / 0 will cause a run-time error *)
# 11 % 3;;   (* n % 0 will cause a run-time error *)

(* Floating-point numbers *)
# 1.1 +. 2.4;;
# 5.8 -. 1.7;;
# 4.2 *. 2.;;
# 4.5 /. 1.5;;

(* Booleans *)
# true && false;;
# false || true;;
# if 1 = 2 then 3 else 4;;

(* Strings *)
# "foo" ^ "bar";;
# str_len "foo";;
# str_sub "foobar" 1 3;;  (* invalid arguments will cause a run-time error *)

(* Lists *)
# [];;
# 1 :: 2 :: [];;
# [1.; 2.; 3.];;

(* Polymorphic comparison; comparing functions will fail  *)
# 1 = 2;;
# 1 <> 2;;
# 1.1 > 1.1;;
# 1.1 >= 1.1;;
# "foo" < "bar";;
# "foo" <= "bar";;

(* Sequential composition *)
# 1; true;;
```
