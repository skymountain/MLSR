{

open Lexing
open Parser

let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <- {
    pos with pos_bol = lexbuf.lex_curr_pos;
             pos_lnum = pos.pos_lnum + 1;
  }

}


let int = '-'? ['0'-'9'] ['0'-'9']*

let digit = ['0'-'9']
let frac = '.' digit*
let exp = ['e' 'E'] ['-' '+']? digit+
let float = digit* frac? exp?

let id = ['a'-'z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*

let white = [' ' '\t']
let newline = '\n' | '\r' | "\r\n"

rule main = parse
  | white   { main lexbuf }
  | newline { next_line lexbuf; main lexbuf }
  | "int"   { INT }
  | "string" { STRING }
  | "bool"  { BOOL }
  | "float" { FLOAT }
  | "true"  { TRUE }
  | "false" { FALSE }
  | "fun"   { FUN }
  | "->"    { RIGHT_ARROW }
  | "let"   { LET }
  | "in"    { IN }
  | "effect" { EFFECT }
  | "handle" { HANDLE }
  | "with"   { WITH }
  | "return" { RETURN }
  | '='     { EQUAL }
  | '*'     { ASTERISK }
  | '('     { LEFT_PAREN }
  | ')'     { RIGHT_PAREN }
  | ','     { COMMA }
  | '\''    { SINGLE_QUOTE }
  | ':'     { COLON }
  | '.'     { DOT }
  | '|'     { VERTICAL_BAR }
  | '{'     { LEFT_BRACE }
  | '}'     { RIGHT_BRACE }
  | '+'     { PLUS }
  | '-'     { MINUS }
  | '/'     { SLASH }
  | '%'     { PERCENT }
  | '^'     { CARET }
  | '"'     { let buf = Buffer.create 17 in read_string buf lexbuf }
  | ';'     { SEMICOLON }
  | '<'     { LESS }
  | '>'     { GREAT }
  | ";;"    { DOUBLE_SEMICOLON }
  | "&&"    { DOUBLE_AMPERSAND }
  | "||"    { DOUBLE_VERTICAL_BAR }
  | "<="    { LESS_EQUAL }
  | ">="    { GREAT_EQUAL }
  | "<>"    { LESS_GREAT }
  | "=>"    { DOUBLE_RIGHT_ARROW }
  | int     { LITERAL_INT (int_of_string (Lexing.lexeme lexbuf)) }
  | float   { LITERAL_FLOAT (float_of_string (Lexing.lexeme lexbuf)) }
  | id      { ID (Lexing.lexeme lexbuf) }
  | _       { let msg = "Unexpected character: " ^ Lexing.lexeme lexbuf in
              raise (Syntax.Error msg) }
  | eof     { EOF }

and read_string buf = parse
  | '"'          { LITERAL_STRING (Buffer.contents buf) }
  | '\\' '\\'    { Buffer.add_char buf '\\'; read_string buf lexbuf }
  | '\\' '"'     { Buffer.add_char buf '"'; read_string buf lexbuf }
  | [^ '"' '\\'] { Buffer.add_string buf (Lexing.lexeme lexbuf);
                   read_string buf lexbuf }
  | eof          { raise (Syntax.Error "String is not terminated") }
