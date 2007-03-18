{
(* A lexer for Creol.

   This file has been generated from Creol.mly

   Ceol.mll is part of creolcomp written by

   Marcel Kyas <kyas@ifi.uio.no> with contributions from
   Olaf Owe and Einar Broch Johnsen

   Copyright (c) 2007

   The code in CreolParser.mly has been generated by the menhir parser
   generator.  In accordance with the Lesser General Public License,
   the generated parser as well as its source file are distributed
   under the terms of the GPL:

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.
   
   This program is distributed in the hope that it will be useful, but
   WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   General Public License for more details.
   
   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA
   02111-1307, USA. *)

open CreolParser
open Lexing

exception Reserved of string * int * string

let update_loc lexbuf =
  let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <-
      { pos with pos_lnum = pos.pos_lnum + 1; pos_bol = pos.pos_cnum }

let reserved lexbuf =
  let pos = lexbuf.lex_curr_p in
    let tok = Lexing.lexeme lexbuf in
      raise (Reserved (pos.pos_fname, pos.pos_lnum, tok))
}
let COMMENT = '/' '/' [ ^ '\n' ]*
let FLOAT = ['0'-'9']+'.'['0'-'9']+('e' ('+'|'-')? ['0'-'9']+)
let CID = [ 'A'-'Z' ][ 'a'-'z' 'A'-'Z' ]*
let ID =  [ 'a'-'z' ][ 'a'-'z' 'A'-'Z' '0'-'9' ]*
let STRING = '"' [^ '\n' '"' ]* '"'
rule token = parse
      [' ' '\t'] { token lexbuf }
    | COMMENT { token lexbuf }
    | "/*" { c_style_comment lexbuf }
    | '\n' { update_loc lexbuf; token lexbuf }
    | ":=" { ASSIGN }
    | "::" { reserved lexbuf }
    | '_' { reserved lexbuf }
    | ':' { COLON }
    | '?' { QUESTION }
    | '!' { BANG }
    | "@@" { reserved lexbuf }
    | '@' { AT }
    | '#' { reserved lexbuf }
    | "==" { EQEQ }
    | "<=" { LE }
    | ">=" { GE }
    | ">>" { reserved lexbuf }
    | "<<" { UPPER }
    | "<" { LT }
    | ">" { GT }
    | "/=" { NE }
    | '*' { TIMES }
    | '/' { DIV }
    | '+' { PLUS }
    | '-' { MINUS }
    | '=' { EQ }
    | ',' { COMMA }
    | ';' { SEMI }
    | ".." { reserved lexbuf }
    | '.' { DOT }
    | "[]" { BOX }
    | '[' { LBRACK }
    | ']' { RBRACK }
    | '(' { LPAREN }
    | ')' { RPAREN }
    | '{' { reserved lexbuf }
    | '}' { reserved lexbuf }
    | "<>" { reserved lexbuf }
    | "|||" { MERGE }
    | "||" { reserved lexbuf }
    | "|" { reserved lexbuf }
    | "and" { AND }
    | "await" { AWAIT }
    | "begin" { BEGIN }
    | "caller" { ID("caller") (* XXX: Should be special *) }
    | "class" { CLASS }
    | "contracts" { CONTRACTS }
    | "else" { ELSE }
    | "end" { END }
    | "false" { BOOL(false) }
    | "fi" { FI }
    | "iff" { IFF }
    | "if" { IF }
    | "implements" { IMPLEMENTS }
    | "inherits" { INHERITS }
    | "interface" { INTERFACE }
    | "inv" { reserved lexbuf }
    | "in" { IN }
    | "new" { NEW }
    | "nil" { NIL }
    | "null" { NULL }
    | "not" { NOT }
    | "op" { OP }
    | "or" { OR }
    | "out" { OUT }
    | "pre" { reserved lexbuf }
    | "post" { reserved lexbuf }
    | "skip" { SKIP }
    | "system" { reserved lexbuf }
    | "then" { THEN }
    | "this" { ID("this") (* XXX: Should be special, too. *) }
    | "true" { BOOL(true) }
    | "var" { VAR }
    | "wait" { WAIT }
    | "with" { WITH }
    | "xor" { XOR }
    | "Label" { reserved lexbuf }
    | "System" { reserved lexbuf }
    | FLOAT { FLOAT(float_of_string (Lexing.lexeme lexbuf)) }
    | ['0'-'9']+ { INT(int_of_string (Lexing.lexeme lexbuf)) }
    | CID { CID(Lexing.lexeme lexbuf) }
    | ID { ID(Lexing.lexeme lexbuf) }
    | STRING { let s = Lexing.lexeme lexbuf in STRING(String.sub s 1 ((String.length s) - 2)) }
    | eof { EOF }
and c_style_comment = parse
      "*/"	{ token lexbuf }
    | '\n' { update_loc lexbuf; c_style_comment lexbuf }
    | '*' { c_style_comment lexbuf }
    | [ ^ '\n' '*'] * { c_style_comment lexbuf }
