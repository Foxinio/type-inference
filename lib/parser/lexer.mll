(** OCamllex generated lexer *)

{
open Core

let report_error_lex (lexbuf : Lexing.lexbuf) fmt =
  Utils.report_error_pp lexbuf.lex_start_p lexbuf.lex_curr_p fmt

let kw_map =
  let open YaccParser in
  [ "else",   KW_ELSE
  ; "end",    KW_END
  ; "false",  KW_FALSE
  ; "fix",    KW_FIX
  ; "fn",     KW_FN
  ; "fst",    KW_FST
  ; "if",     KW_IF
  ; "in",     KW_IN
  ; "let",    KW_LET
  ; "match",  KW_MATCH
  ; "rec",    KW_REC
  ; "snd",    KW_SND
  ; "then",   KW_THEN
  ; "true",   KW_TRUE
  ; "with",   KW_WITH
  ; "type",   KW_TYPE
  ; "begin",  KW_BEGIN
  ; "bool",   TYP_KW_BOOL
  ; "int",    TYP_KW_INT
  ; "unit",   TYP_KW_UNIT
  ] |> List.to_seq |> Hashtbl.of_seq

let tokenize_ident str =
  match Hashtbl.find_opt kw_map str with
  | Some tok -> tok
  | None     -> YaccParser.LID str

let tokenize_number lexbuf str =
  match int_of_string_opt str with
  | Some n -> YaccParser.NUM n
  | None   ->
    report_error_lex lexbuf
      "invalid numeric literal"
}

let whitespace = ['\011'-'\r' '\t' ' ']
let digit      = ['0'-'9']
let lvar_start = ['a'-'z' '_']
let uvar_start = ['A'-'Z']
let var_char   = lvar_start | uvar_start | digit | '\''

rule token = parse
    whitespace+ { token lexbuf }
  | '\n' { Lexing.new_line lexbuf; token lexbuf }
  | "(*" { block_comment 1 lexbuf }
  | "//" { skip_line lexbuf; token lexbuf }
  | "("  { YaccParser.BR_OPN    }
  | ")"  { YaccParser.BR_CLS    }
  | "=>" { YaccParser.ARROW2    }
  | "->" { YaccParser.ARROW1    }
  | "|"  { YaccParser.BAR       }
  | ","  { YaccParser.COMMA     }
  | "="  { YaccParser.EQ        }
  | ";"  { YaccParser.SEMICOLON }
  | "*"  { YaccParser.TYP_STAR  }
  | ":"  { YaccParser.TYP_COLON }
  | '\'' (_ as x) '\''        { YaccParser.NUM (Char.code x) }
  | lvar_start var_char* as x { tokenize_ident x }
  | uvar_start var_char* as x { YaccParser.UID x }
  | '\'' var_char*       as x { YaccParser.AID x }
  | digit var_char*      as x { tokenize_number lexbuf x }
  | eof    { YaccParser.EOF }
  | _ as x {
      report_error_lex lexbuf
        "invalid character in input ('%s')"
        (Char.escaped x)
    }

and block_comment depth = parse
    '\n' { Lexing.new_line lexbuf; block_comment depth lexbuf }
  | "(*" { block_comment (depth+1) lexbuf }
  | "*)" {
      if depth = 1 then token lexbuf
      else block_comment (depth-1) lexbuf
    }
  | "//" { skip_line lexbuf; block_comment depth lexbuf }
  | eof {
      report_error_lex lexbuf
        "unexpected end of file inside a block comment"
    }
  | _ { block_comment depth lexbuf }

and skip_line = parse
    '\n' { Lexing.new_line lexbuf }
  | eof  { () }
  | _    { skip_line lexbuf }
