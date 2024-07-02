/** Yacc-generated parser */
%token<string> LID UID AID
/** AID - apostrophe ids */
/** LID - lowercase ids  */
/** UID - uppercase ids  */

%token<int> NUM
%token BR_OPN BR_CLS
%token TYP_STAR TYP_COLON
%token ARROW2 BAR COMMA EQ SEMICOLON
%token KW_ELSE KW_BEGIN KW_END KW_FALSE KW_FIX KW_FN KW_FST KW_IF
%token KW_IN KW_LET KW_MATCH KW_REC KW_SND KW_THEN KW_TRUE KW_TYPE
%token KW_WITH
%token TYP_KW_INT TYP_KW_BOOL TYP_KW_UNIT
%token EOF

%type<Ast.program> file
%start file

%{
include YaccParserPreamble
open Core
open Ast
%}

%%

expl_type_list2
: expl_type COMMA expl_type       { [ $1 ] }
| expl_type COMMA expl_type_list2 { $1 :: $3   }
;

expl_type
: prod_type ARROW2 expl_type                 { TArrow (EffUnknown, $1, $3) }
| prod_type                                  { $1                       }
;

 prod_type
: prod_type TYP_STAR simpl_type { TPair($1, $3)  }
| simpl_type                    { $1             }
;

simpl_type
: BR_OPN expl_type BR_CLS           { $2                       }
| AID                               { TVar $1                  }
| LID                               { desugar_type_alias $1 [] }
| LID simpl_type                    { desugar_type_alias $1 [$2] }
| LID BR_OPN expl_type_list2 BR_CLS { desugar_type_alias $1 $3 }
| TYP_KW_INT                        { TInt                     }
| TYP_KW_BOOL                       { TBool                    }
| TYP_KW_UNIT                       { TUnit                    }
;

id
: LID                                   { make $1             }
| BR_OPN LID TYP_COLON expl_type BR_CLS { make_with_typ $2 $4 }
;

id_list1
: id          { [ $1 ]   }
| id id_list1 { $1 :: $2 }
;

bar_opt
: /* empty */ { () }
| BAR         { () }
;

expr
: def_list1 KW_IN       expr      { desugar_defs $1 $3         }
| KW_FN id_list1 ARROW2 expr      { desugar_fn $2 $4 THole     }
| KW_FIX LID id_list1 ARROW2 expr { desugar_fix $2 $3 $5 THole }
| KW_MATCH expr KW_WITH
  bar_opt clauses KW_END
    { make (EMatch ($2, $5)) }
| KW_IF expr KW_THEN expr KW_ELSE expr
    { make (EIf($2, $4, $6)) }
| expr_app SEMICOLON expr { make (ESeq($1, $3)) }
| expr_app                { $1 }
;

expr_app
: expr_app expr_simple { make (EApp ($1, $2))  }
| KW_FST   expr_simple { make (EFst $2)       }
| KW_SND   expr_simple { make (ESnd $2)       }
| UID      expr_simple { make (ECtor($1, $2)) }
| expr_simple          { $1                   }
;

expr_simple
: BR_OPN BR_CLS                 { make EUnit }
| BR_OPN expr BR_CLS            { make ($2).data }
| KW_BEGIN expr KW_END          { make ($2).data }
| BR_OPN expr COMMA expr BR_CLS { make (EPair($2, $4)) }
| NUM                           { make (ENum $1) }
| LID                           { make (EVar ($1, THole)) }
| KW_TRUE                       { make (EBool true) }
| KW_FALSE                      { make (EBool false) }
;

clause
: UID LID ARROW2 expr { ($1, ($2, THole), $4) }
;

clauses
: clause             { [$1] }
| clause BAR clauses { $1 :: $3 }
;

const
: UID TYP_COLON expl_type  { ($1, $3) }
;

const_list
: const                { [ $1 ]   }
| const BAR const_list { $1 :: $3 }
;

aid_list2
: AID COMMA AID          { [$1; $3] }
| AID COMMA aid_list2    { $1 :: $3 }
;

alias
: LID                         { ($1, [])   }
| LID AID                     { ($1, [$2]) }
| LID BR_OPN aid_list2 BR_CLS { ($1, $3)   }
;

def
: KW_LET LID EQ expr                     { make (DLet(($2, THole), $4))                }
| KW_LET LID TYP_COLON expl_type EQ expr { make_with_typ (DLet(($2,$4), $6)) $4    }
| KW_LET LID id_list1 EQ expr            { desugar_let_fun $2 $3 $5 THole      }
| KW_LET LID id_list1
  TYP_COLON expl_type EQ expr            { desugar_let_fun $2 $3 $7 $5 }
| KW_LET KW_REC LID id_list1 EQ expr     { desugar_let_rec $3 $4 $6 THole      }
| KW_LET KW_REC LID id_list1
  TYP_COLON expl_type EQ expr            { desugar_let_rec $3 $4 $8 $6 }
| KW_TYPE alias EQ bar_opt const_list   { make (DType ($2, $5))              }
| KW_TYPE alias EQ expl_type            { make (DTypeAlias ($2, $4))              }
;

def_list1
: def           { [ $1 ] }
| def def_list1 { $1 :: $2 }
;

file
: expr EOF { $1 }
;
