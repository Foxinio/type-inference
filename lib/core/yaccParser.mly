/** Yacc-generated parser */
%token<string> LID UID AID 
/** AID - apostrophe ids */
%token<int> NUM
%token BR_OPN BR_CLS CBR_OPN CBR_CLS
%token TYP_STAR TYP_PLUS TYP_COLON
%token ARROW2 BAR COMMA DOT EQ SEMICOLON
%token KW_ABSURD KW_CASE KW_ELSE KW_BEGIN KW_END KW_FALSE KW_FIX KW_FN KW_FST KW_IF
%token KW_IN KW_INL KW_INR KW_LET KW_MATCH KW_OF KW_REC KW_SND KW_THEN KW_TRUE KW_TYPE
%token KW_WITH
%token TYP_KW_INT TYP_KW_BOOL TYP_KW_UNIT
%token EOF

%type<Ast.program> file
%start file

%{
open Ast

type 'typ def =
| DLet of 'typ var * 'typ expr
| DType of scheme * (ctor_name * 'typ) list
| DTypeAlias of scheme * 'typ

let make data =
  { data      = data;
    typ       = None;
    start_pos = Parsing.symbol_start_pos ();
    end_pos   = Parsing.symbol_end_pos ();
  }

let make_with_typ data typ =
  { (make data) with typ=Some(typ) }

let extract args typ =
  let extract_ids arg = (arg.data, arg.typ) in
  let found = ref (Option.is_some typ) in
  let extract_typ = function
    | {typ=Some tp;_} -> found := true; tp
    | {typ=None; _}   -> THole
  in
  let extracted_typ = List.map extract_typ args in
  let typ = Option.value ~default:(THole) typ in
  (List.map extract_ids args,
   if !found then Some(TArrow(extracted_typ, typ)) else None)

let desugar_fn args body typ =
  let args, typ = extract args typ in
  { (make (EFn(args, body))) with typ }

let desugar_fix fn args body typ =
  let args, typ = extract args typ in
  { (make (EFix(fn, args, body))) with typ }

let desugar_let_fun fn args body typ =
  make (DLet(fn, desugar_fn args body typ))

let desugar_let_rec fn args body typ =
  make (DLet(fn, desugar_fix fn args body typ))

let desugar_def def rest =
  match def.data with
  | DLet(x, body) ->
    { data      = ELet(x, body, rest);
      typ       = None;
      start_pos = def.start_pos;
      end_pos   = rest.end_pos
    }
  | DType(x, cts) ->
    { data      = EType(x, cts, rest);
      typ       = None;
      start_pos = def.start_pos;
      end_pos   = rest.end_pos
    }
  | DTypeAlias(vars, name) ->
    { data      = ETypeAlias(vars, name, rest);
      typ       = None;
      start_pos = def.start_pos;
      end_pos   = rest.end_pos
    }

let desugar_defs defs rest =
  List.fold_right desugar_def defs rest

let desugar_app = function
  | fn :: args ->
    make (EApp(fn, args))
  | [] -> assert false

(* maybe there is a better way to do this,
   but i think its over all a good idea *)
let desugar_type_id id =
  if id = "_" then THole
  else TVar id


%}

%%

type_list2
: expl_type COMMA expl_type  { [ $1; $3 ] }
| expl_type COMMA type_list2 { $1 :: $3   }
;


expl_type
: sum_type ARROW2 expl_type                 { TArrow ([ $1 ], $3) }
| BR_OPN type_list2 BR_CLS ARROW2 expl_type { TArrow ($2, $5) }
| sum_type                                  { $1 }
;

sum_type
: sum_type TYP_PLUS prod_type  { TCoProd ($1, $3) }
| prod_type                    { $1 }
;

prod_type 
: prod_type TYP_STAR simpl_type  { TProd($1, $3)  }
| simpl_type                     { $1 }
;

simpl_type
: BR_OPN expl_type BR_CLS { $2 }
| LID                     { desugar_type_id $1   }
| AID                     { TVar $1              }
| expl_type LID           { TSchema ([ $1 ], $2) }
| BR_OPN type_list2 BR_CLS LID { TSchema ($2, $4) }
| TYP_KW_INT              { TInt }
| TYP_KW_BOOL             { TBool }
| TYP_KW_UNIT             { TUnit }
;

id
: LID { make $1 }
| BR_OPN LID TYP_COLON expl_type BR_CLS { make_with_typ $2 $4 }
;

id_list1
: id          { [ $1 ] }
| id id_list1 { $1 :: $2 }
;

bar_opt
: /* empty */ { () }
| BAR         { () }
;

expr
: def_list1 KW_IN       expr { desugar_defs $1 $3 }
| KW_FN id_list1 ARROW2 expr { desugar_fn $2 $4 }
| KW_FIX LID id_list1 ARROW2 expr { desugar_fix $2 $3 $5 }
| KW_CASE expr KW_OF
  bar_opt KW_INL LID ARROW2 expr
  BAR     KW_INR LID ARROW2 expr
    { make (ECase($2, ($6, $8), ($11, $13))) }
| KW_MATCH expr KW_WITH
  bar_opt clauses KW_END
    { $5 (Parsing.symbol_start_pos ()) $2 }
| KW_IF expr KW_THEN expr KW_ELSE expr
    { make (EIf($2, $4, $6)) }
| KW_ABSURD expr { make (EAbsurd $2) }
| expr_app SEMICOLON expr { make (ESeq($1, $3)) }
| expr_app { $1 }
;

expr_app
: expr_simple_list2 { desugar_app $1 }
| KW_FST   expr_simple { make (EFst $2) }
| KW_SND   expr_simple { make (ESnd $2) }
| KW_INL   expr_simple { make (EInl $2) }
| KW_INR   expr_simple { make (EInr $2) }
| UID      expr_simple { make (ECtor($1, $2)) }
| expr_simple { $1 }
;

expr_simple_list2
: expr_simple expr_simple { [ $1; $2 ] }
| expr_simple expr_simple_list2 { $1 :: $2 }
;

expr_simple
: BR_OPN BR_CLS                 { make EUnit }
| BR_OPN expr BR_CLS            { make ($2).data }
| KW_BEGIN expr KW_END          { make ($2).data }
| BR_OPN expr COMMA expr BR_CLS { make (EPair($2, $4)) }
| NUM      { make (ENum $1) }
| LID      { make (EVar $1) }
| KW_TRUE  { make (EBool true) }
| KW_FALSE { make (EBool false) }
;

(* clause *)
(* : UID LID ARROW2 *)

(* all this requires reworking to new model *)
(* TODO: rework this                        *)
clauses
: LID ARROW2     expr
  { let end_pos = Parsing.symbol_end_pos () in
    fun start_pos e ->
    { data      = ELet($1, e, $3);
      start_pos = start_pos;
      end_pos   = end_pos } }
| UID LID ARROW2 expr
  { let end_pos = Parsing.symbol_end_pos () in
    let make_at_end data = { data; start_pos = end_pos; end_pos } in
    fun start_pos e ->
    { data      = EMatch(e, $1, ($2, $4),
        ("$rest", make_at_end (EMatchEmpty(make_at_end (EVar "$rest")))));
      start_pos = start_pos;
      end_pos   = end_pos } }
| UID LID ARROW2 expr BAR clauses
  { let bar_pos = Parsing.rhs_start_pos 5 in
    let end_pos = Parsing.symbol_end_pos () in
    let make_at_bar data = { data; start_pos = bar_pos; end_pos = bar_pos } in
    fun start_pos e ->
    { data      = EMatch(e, $1, ($2, $4),
        ("$rest", $6 bar_pos (make_at_bar (EVar "$rest"))));
      start_pos = start_pos;
      end_pos   = end_pos } }
;

const
: LID TYP_COLON expl_type  { ($1, $3) }
;

const_list
: const                { [ $1 ]   }
| const BAR const_list { $1 :: $3 }
;

types
: const  { [ $1 ]   }
| const BAR types        { $1 :: $3 }
;

scheme
: LID                         { ([], $1)   }
| AID LID                     { ([$1], $2) }
| BR_OPN aid_list2 BR_CLS LID { ($2, $4)   }
;

aid_list2
: AID COMMA AID          { [$1; $3] }
| AID COMMA aid_list2    { $1 :: $3 }
;

def
: KW_LET LID EQ expr                     { make (DLet($2, $4))                }
| KW_LET LID TYP_COLON expl_type EQ expr { make_with_typ (DLet($2, $6)) $4    }
| KW_LET LID id_list1 EQ expr            { desugar_let_fun $2 $3 $5 None      }
| KW_LET LID id_list1
  TYP_COLON expl_type EQ expr            { desugar_let_fun $2 $3 $7 (Some $5) }
| KW_LET KW_REC LID id_list1 EQ expr     { desugar_let_rec $3 $4 $6 None      }
| KW_LET KW_REC LID id_list1
  TYP_COLON expl_type EQ expr            { desugar_let_rec $3 $4 $8 (Some $6) }
| KW_TYPE scheme EQ bar_opt types           { make (DType ($2, $5))              }
| KW_TYPE scheme EQ expl_type               { make (DTypeAlias ($2, $4))              }
;

def_list1
: def           { [ $1 ] }
| def def_list1 { $1 :: $2 }
;

file
: expr EOF { $1 }
;
