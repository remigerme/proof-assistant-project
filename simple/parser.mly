%{
open Expr
%}

%token IMP AND OR TRUE FALSE NOT
%token FUN TO CASE OF
%token LPAR RPAR COLON COMMA BAR
%token FST SND LEFT RIGHT ABSURD
%token <string> IDENT
%token EOF

%right IMP
%right OR
%right AND
%nonassoc NOT

%start ty
%start tm
%type <Expr.ty> ty
%type <Expr.tm> tm
%%

/* A type */
ty:
  | IDENT     { TVar $1 }
  | ty IMP ty { TAbs ($1, $3) }
  | ty AND ty { TProd ($1, $3) }
  | ty OR ty  { TCoprod ($1, $3) }
  | NOT ty    { TAbs ($2, TEmpty) }
  | TRUE      { TUnit }
  | FALSE     { TEmpty }
  | LPAR ty RPAR { $2 }

/* A term */
tm:
  | atm                                    { $1 }
  | FUN LPAR IDENT COLON ty RPAR TO tm     { Abs ($3, $5, $8) }
  | CASE tm OF IDENT TO tm BAR IDENT TO tm { Coprod ($2, $4, $6, $8, $10) }

/* An application */
atm:
  | stm     { $1 }
  | atm stm { App ($1, $2) }

/* A simple term */
stm:
  | IDENT                        { Var $1 }
  | LPAR tm RPAR                 { $2 }
  | FST stm                      { Fst $2 }
  | SND stm                      { Snd $2 }
  | LPAR RPAR                    { Unit }
  | LPAR tm COMMA tm RPAR        { Prod ($2, $4) }
  | LEFT LPAR tm COMMA ty RPAR   { Left ($3, $5) }
  | RIGHT LPAR ty COMMA tm RPAR  { Right ($3, $5) }
  | ABSURD LPAR tm COMMA ty RPAR { Empty ($3, $5) }
