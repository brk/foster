grammar foster;

options {
  // Leaving this line commented out lets us play with the grammar in ANTLRworks
  // and still automatically generate a C-language parser via CMake and Python.
  //language = C;
  output = AST;
}


tokens {
  AS='as'; AT='at'; DO='do'; IN='in'; IS='is'; IT='it'; TO='to';
  LET='let'; WHERE='where';

  IF='if'; THEN='then'; ELSE='else'; TRU='True'; FLS='False';
  CASE='case'; END='end'; OF='of';
  AND='and'; OR='or'; EQ='='; MINUS='-';
  TYPE='type';
  COMPILES='__COMPILES__';

  VAL_APP; FORMALS;
  BINDING; ABINDING; LETS; LETREC; SEQ; STMTS;
  LIT_NUM; BOOL; STRING;
  DECL; DEFN; PARSE_DECL;
  TERMNAME; TYPENAME; TYPEVAR_DECL;
  TERM; PHRASE; PRIMAPP; LVALUE; SUBSCRIPT;
  VAL_TYPE_APP; DEREF; ASSIGN_TO;
  REF; TUPLE; VAL_ABS; TYP_ABS; TYPE_ATOM; TYANNOT;
  TYPE_TYP_APP; TYPE_TYP_ABS;
  KIND_TYPE; KIND_TYOP; KIND_TYPE_BOXED; FORALL_TYPE;
  FUNC_TYPE; REFINED;
  TYPE_CTOR; DATATYPE; CTOR; TYPE_PLACEHOLDER;
  FORMAL; MODULE; WILDCARD; SNAFUINCLUDE; QNAME;

  MU; // child marker
}


module  :       imports* decl_or_defn* EOF   ->  ^(MODULE ^(SNAFUINCLUDE imports*)
                                                           decl_or_defn*);

imports :       ('snafuinclude' id str ';')       -> ^(SNAFUINCLUDE id str);

decl_or_defn :
        x ( '::' t ';'                    -> ^(DECL x t)
          | EQ atom ';'                   -> ^(DEFN x atom) // We should allow suffixes, but only of type application.
          )
        | data_defn ';'                   -> data_defn
        ;

// Or perhaps TYPE id OF (CASE ctor ...)+
data_defn : TYPE CASE nm=tyformal
                         ('(' args+=tyformal ')')*
                         data_ctor*             -> ^(DATATYPE $nm ^(MU $args*) ^(MU data_ctor*));
data_ctor : OF dctor tatom*                     -> ^(OF dctor tatom*);

opr     :       SYMBOL;
id      :       SMALL_IDENT | UPPER_IDENT | UNDER_IDENT;

name    :     id ('.' name -> ^(QNAME id name)
                 |         -> id
                 )
        |       '(' opr ')' -> opr;

nopr    :       name | opr;

x       :       name -> ^(TERMNAME name);
a       :       name -> ^(TYPENAME name);


nameunq :      id      -> id
        |  '(' opr ')' -> opr;

xid     :      nameunq -> ^(TERMNAME nameunq); // unqualified variants,
aid     :      nameunq -> ^(TYPENAME nameunq); // needed to disambiguate grammar

ctor  :     x          -> ^(CTOR x);
dctor : '$' ctor       -> ctor ;
tctor : '$' ctor       -> ctor ;

k       :              // kinds
    'Type'                              -> ^(KIND_TYPE)         // kind of types
  | 'Boxed'                             -> ^(KIND_TYPE_BOXED)
//  |     '{' a '->' k '}'                -> ^(KIND_TYOP a k)     // dependent kinds (kinds of type operators)
  ;

// Syntax sugar for sequence of (recursive) let bindings & expressions.
// the last stmt in stmts should be an expr, not a binding,
// but we can give better error messages later on in the pipeline.
stmts   :  stmt_ (';' stmt_)* ';'? -> ^(STMTS stmt_ +);
stmt_   : abinding | e ;
abinding : 'REC' idbinding -> ^(ABINDING 'rec' idbinding)
         |        pbinding -> ^(ABINDING        pbinding);

idbinding : xid '=' e    -> ^(BINDING xid e);
pbinding  : xid '=' e    -> ^(BINDING xid e);

e       :
    opr? phrase
           binops? // value application, with optional prefix operator
              -> ^(TERM ^(MU opr?) ^(MU phrase) ^(MU binops?))
  ;

binop   : opr          -> opr
        | '`' name '`' -> name
        ;

binops  : (binop phrase)+;

phrase  :       '-'?   lvalue+                  -> ^(PHRASE '-'?  lvalue+)
        |       'prim' nopr tyapp? lvalue*      -> ^(PRIMAPP nopr ^(MU tyapp?) lvalue*);
lvalue  :              atom suffix*             -> ^(LVALUE atom suffix*);

tyapp : type_application;
type_application
        :	':[' t (',' t)* ']'          -> ^(VAL_TYPE_APP t+) // type application
        |	':['  ']'                    -> ^(VAL_TYPE_APP)    // nullary type application
        ;

suffix  :       type_application
  |     '^'                             -> ^(DEREF)             // dereference
  |     '[' e ']'                       -> ^(SUBSCRIPT e)
  |     '!'                             -> ^(VAL_APP)		// nullary call
//      |       '.(' e ')'                      -> ^(VAL_APP e)
  ;

atom    :       // syntactically "closed" terms
    x                                   // variables
  | lit                                 // literals
  | lets                                // sequential let
  | letrec                              // recursive let
  | ifexpr
  | parse_in
  | 'case' e (OF pmatch)+ 'end'         -> ^(CASE e pmatch+) // pattern matching
  | '(' ')'                             -> ^(TUPLE)
  | '(' COMPILES e ')'                  -> ^(COMPILES e)
  | '(' 'ref' e ')'                     -> ^(REF e)     // allocation
  | tuple
  | val_abs
  ;

val_abs :
    '{' ('forall' tyformal* ',')?
        (formal '=>')*
         stmts?
    '}'                                 -> ^(VAL_ABS ^(FORMALS formal*)
                                                     ^(MU tyformal*)
                                                     stmts?)
                  // value + type abstraction (terms indexed by terms and types)
    ;

parse_in :
	'#associate' e 'as' e 'in' stmts 'end' -> ^(PARSE_DECL e e stmts)
	;

tuple : '(' e ( AS  t    ')'                  -> ^(TYANNOT e t)
              | (',' e)* ')'                  -> ^(TUPLE e+)  // tuples (products) (sugar: (a,b,c) == Tuple3 a b c)
              )
      ;

pmatch  : p ('if' e)? '->' stmts -> ^(CASE p e stmts);

// Example: (C _ (C2 3 x), C3, 0).
p : dctor patom*  -> ^(MU dctor patom*)
  | patom         -> ^(MU patom);

patom :
    x                                      // variables
  | '_'                  -> ^(WILDCARD)    // wildcards
  | lit
  | '(' ')'              -> ^(TUPLE)
  | '(' p (',' p)* ')'   -> ^(TUPLE p+)    // tuples (products)
  ;

lit     : num | str | TRU -> ^(BOOL TRU) | FLS -> ^(BOOL FLS);

ifexpr : 'if' cond=e 'then' thenpart=stmts 'else' elsepart=stmts 'end'
          -> ^(IF $cond $thenpart $elsepart);

binding  : x '=' e       -> ^(BINDING x e);
formal   : xid (':' t)?  -> ^(FORMAL xid t);
tyformal : aid (':' k)?  -> ^(TYPEVAR_DECL aid k);
tyformalr: aid ':' k     -> ^(TYPEVAR_DECL aid k);

lets   : 'let' (binding ';')+ 'in' stmts 'end' -> ^(LETS   ^(MU binding+) stmts);
letrec : 'rec' (binding ';')+ 'in' stmts 'end' -> ^(LETREC ^(MU binding+) stmts);

////////////////////////////////////////////////////////////////////////////////

// "refined type"
t  : '%' xid ':' tp ':' e -> ^(REFINED xid tp e)
   | tp;

tp // "type phrase"
  : tatom (            -> ^(TYPE_ATOM    tatom)        // atomic types
          | tatom+     -> ^(TYPE_TYP_APP tatom tatom+) // type-level application
          )
  | 'forall' (tyformalr ',')+ t  -> ^(FORALL_TYPE tyformalr+ t) // description of terms indexed by types;
  ;

tatom :
    a                                                   // type variables
  | '??' a                              -> ^(TYPE_PLACEHOLDER a)
  | '(' ')'                             -> ^(TUPLE)
  | '(' t (',' t)* ')'                  -> ^(TUPLE t+)  // tuples (products) (sugar: (a,b,c) == Tuple3 a b c)
  | ('#precondition' val_abs)?
    '{'    t  ('=>' t)* '}'
   ('@' '{' tannots '}')?               -> ^(FUNC_TYPE ^(TUPLE t+) ^(MU val_abs?) tannots?)  // description of terms indexed by terms
//      | ':{'        (a ':' k '->')+ t '}'     -> ^(TYPE_TYP_ABS a k t)        // type-level abstractions
//  | tctor                                -> ^(TYPE_CTOR tctor)                  // type constructor constant
  // The dollar sign is required to distinguish type constructors
  // from type variables, since we don't use upper/lower case to distinguish.
  ;

tannots :  binding (',' binding)* -> ^(BINDING binding+);

////////////////////////////////////////////////////////////////////////////////

// Numbers are things like:
//    1
//    -2
//    1234
//    10101011_2
//    1011`1011_2
//    FEEDFACE_16
//    12.34
//    12.34`56
//    12.34e+01
//    12.34e-10
/*
                      // not currently supported:
                      //    12.34_16
                      //    12.34abc_16
                      //    12.abc_16
                      // If we supported hex clumps following a decimal point,
                      // we would need to use a non-hex digit (like x) to avoid
                      // ambiguity between 1.0e+0 being parsed as
                      // num.hexclump + num  vs num.hexclump sci_notation.
                      // So we don't support hex clumps, nor base specifiers.
*/

num : NUM -> ^(LIT_NUM NUM);
NUM			:  '-'? DIGIT HEX_CLUMP? ('`' HEX_CLUMP)*
				( '.' DIGIT* ('`' DIGIT+)* SCI_NOTATION?
				|                          INT_RAT_BASE?
				);
fragment SCI_NOTATION	: ('e'|'E') ('+'|'-') DIGIT+;
fragment INT_RAT_BASE   : '_' HEX_CLUMP;
fragment HEX_CLUMP      : DIGIT HEX_DIGIT* | SMALL_IDENT | UPPER_IDENT;

fragment WORD_CHAR      : IDENT_START_SMALL | IDENT_START_UPPER;
fragment DIGIT          : '0'..'9';
fragment HEX_DIGIT      : DIGIT |'a'..'f' | 'A'..'F' ;

// Identifiers must start with an upper or lowercase letter, or an underscore.
SMALL_IDENT             :       IDENT_START_SMALL IDENT_CONTINUE*;
UPPER_IDENT             :       IDENT_START_UPPER IDENT_CONTINUE*;
UNDER_IDENT             :       '_'               IDENT_CONTINUE+;
fragment IDENT_START_SMALL : 'a'..'z' ;
fragment IDENT_START_UPPER : 'A'..'Z' ;
fragment IDENT_CONTINUE    : (DIGIT | WORD_CHAR | IDENT_SYMBOL);
// Meanwhile, symbols start with a non-numeric, non-alphabetic glyph.
// We must play some tricks here to ensure that '=' is a keyword, not a symbol.
// Also, +Int32 is a symbol, but +2 is not.
SYMBOL    :    SYMBOL_SINGLE_START
          |    SYMBOL_MULTI_START   SYMBOL_CONTINUE_NDIG   SYMBOL_CONTINUE*;

fragment SYMBOL_CONTINUE        :(SYMBOL_CONTINUE_NDIG | DIGIT);
fragment SYMBOL_CONTINUE_NDIG   :('/' | '^' | WORD_CHAR | IDENT_SYMBOL);

fragment IDENT_SYMBOL   :      '_' | SYMBOL_MULTI_START;
fragment SYMBOL_MULTI_START  : '=' | SYMBOL_SINGLE_START;
fragment SYMBOL_SINGLE_START : '!' | '|'
        | '>' | '<' | '-'
        | '?' | '+' | '*';



str                     :       s=STR -> ^(STRING $s);

fragment TICK  : '\'';
fragment TRTK  : '\'\'\''; // triple-tick
fragment DQUO  : '"'; // double-quote
fragment TDQU  : '"""'; // triple double-quote
fragment BACKSLASH : '\\';

// TODO single-mark strings should not contain newlines,
// but to give better error messages, we delay checking
// until post-processing.
STR
  // tick,
  // stuff that's not a tick or an escape sequence,
  // escape sequence, then chars that won't end the string
  //                       or start another escape sequence,
  // tick
    : 'r'?
    (  TICK (~(BACKSLASH|TICK))* ( ESC_SEQ (~(BACKSLASH|TICK)*) )* TICK
    |  DQUO (~(BACKSLASH|DQUO))* ( ESC_SEQ (~(BACKSLASH|DQUO)*) )* DQUO
    |  TDQU (options {greedy=false;} : (.))* TDQU
    |  TRTK (options {greedy=false;} : (.))* TRTK
    )
    ;

// Escape sequences are limited to \n, \t, \r, \", \', \\, and \u...
fragment ESC_SEQ        :       '\\' ('t'|'n'|'r'|'"'|TICK|'\\') | UNICODE_ESC;

// Examples of Unicode escape sequences:
//      \u0000
//      \U0000
//      \u{00}
//      \u00
//      \u+00
//      \U+00b1
//      \u{00b1}
//      \u{Plus-minus sign}     // U+00B1
//      \U{123}
//      \U{123456}
// Non-examples (lexically)
//      \u{&&}          -- invalid char in escape
// Non-examples (post-processing)
//      \u{}            -- need at least two
//      \u{0}           -- need at least two
//      \u{12345789}    -- too long
//      \u{foobity}     -- no such escape!
fragment UNICODE_ESC : '\\' ('u' | 'U')
        ( '+'? HEX_DIGIT HEX_DIGIT (HEX_DIGIT HEX_DIGIT)?
        | '{' UNICODE_INNER* '}');
fragment UNICODE_INNER
  : ('a'..'z'|'A'..'Z'|'0'..'9'|'_'|' '|'+'|'-');


LINE_COMMENT    :       '//' ~('\n'|'\r')* '\r'? {$channel=HIDDEN;} ;

NESTING_COMMENT :
    '/*' ( options {greedy=false;} :
           NESTING_COMMENT | .
          ) *
    '*/' {$channel=HIDDEN;}
    ;

NL  :   '\n' {$channel=HIDDEN;};
WS  :   ( ' '
        | '\t'
        | '\r'
        )+ {$channel=HIDDEN;}
    ;



