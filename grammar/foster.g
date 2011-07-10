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

  IF='if'; THEN='then'; ELSE='else'; TRU='true'; FLS='false';
  CASE='case'; END='end'; OF='of';
  AND='and'; OR='or'; EQ='=';
  TYPE='type';
  COMPILES='__COMPILES__';

  VAL_APP; UNTIL; FORMALS;
  BINDING; LETS; LETREC; SEQ;
  RAT_NUM; INT_NUM; BOOL;
  DECL; DEFN;
  TERMVAR; TYPEVAR;
  TERM; PHRASE; LVALUE; SUBSCRIPT;
  VAL_TYPE_APP; DEREF; ASSIGN_TO;
  REF; TUPLE; VAL_ABS; TYP_ABS; TYPE_ATOM;
  TYPE_TYP_APP; TYPE_TYP_ABS;
  KIND_TYPE; KIND_TYOP; FORALL_TYPE;
  FUNC_TYPE;
  TYPE_CTOR;
  FORMAL; MODULE; WILDCARD;
}


program :       decl_or_defn* EOF               ->  ^(MODULE decl_or_defn*);

decl_or_defn : decl | defn;
decl    :       x '::' t ';'                    -> ^(DECL x t);
defn    :       x EQ atom ';'                   -> ^(DEFN x atom); // We should allow suffixes, but only of type application.

opr     :       SYMBOL;
id      :       IDENT;

x       :       id              -> ^(TERMVAR id)
        |       '(' opr ')'     -> ^(TERMVAR opr);       // term variables

a       :       id              -> ^(TYPEVAR id)
        |       '(' opr ')'     -> ^(TYPEVAR opr);       // type variables

k       :               // kinds
    'Type'                              -> ^(KIND_TYPE)         // kind of types
  |     '{' a '->' k '}'                -> ^(KIND_TYOP a k)     // dependent kinds (kinds of type operators)
  ;

e_seq 	:	 e (';' e)* ';'? -> ^(SEQ e+);
e    :
    phrase
        binops? // value application
              -> ^(TERM phrase binops?)
  ;

binops  :       (binop phrase)+;
binop   :       SYMBOL;

phrase  :       lvalue+                         -> ^(PHRASE lvalue+);
lvalue  :       atom suffix*                    -> ^(LVALUE atom suffix*);

type_application
	:	':[' t (',' t)* ']'             -> ^(VAL_TYPE_APP t+)    // type application
	;

suffix  :       type_application
  |     '^'                             -> ^(DEREF)             // dereference
  |     '[' e ']'                       -> ^(SUBSCRIPT e)
//      |       '.(' e ')'                      -> ^(VAL_APP e)
  ;

ifexpr                  :       'if' cond=e 'then' thenpart=e_seq 'else' elsepart=e_seq 'end'
          -> ^(IF $cond $thenpart $elsepart);

binding : x '=' e ';' -> ^(BINDING x e);

lets    : 'let' binding+ 'in' e_seq 'end'   -> ^(LETS binding+ e_seq);

// atom is really (type/val abstraction)
letrec : 'rec' binding+ 'in' atom 'end' -> ^(LETREC binding+ atom);

formal  : x (':' t) -> ^(FORMAL x t);

atom    :       // syntactically "closed" terms
    x                                   // variables
  | lit                                 // literals
  | lets
  | letrec
  | ifexpr
  | 'until' e 'then' e_seq 'end'        -> ^(UNTIL e e_seq)
  | '(' ')'                             -> ^(TUPLE)
  | '(' COMPILES e ')'                  -> ^(COMPILES e)
  | '(' 'ref' e ')'                     -> ^(REF e)     // allocation
  | '(' e (',' e)* ')'                  -> ^(TUPLE e+)  // tuples (products) (sguar: (a,b,c) == Tuple3 a b c)
  | '{' (formal '=>')* e_seq? '}'       -> ^(VAL_ABS ^(FORMALS formal*) e_seq?) // value abstraction (terms indexed by terms)
//      | '{' 'forall' a ':' k ',' e '}'        -> ^(TYP_ABS a k e) // type abstraction (terms indexed by types)
  | CASE e (OF pmatch)+ END             -> ^(CASE e pmatch+) // pattern matching
  ;

pmatch  : p '->' e_seq -> ^(CASE p e_seq);

p       :               // patterns
    x                                     // variables
  | '_'                 -> ^(WILDCARD)    // wildcards
  | lit
  | '(' ')'             -> ^(TUPLE)
  | '(' p (',' p)* ')'  -> ^(TUPLE p+)    // tuples (products)
  ;

lit     : num | str | TRU -> ^(BOOL TRU) | FLS -> ^(BOOL FLS);

/////////////////////////////////////////////////////////////////////////////////////////

t       :               // types
    tatom (                             -> ^(TYPE_ATOM    tatom) // atomic types
          | t2=t                                -> ^(TYPE_TYP_APP tatom t) // type-level application
          )
  ;

barebinding
	:  x '=' e -> ^(BINDING x e);
tannots :  barebinding (',' barebinding)* -> ^(BINDING barebinding+);

tatom   :
    a                                                                   // type variables
  | '(' ')'                             -> ^(TUPLE)
  | '(' t (',' t)* ')'                  -> ^(TUPLE t+)  // tuples (products) (sugar: (a,b,c) == Tuple3 a b c)
//      | ':{'        (a ':' k '->')+ t '}'     -> ^(TYPE_TYP_ABS a k t)        // type-level abstractions
  | '{'    t  ('=>' t)* '}'
   ('@' '{' tannots '}')?               -> ^(FUNC_TYPE ^(TUPLE t+) tannots?)  // function types
//      | '{' 'forall' (a ':' k ',')+ t '}'     -> ^(FORALL_TYPE a k t)         // universal type
  | '$' ctor                                        -> ^(TYPE_CTOR ctor)            // type constructor constant
  // The dollar sign is required to distinguish type constructors
  // from type variables, since we don't use upper/lower case to distinguish.
  ;

ctor : x ;


// Numbers are things like:
//    1
//    1234
//    10101011_2
//    1011`1011_2
//    FEEDFACE_16
//
// Every number starts with a sequence of one or more
// hexadecimal digit clumps, separated by backticks.
// ((fragment))
num_start               :  (IDENT '`' hex_clump  | DIGIT_HEX_CLUMP)  ('`' hex_clump)*;
// Numbers may end (optionally) with a trailer specifying their base.
// ((fragment))
int_rat_base            :       '_' hex_clump;
// A rational number continues with more digits after a "decimal" point.
// To avoid ambiguity for "1234.a123" (compound.name vs num.rat), we require
// that rational numbers must distinguish the first clump after the point
// by either starting with a decimal digit (unlike IDENT), or by including
// either a clump separator or a base trailer.
rat_continue    :       '.' (   IDENT (                    int_rat_base
              |   ('`' hex_clump)+ int_rat_base?)
      | DIGIT_HEX_CLUMP ('`' hex_clump)* int_rat_base?
      );
// A number is either an integer or a rational, depending on whether it contains a decimal point.
num     :       num_start (
          int_rat_base? -> ^(INT_NUM num_start int_rat_base?)
        | rat_continue  -> ^(RAT_NUM num_start rat_continue)
                          );

str                     :       s=STR -> ^(STR $s);

hex_clump               :       DIGIT_HEX_CLUMP | IDENT;
DIGIT_HEX_CLUMP         :       ('0'..'9') HEX_DIGIT*;


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




// Identifiers must start with an upper or lowercase letter.
IDENT                   :       IDENT_START IDENT_CONTINUE*;
// Meanwhile, symbols start with a non-numeric, non-alphabetic glyph.
// We must play some tricks here to ensure that '=' is a keyword, not a symbol.
SYMBOL                  :       SYMBOL_SINGLE_START
                        |       SYMBOL_MULTI_START  SYMBOL_CONTINUE+;

fragment IDENT_START            : 'a'..'z' | 'A'..'Z';
fragment IDENT_CONTINUE         :('a'..'z' | 'A'..'Z' | '0'..'9' | IDENT_SYMBOL);
fragment SYMBOL_CONTINUE        :('a'..'z' | 'A'..'Z' |            SYMBOL_GLYPH);
fragment SYMBOL_SINGLE_START   :  '!' | '|'
        | '>' | '<' | '-'
        | '?' | '+' | '*';
fragment SYMBOL_MULTI_START : '=' | SYMBOL_SINGLE_START;
fragment IDENT_SYMBOL   :         '_' | SYMBOL_MULTI_START;
fragment SYMBOL_GLYPH   :         '/' | '^' | IDENT_SYMBOL;

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


fragment HEX_DIGIT      :       ('0'..'9'|'a'..'f'|'A'..'F');

LINE_COMMENT    :       '//' ~('\n'|'\r')* '\r'? {$channel=HIDDEN;} ;

NESTING_COMMENT :
    '/*' ( options {greedy=false;} :
           NESTING_COMMENT | .
          ) *
    '*/' {$channel=HIDDEN;}
    ;

NL  :   '\n' WS? {$channel=HIDDEN;};
WS  :   ( ' '
        | '\t'
        | '\r'
        )+ {$channel=HIDDEN;}
    ;


