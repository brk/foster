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
  AND='and'; OR='or'; EQ='=';
  TYPE='type';
  COMPILES='__COMPILES__';

  VAL_APP; UNTIL; FORMALS;
  BINDING; LETS; LETREC; SEQ;
  RAT_NUM; INT_NUM; BOOL; STRING;
  DECL; DEFN;
  TERMNAME; TYPENAME; TYPEVAR_DECL;
  TERM; PHRASE; LVALUE; SUBSCRIPT;
  VAL_TYPE_APP; DEREF; ASSIGN_TO;
  REF; TUPLE; VAL_ABS; TYP_ABS; TYPE_ATOM;
  TYPE_TYP_APP; TYPE_TYP_ABS;
  KIND_TYPE; KIND_TYOP; KIND_TYPE_BOXED; FORALL_TYPE;
  FUNC_TYPE;
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
data_defn : TYPE CASE id ('(' tyformal ')')*
                         data_ctor*             -> ^(DATATYPE id ^(MU tyformal*) ^(MU data_ctor*));
data_ctor : OF dctor tatom*                     -> ^(OF dctor tatom*);

opr     :       SYMBOL;
id      :       SMALL_IDENT | UPPER_IDENT;

name    :     id ('.' name -> ^(QNAME id name)
                 |         -> id
                 )
        |       '(' opr ')' -> opr;

x       :       name -> ^(TERMNAME name);
a       :       name -> ^(TYPENAME name);


nameunq :      id      -> id
        |  '(' opr ')' -> opr;

xid     :      nameunq -> ^(TERMNAME nameunq); // unqualified variants,
aid     :      nameunq -> ^(TYPENAME nameunq); // needed to disambiguate grammar

ctor  :     x          -> ^(CTOR x);
dctor : '$' ctor       -> ctor ;
tctor : '$' ctor       -> ctor ;

k       :               // kinds
    'Type'                              -> ^(KIND_TYPE)         // kind of types
  | 'Boxed'                             -> ^(KIND_TYPE_BOXED)
//  |     '{' a '->' k '}'                -> ^(KIND_TYOP a k)     // dependent kinds (kinds of type operators)
  ;

e_seq 	:	 e (';' e)* ';'? -> ^(SEQ e+);
e    :
    opr? phrase
           binops? // value application, with optional prefix operator
              -> ^(TERM ^(MU opr?) ^(MU phrase) ^(MU binops?))
  ;

binops  :       (opr phrase)+;

phrase  :       lvalue+                         -> ^(PHRASE lvalue+);
lvalue  :       atom suffix*                    -> ^(LVALUE atom suffix*);

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
  | 'case' e (OF pmatch)+ 'end'         -> ^(CASE e pmatch+) // pattern matching
  | 'until' e 'then' e_seq 'end'        -> ^(UNTIL e e_seq)
  | '(' ')'                             -> ^(TUPLE)
  | '(' COMPILES e ')'                  -> ^(COMPILES e)
  | '(' 'ref' e ')'                     -> ^(REF e)     // allocation
  | '(' e (',' e)* ')'                  -> ^(TUPLE e+)  // tuples (products) (sguar: (a,b,c) == Tuple3 a b c)
  | '{' ('forall' tyformal* ',')?
        (formal '=>')*
         e_seq?
    '}'                                 -> ^(VAL_ABS ^(FORMALS formal*)
                                                     ^(MU tyformal*) e_seq?)
                  // value + type abstraction (terms indexed by terms and types)
  ;

pmatch  : p '->' e_seq -> ^(CASE p e_seq);

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

ifexpr : 'if' cond=e 'then' thenpart=e_seq 'else' elsepart=e_seq 'end'
          -> ^(IF $cond $thenpart $elsepart);

binding : x '=' e     -> ^(BINDING x e);
formal  : xid (':' t)   -> ^(FORMAL xid t);
tyformal: aid (':' k)?  -> ^(TYPEVAR_DECL aid k);
tyformalr: aid ':' k    -> ^(TYPEVAR_DECL aid k);

lets   : 'let' (binding ';')+ 'in' e_seq 'end' -> ^(LETS   ^(MU binding+) e_seq);
letrec : 'rec' (binding ';')+ 'in' e_seq 'end' -> ^(LETREC ^(MU binding+) e_seq);

////////////////////////////////////////////////////////////////////////////////

t : tatom (            -> ^(TYPE_ATOM    tatom)        // atomic types
          | tatom+     -> ^(TYPE_TYP_APP tatom tatom+) // type-level application
          )
  | 'forall' (tyformalr ',')+ t  -> ^(FORALL_TYPE tyformalr+ t) // description of terms indexed by types;
  ;

tatom :
    a                                                   // type variables
  | '??' a                              -> ^(TYPE_PLACEHOLDER a)
  | '(' ')'                             -> ^(TUPLE)
  | '(' t (',' t)* ')'                  -> ^(TUPLE t+)  // tuples (products) (sugar: (a,b,c) == Tuple3 a b c)
  | '{'    t  ('=>' t)* '}'
   ('@' '{' tannots '}')?               -> ^(FUNC_TYPE ^(TUPLE t+) tannots?)  // description of terms indexed by terms
//      | ':{'        (a ':' k '->')+ t '}'     -> ^(TYPE_TYP_ABS a k t)        // type-level abstractions
//  | tctor                                -> ^(TYPE_CTOR tctor)                  // type constructor constant
  // The dollar sign is required to distinguish type constructors
  // from type variables, since we don't use upper/lower case to distinguish.
  ;

tannots :  binding (',' binding)* -> ^(BINDING binding+);

////////////////////////////////////////////////////////////////////////////////

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
num_start               :  (id '`' hex_clump // e.g. the start of   abc`def_16
                           | DIGIT_HEX_CLUMP)  ('`' hex_clump)*;
// Numbers may end (optionally) with a trailer specifying their base.
// This is not a lexer rule because we don't want to ignore space after the _.
INT_RAT_BASE            :       '_' HEX_CLUMP;
// A rational number continues with more digits after a "decimal" point.
// To avoid ambiguity for "1234.a123" (compound.name vs num.rat), we require
// that rational numbers must distinguish the first clump after the point
// by either starting with a decimal digit (unlike IDENT), or by including
// either a clump separator or a base trailer.
rat_continue    :       '.' (      id (                        INT_RAT_BASE
                                      |       ('`' HEX_CLUMP)+ INT_RAT_BASE?)
                            | DIGIT_HEX_CLUMP ('`' HEX_CLUMP)* INT_RAT_BASE?
                            );
// A number is either an integer or a rational, depending on whether it contains a decimal point.
num     :       num_start (
          INT_RAT_BASE? -> ^(INT_NUM num_start INT_RAT_BASE?)
        | rat_continue  -> ^(RAT_NUM num_start rat_continue)
                          );

DIGIT_HEX_CLUMP         :       DIGIT HEX_DIGIT*;

fragment
HEX_CLUMP               :       DIGIT_HEX_CLUMP | SMALL_IDENT | UPPER_IDENT;
hex_clump               :       DIGIT_HEX_CLUMP | SMALL_IDENT | UPPER_IDENT;



fragment WORD_CHAR      : IDENT_START_SMALL | IDENT_START_UPPER;
fragment DIGIT          : '0'..'9';
fragment HEX_DIGIT      : DIGIT |'a'..'f' | 'A'..'F' ;

// Identifiers must start with an upper or lowercase letter.
SMALL_IDENT             :       IDENT_START_SMALL IDENT_CONTINUE*;
UPPER_IDENT             :       IDENT_START_UPPER IDENT_CONTINUE*;
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

NL  :   '\n' WS? {$channel=HIDDEN;};
WS  :   ( ' '
        | '\t'
        | '\r'
        )+ {$channel=HIDDEN;}
    ;



