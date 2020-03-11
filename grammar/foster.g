grammar foster;

options {
  // Leaving this line commented out lets us play with the grammar in ANTLRworks
  // and still automatically generate a C-language parser via CMake and Python.
  //language = C;
  output = AST;

  // Grammar is LL(5); lookahead is needed to
  // disambiguate    '(' '(' SYMBOL ')'
}


tokens {
  AS='as'; AT='at'; DO='do'; IN='in'; IS_='is'; IT='it'; TO='to';
  LET='let'; WHERE='where'; WITH='with';

  IF='if'; THEN='then'; ELSE='else'; TRU='True'; FLS='False';
  CASE='case'; END='end'; OF='of';
  AND='and'; OR='or'; EQ='='; MINUS='-';
  FOREIGN='foreign'; IMPORT='import';
  TYPE='type'; EFFECT='effect'; HANDLE='handle';
  COMPILES='__COMPILES__';
  HASH_MARK='#';

  OPEN_PAREN='('; CLOSE_PAREN=')';
  OPEN_SQRBR='['; CLOSE_SQRBR=']'; OPEN_COLON_SQRBR=':['; OPEN_DOT_SQRBR='.[';
  OPEN_CURLY='{'; CLOSE_CURLY='}';

  VAL_APP; FORMALS;
  BINDING; ABINDING; LETS; LETREC; SEQ; STMTS;
  LIT_NUM; BOOL; STRING;
  DECL; DEFN; PARSE_DECL;
  TERMNAME; TYPENAME; TYPEVAR_DECL;
  TERM; PHRASE; PRIMAPP; LVALUE; SUBSCRIPT;
  VAL_TYPE_APP; DEREF; ASSIGN_TO;
  TUPLE; VAL_ABS; TYP_ABS; TYPE_ATOM; TYANNOT;
  TYPE_TYP_APP; TYPE_TYP_ABS;
  KIND_CONST; KIND_TYOP; FORALL_TYPE;
  FUNC_TYPE; REFINED;
  TYPE_CTOR; DATATYPE; CTOR; TYPE_PLACEHOLDER;
  FORMAL; MODULE; WILDCARD; SNAFUINCLUDE; QNAME;
  EFFECT_SINGLE; EFFECT_ROW;

  MU; // child marker
}


module  :       imports* decl_or_defn* EOF   ->  ^(MODULE ^(SNAFUINCLUDE imports*)
                                                           decl_or_defn*);

imports :       ('snafuinclude' id s=DQUO_STR ';')     -> ^(SNAFUINCLUDE id $s);

decl_or_defn :
        'REC'? x ( '::' t ';'             -> ^(DECL x t)
                 | EQ phrase ';'          -> ^(DEFN x phrase) // We should allow suffixes, but only of type application.
                 )
        | data_defn ';'                   -> data_defn
        | effect_defn ';'                 -> effect_defn
        | FOREIGN IMPORT x (AS id)? '::' t ';'
                                          -> ^(FOREIGN DECL x t id?)
        | FOREIGN TYPE tyformal   ';'     -> ^(FOREIGN TYPE tyformal)
        ;

// Or perhaps TYPE id OF (CASE ctor ...)+
data_defn : TYPE CASE nm=tyformal
                         ('(' args+=tyformal ')')*
                         data_ctor*             -> ^(DATATYPE $nm ^(MU $args*) ^(MU data_ctor*));
data_ctor : OF dctor tatom*                     -> ^(OF dctor tatom*);

effect_defn : EFFECT nm=tyformal
                         ('(' args+=tyformal ')')*
                         effect_ctor*             -> ^(EFFECT $nm ^(MU $args*) ^(MU effect_ctor*));
effect_ctor : OF dctor tatom* ('=>' t)?           -> ^(OF dctor ^(MU tatom*) ^(MU t?));

opr     :       SYMBOL | MINUS;
id      :       SMALL_IDENT | UPPER_IDENT | UNDER_IDENT;

name    :     id ('.' name -> ^(QNAME id name)
                 |         -> id
                 )
        |       '(' opr ')' -> opr;

x       :       name -> ^(TERMNAME name);
a       :       name -> ^(TYPENAME name);


nameunq :      id      -> id
        |  '(' opr ')' -> opr;

pid     :      id      -> ^(TERMNAME id);
xid     :      nameunq -> ^(TERMNAME nameunq); // unqualified variants,
aid     :      id      -> ^(TYPENAME id); // needed to disambiguate grammar

ctor  :     x          -> ^(CTOR x);
dctor : '$' ctor       -> ctor ;
tctor : '$' ctor       -> ctor ;

k       :              // kinds
    a                                     -> ^(KIND_CONST a)
//  |     '{' a '->' k '}'                -> ^(KIND_TYOP a k)     // dependent kinds (kinds of type operators)
  ;

// Syntax sugar for sequence of (recursive) let bindings & expressions.
// the last stmt in stmts should be an expr, not a binding,
// but we can give better error messages later on in the pipeline.
stmts   :  stmt_ stmt_cont* ';'* -> ^(STMTS stmt_ stmt_cont*);
stmt_   : abinding | e ;
stmt_cont : semi=';'+ stmt_ -> ^(MU $semi stmt_);
abinding : 'REC' pbinding -> ^(ABINDING 'REC' pbinding)
         |       pbinding -> ^(ABINDING       pbinding);
pbinding  : patbind '=' e    -> ^(BINDING patbind e);

patbind :
  xid                                      // variables
  | '_'                  -> ^(WILDCARD)    // wildcards
  | 'let' '(' p (',' p)* ')'   -> ^(TUPLE p+)    // tuples (products)
  ;

e       :
    phrase
           binops? // value application, with optional prefix operator
              -> ^(TERM phrase ^(MU binops?))
  ;

binops  : (binop phrase)+;
binop   : opr          -> opr
        | '`' name '`' -> name
        ;

nopr    : name | opr ;
phrase  :       lvalue+                         -> ^(PHRASE lvalue+)
        |       'prim' nopr tyapp? lvalue*      -> ^(PRIMAPP nopr ^(MU tyapp?) lvalue*);
lvalue  :              atom suffix*             -> ^(LVALUE atom suffix*);

tyapp   :	':[' t (',' t)* ']'          -> ^(VAL_TYPE_APP t+) // type application
        |	':['  ']'                    -> ^(VAL_TYPE_APP)    // nullary type application
        ;

suffix  :  tyapp
        |  '^'                          -> ^(DEREF)             // dereference
        |  '.[' e ']'                   -> ^(SUBSCRIPT e)
        |  '!'                          -> ^(VAL_APP)		// nullary call
//      |    '.(' e ')'                 -> ^(VAL_APP e)
  ;

atom    :       // syntactically "closed" terms
    x                                   // variables
  | lit                                 // literals
  | ifexpr
  | 'case' e (OF pmatch)+ 'end'         -> ^(CASE e pmatch+) // pattern matching
  | '(' ')'                             -> ^(TUPLE)
  | '(' COMPILES stmts ')'              -> ^(COMPILES stmts)
  | tuple
  | handler
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

tuple : '(' e ( AS  t    ')'        -> ^(TYANNOT e t)
                  | (',' e)* ')' hashq  -> ^(TUPLE hashq e+)  // tuples (products) (sugar: (a,b,c) == Tuple3 a b c)
                  )
      ;

hashq : '#'?;

handler : HANDLE action=e
          effmatch*
          (AS xform=e)?
          'end'                         -> ^(HANDLE $action ^(MU effmatch*) ^(MU $xform));
 
effmatch : OF patside '->' stmts        -> ^(CASE patside stmts);

pmatch  : p ('if' e)? '->' stmts -> ^(CASE p e stmts);

p : patside (('or' patside)+  -> ^(OR patside+)
             |                -> patside
            );

// Example: ($C _ ($C2 3 x), $C3, 0).
patside
  : dctor patom*  -> ^(CTOR dctor patom*)
  | patom         -> ^(MU   patom);

patom :
    x                                      // variables
  | '_'                  -> ^(WILDCARD)    // wildcards
  | lit
  | '(' ')'              -> ^(TUPLE)
  | '(' p (',' p)* ')'   -> ^(TUPLE p+)    // tuples (products)
  ;

lit     : num | str | TRU -> ^(BOOL TRU) | FLS -> ^(BOOL FLS);

ifexpr : 'if' cond=stmts 'then' thenpart=stmts ('else' elsepart=stmts)? 'end'
          -> ^(IF $cond $thenpart $elsepart);

formal   : pid (':' t)?  -> ^(FORMAL pid t);
tyformal : aid (':' k)?  -> ^(TYPEVAR_DECL aid k);
tyformalr: '(' aid ':' k ')' -> ^(TYPEVAR_DECL aid k);

////////////////////////////////////////////////////////////////////////////////

// "refined type"
t  : '%' xid ':' tp ':' e -> ^(REFINED xid tp e)
   | tp;

tp // "type phrase"
  : tatom (            -> ^(TYPE_ATOM    tatom)        // atomic types
          | tatom+     -> ^(TYPE_TYP_APP tatom tatom+) // type-level application
          )
  | 'forall' tyformalr+ t  -> ^(FORALL_TYPE tyformalr+ t) // description of terms indexed by types;
  ;

minusq : '-' ? ;
single_effect : minusq a tatom* -> ^(EFFECT_SINGLE minusq a tatom*);

effect : '@' (  a      -> ^(EFFECT_SINGLE a)
             | '(' ')' -> ^(EFFECT_ROW)
             | '('
                  single_effect (',' single_effect)*
                  (
                              -> ^(EFFECT_ROW ^(MU single_effect+) )
                  | '|' aid?  -> ^(EFFECT_ROW ^(MU single_effect+) ^(MU aid? ))
                  )
               ')' );
tatom :
    a                                                   // type variables
  | '??' a                              -> ^(TYPE_PLACEHOLDER a)
  | '(' ')'                             -> ^(TUPLE)
  | '(' t (',' t)* ')' hashq            -> ^(TUPLE hashq t+)  // tuples (products) (sugar: (a,b,c) == Tuple3 a b c)
  |
    '{' t  ('=>' t)* effect? '}'
   ('@' '{' tannots '}')?               -> ^(FUNC_TYPE ^(TUPLE t+) ^(MU effect?) tannots?)  // description of terms indexed by terms
//      | ':{'        (a ':' k '->')+ t '}'     -> ^(TYPE_TYP_ABS a k t)        // type-level abstractions
//  | tctor                                -> ^(TYPE_CTOR tctor)                  // type constructor constant
  // The dollar sign is required to distinguish type constructors
  // from type variables, since we don't use upper/lower case to distinguish.
  ;

tannots   : tabinding (',' tabinding)* -> ^(BINDING tabinding+);
tabinding : x '=' e                    -> ^(BINDING x e);

////////////////////////////////////////////////////////////////////////////////

// Numbers are things like:
//    1
//    -2
//    1234
//    0b10101011
//    0b`1011`1011
//    0xFEEDFACE
//    12.34
//    12.34`56
//    12.34e+01
//    12.34e-10
//    0x1.2p3
//    0xe
//    1e4

num : NUM -> ^(LIT_NUM NUM);
NUM			:  ('+'|'-')?
               (DIGIT         DIGIT*     ('`' DIGIT+   )* ( '.' DIGIT*     ('`' DIGIT+)*     )? SCI_NOTATION?
               |'0' ('x'|'b') HEX_CLUMP? ('`' HEX_CLUMP)* ( '.' HEX_CLUMP* ('`' HEX_CLUMP+)* )?
               );
fragment SCI_NOTATION	: ('e'|'E') ('+'|'-')? DIGIT+;
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
fragment IDENT_CONTINUE    : (DIGIT | WORD_CHAR | IDENT_SYMBOL_CONTINUE);
// Meanwhile, symbols start with a non-numeric, non-alphabetic glyph.
// We must play some tricks here to ensure that '=' is a keyword, not a symbol.
// Also, +Int32 is a symbol, but +2 is not.
SYMBOL    :    SYMBOL_COMMON
          |    '|' (AFTER_PIPE SYMBOL_CONTINUE*)?
          |    SYMBOL_MULTI_START   SYMBOL_CONTINUE_NDIG   SYMBOL_CONTINUE*;

fragment SYMBOL_CONTINUE        :(SYMBOL_CONTINUE_NDIG | DIGIT);
fragment SYMBOL_CONTINUE_NDIG   :('/' | '^' | WORD_CHAR | IDENT_SYMBOL_CONTINUE);

fragment SYMBOL_MULTI_START  : '=' | SYMBOL_COMMON;

fragment SYMBOL_COMMON :
    '!' | '>' | '<' | '-'
        | '?' | '+' | '*';

fragment IDENT_SYMBOL_CONTINUE   : '_' | SYMBOL_MULTI_START;
// Note: AFTER_PIPE is SYMBOL_CONTINUE_NDIG, minus WORD_CHAR
fragment AFTER_PIPE : IDENT_SYMBOL_CONTINUE | '/' | '^';

TICK  : '\'';
TRTK  : '\'\'\''; // triple-tick
DQUO  : '"'; // double-quote
TDQU  : '"""'; // triple double-quote
BACKSLASH : '\\';

str :
        s=TICK_STR -> ^(STRING TICK $s)
      | s=DQUO_STR -> ^(STRING DQUO $s)
      | s=TDQU_STR -> ^(STRING TDQU $s)
      | s=TRTK_STR -> ^(STRING TRTK $s)
      ;

TICK_STR : STR_TAG? TICK TICK_STR_CONTENTS TICK;
DQUO_STR : STR_TAG? DQUO DQUO_STR_CONTENTS DQUO;
TDQU_STR : STR_TAG? TDQU (options {greedy=false;} : (.))* TDQU;
TRTK_STR : STR_TAG? TRTK (options {greedy=false;} : (.))* TRTK;

fragment STR_TAG : 'r' | 'b';
fragment TICK_STR_CONTENTS : (~(BACKSLASH|TICK))* ( ESC_SEQ (~(BACKSLASH|TICK)*) )* ;
fragment DQUO_STR_CONTENTS : (~(BACKSLASH|DQUO))* ( ESC_SEQ (~(BACKSLASH|DQUO)*) )* ;


// TODO single-mark strings should not contain newlines,
// but to give better error messages, we delay checking
// until post-processing.

// Escape sequences are limited to \n, \t, \r, \", \', \\, and \u...
// ... but the lexer is over-permissive because lexer errors are nasty.
// Anyhow, raw strings don't have the restriction on what comes after backslash.
ESC_SEQ        : BACKSLASH (~('u'|'x'))
               | BACKSLASH 'u' '{' UNICODE_INNER* '}'
               | BACKSLASH 'x' HEX_DIGIT HEX_DIGIT;

// Examples of Unicode escape sequences:
//      \u{00}
//      \u{00b1}
//      \u{Plus-minus sign}     // U+00B1
// Non-examples (lexically)
//      \u{&&}          -- invalid char in escape
// Non-examples (post-processing)
//      \u{}            -- need at least two
//      \u{0}           -- need at least two
//      \u{12345789}    -- too long
//      \u{foobity}     -- no such escape!
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



