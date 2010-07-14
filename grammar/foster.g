grammar foster;

options {
  // Leaving this line commented out lets us play with the grammar in ANTLRworks
  // and still automatically generate a C-language parser via CMake and Python.
  //language = C;
  output = AST;
}

tokens {
	AS='as'; AT='at'; DO='do'; ID='id'; IF='if'; IN='in'; IS='is'; IT='it'; TO='to';
	FOR='for'; NIL='nil'; TRUE='true'; FALSE='false'; AND='and'; OR='or';
	COMPILES='__COMPILES__'; STRUCTURE='struct';

	FN; OUT; BODY; GIVEN; GIVES; SEQ; INT; RAT; EXPRS; NAME; CTOR;
	TRAILERS; CALL; TUPLE; SUBSCRIPT; LOOKUP; FORMAL; ARRAY; SIMD;
	LETEXPR; SETEXPR; PARENEXPR; TYPEDEFN; FNDEF; FORRANGE;
	}

program			:	nl* toplevelexpr (nl+ toplevelexpr)* nl* EOF -> ^(EXPRS toplevelexpr+);

fn			:	'fn' n=str? '(' in=formals? ('to' out=typeexpr)? ')' seq? requires? ensures?
					-> ^(FN ^(NAME $n) ^(IN $in) ^(OUT $out) ^(BODY seq) ^(GIVEN requires?) ^(GIVES ensures?));
requires		:	'given' seq;
ensures			:	'gives' seq;

//names			:	name (',' name)* -> name+;
formals			:	formal (',' formal)* -> formal+;
formal                		:	i=name t=typeinscription? -> ^(FORMAL $i $t); 	
typeinscription		:	':' typeexpr -> typeexpr;


num			:	( int_num -> ^(INT int_num)
				| rat_num -> ^(RAT rat_num));
				
literal			:	TRUE | FALSE | num;
name			:	n=IDENT -> ^(NAME $n);
str	                :       STR;

nil	:	NIL;

// name seq?
name_or_ctor		:	name (seq -> ^(CTOR name seq)
				        |   -> name);

forrange	:	FOR var=name IN start=expr TO end=expr ('by' incr=expr)? DO body=expr nl? -> ^(FORRANGE $var $start $end $body $incr);

// lhs = ident or LOOKUP or SUBSCRIPT but not CALL
setexpr	:	'set' lhs=compound '=' rhs=expr -> ^(SETEXPR $lhs $rhs);

letexpr	:	'let' formal '=' arg=expr 
			( ((nl | ';') next=letexpr) 
			| ('in') body=seq typeinscription?) -> ^(LETEXPR formal $arg $body $next typeinscription);
ifexpr                  :       'if' cond=expr 'then' thenpart=expr 'else' elsepart=expr
					-> ^(IF $cond $thenpart $elsepart);
					
custom_terms		:	parenexpr
                                | prefix_unop nl? expr -> ^(prefix_unop expr);
parenexpr	:	'(' expr ')' -> ^(PARENEXPR expr);

sugarterm	:	letexpr;

term			:	( literal
				| fn
				| nil
				| seq
				| ifexpr
				| setexpr
				| forrange
				| sugarterm
				| name_or_ctor
				| custom_terms
                                );

compound                :       (term) ( trailer+ -> ^(TRAILERS term trailer+)
                                      |        -> ^(term)
                                );	

subexpr			:	compound (  binop nl? subexpr	-> ^(binop compound subexpr)
					  |		-> ^(compound)
				);
expr	:	subexpr;

fndef 	:	 name '=' fn -> ^(FNDEF name fn);
toplevelexpr : fndef | typedefn | fn;
typedefn : 'type' name '=' typeexpr -> ^(TYPEDEFN name typeexpr);

type_of_type	:	name 'of' typeexpr 'to'? typeexpr  -> ^(CTOR name ^(SEQ typeexpr+));
typeexpr	:	literal | name_or_ctor | custom_terms | type_of_type | fn;

trailer                 :       '(' arglist? ')' -> ^(CALL arglist)
                        |       '.' name         -> ^(LOOKUP name)
	                |	'[' literal ']'  -> ^(SUBSCRIPT literal);

arglist                 :       expr (',' nl? expr)* -> expr+;

seq			:	'{' nl* exprlist? nl* '}' -> ^(SEQ exprlist);
exprlist        :       expr ((sep | nl) nl* expr)* sep? -> expr+;
sep		:	';' | ','; // semicolon or comma

binop			:	'+' | '-' | '*' | '/' | '..'
			|	'<' | '<=' | '>=' | '>' | '==' | '!='
			|	AND | OR | '+=' | '-=' | '*=' | '/=';

REF	:	'ref' | '?ref';
prefix_unop		:	'-' | 'not' | 'new' | REF | COMPILES;

nl : NEWLINE;


// TODO: sema should warn if int_num starts with zero and doesn't include a base
// TODO: sema should error if int_num contains hex digits without specifying a hex base
// TODO: sema should error if hex_clump contains non_hex chars
int_num			:	num_start                                ('_' hex_clump)?;
rat_num			:	num_start '.' hex_clump ('`' hex_clump)* ('_' hex_clump)?;
num_start		:	DIGIT_HEX_CLUMP         ('`' hex_clump)*;
hex_clump		:	DIGIT_HEX_CLUMP | IDENT;
DIGIT_HEX_CLUMP		:	('0'..'9') HEX_DIGIT*;

IDENT			:	IDENT_START IDENT_CONTINUE*;
fragment IDENT_START		: 'a'..'z' | 'A'..'Z';
fragment IDENT_CONTINUE		:('a'..'z' | 'A'..'Z' | '0'..'9'
				| '_' | '!' | '$'
				| '>' | '<' | '='
				| '?' | '+' | '*'
				| '/' | '~' | '-');

// Very weird: for some reason, the default ANTLR string RE
// fails on strings that contain but do not start with an escape sequence,
// requiring the non-escape-sequence character class to be explicitly duplicated.
STR
    :  '\'' ~('\\'|'\'')* ( ESC_SEQ | ~('\\'|'\'') )* '\''
    |  '"'  ~('\\'|'"' )* ( ESC_SEQ | ~('\\'|'"' ) )* '"'
    ;

LINE_COMMENT	:	'//' ~('\n'|'\r')* '\r'? {$channel=HIDDEN;} ;
NESTING_COMMENT	:
		'/*' ( options {greedy=false;} :
		       NESTING_COMMENT | .
		      ) *
		'*/' {$channel=HIDDEN;}
		;


fragment ESC_SEQ	:	'\\' ('t'|'n'|'r'|'"'|'\''|'\\') | UNICODE_ESC;
fragment UNICODE_ESC    :	'\\' ('u' | 'U') HEX_DIGIT HEX_DIGIT HEX_DIGIT HEX_DIGIT;
fragment HEX_DIGIT 	: 	('0'..'9'|'a'..'f'|'A'..'F');

NEWLINE : '\n';
WS  :   ( ' '
        | '\t'
        | '\r'
        ) {$channel=HIDDEN;}
    ;
