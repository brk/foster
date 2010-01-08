grammar foster;

options {
  // Commenting out this line lets us play with the grammar in ANTLRworks,
  // and still automatically generate a C-language parser via CMake and Python.
  //language = C;
  output = AST;
}

tokens {
	AS='as'; AT='at'; DO='do'; ID='id'; IF='if'; IN='in'; IS='is'; IT='it'; TO='to';
	FOR='for'; NIL='nil'; TRUE='true'; FALSE='false'; AND='and'; OR='or';
	COMPILES='__COMPILES__';

	FN; OUT; BODY; GIVEN; GIVES; IDS; SEQ; FIELD_LIST; INT; RAT; EXPRS; NAME;
	TRAILERS; CALL; TUPLE; SUBSCRIPT; LOOKUP; FORMAL; ARRAY;
}

program			:	expr+ EOF -> ^(EXPRS expr+);

fn			:	'fn' n=str? in=formals? ('to' out=formals)? seq requires? ensures?
					-> ^(FN ^(NAME $n) ^(IN $in) ^(OUT $out) ^(BODY seq) ^(GIVEN requires?) ^(GIVES ensures?));
requires		:	'given' seq;
ensures			:	'gives' seq;
num			:	( int_num -> ^(INT int_num)
				| rat_num -> ^(RAT rat_num));
formal                  :        i=IDENT (':' t=expr) -> ^(FORMAL $i $t); 	
formals			:	(      formal+
				 | '(' formal (','? formal)* ')'
				) -> formal*;

literal			:	TRUE | FALSE | num | tuple | array;
name			:	n=IDENT -> ^(NAME $n);
str	                :       STR;
tuple	                :       'tuple' seq -> ^(TUPLE seq);
array                   :       'array' seq -> ^(ARRAY seq);	

ifexpr                  :       'if' cond=expr thenseq=seq 'else' elseseq=seq
					-> ^(IF $cond $thenseq $elseseq);

term			:	( literal
				| name
                                | fn
                                | seq
                                | ifexpr
                                | unop_prefixed_expr);

compound                :       term ( trailer -> ^(TRAILERS term trailer)
                                      |        -> ^(term)
                                );	
//opt_paren_expr          :      ('(' expr ')' | expr)	-> expr;

// Defining expr : '(' expr ')' | ... ; creates abiguity with call expressions
expr			:	compound (  binop expr	-> ^(binop compound expr)
					  |		-> ^(compound)
				);

trailer                 :       '(' arglist? ')' -> ^(CALL arglist)
                        |       '.' name         -> ^(LOOKUP name)
	                |	'[' literal ']'  -> ^(SUBSCRIPT literal);

arglist                 :       expr (',' expr)*;

seq			:	'{' fieldlist? '}' -> ^(SEQ fieldlist);
fieldlist		:	field (fieldsep field)* fieldsep? -> ^(FIELD_LIST field*);
field			:	'[' expr ']' ':' expr | name ':' expr | expr;
fieldsep		:	';' | ',';

binop			:	'+' | '-' | '*' | '/' | '..' | '='
			|	'<' | '<=' | '>=' | '>' | '==' | '!='
			|	'bitand' | 'bitor' | 'shl' | 'shr'
			|	AND | OR | '+=' | '-=' | '*=' | '/=';

unop_prefixed_expr      :       prefix_unop expr -> ^(prefix_unop expr);	
prefix_unop		:	'-' | 'not' | COMPILES;


// TODO: sema should warn  if int_num starts with zero and doesn't include a base
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
				| '/' | '~' );

// Very weird: for some reason, the default ANTLR string RE
// fails on strings that contain but do not start with an escape sequence,
// requiring the non-escape-sequence character class to be explicitly duplicated.
STR
    :  '\'' ~('\\'|'\'')* ( ESC_SEQ | ~('\\'|'\'') )* '\''
    |  '"'  ~('\\'|'"' )* ( ESC_SEQ | ~('\\'|'"' ) )* '"'
    ;

COMMENT			:	'//' ~('\n'|'\r')* '\r'? '\n' {$channel=HIDDEN;} ;

fragment ESC_SEQ	:	'\\' ('t'|'n'|'r'|'"'|'\''|'\\') | UNICODE_ESC;
fragment UNICODE_ESC    :	'\\' ('u' | 'U') HEX_DIGIT HEX_DIGIT HEX_DIGIT HEX_DIGIT;
fragment HEX_DIGIT 	: 	('0'..'9'|'a'..'f'|'A'..'F');

WS  :   ( ' '
        | '\t'
        | '\r'
        | '\n'
        ) {$channel=HIDDEN;}
    ;
