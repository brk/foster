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
	COMPILES='__COMPILES__'; UNPACK='unpack'; STRUCTURE='struct';

	FN; OUT; BODY; GIVEN; GIVES; SEQ; INT; RAT; EXPRS; NAME; CTOR;
	TRAILERS; CALL; TUPLE; SUBSCRIPT; LOOKUP; FORMAL; ARRAY; SIMD;
}

program			:	nl* expr (nl+ expr)* nl* EOF -> ^(EXPRS expr+);

fn			:	'fn' n=str? in=formals? ('to' out=formals)? seq requires? ensures?
					-> ^(FN ^(NAME $n) ^(IN $in) ^(OUT $out) ^(BODY seq) ^(GIVEN requires?) ^(GIVES ensures?));
requires		:	'given' seq;
ensures			:	'gives' seq;

formals			:	/* names */ comma_sep_formals;

names			:	'(' comma_sep_names ')' | comma_sep_names;
comma_sep_names		:	name (',' name)* -> name+;
comma_sep_formals	:	'(' formal (',' formal)* ')' -> formal+;
formal                  :        i=name (':' t=typeexpr) -> ^(FORMAL $i $t); 	


num			:	( int_num -> ^(INT int_num)
				| rat_num -> ^(RAT rat_num));
				
literal			:	TRUE | FALSE | num;
name			:	n=IDENT -> ^(NAME $n);
str	                :       STR;

name_or_ctor		:	name (seq -> ^(CTOR name seq)
				        |   -> name);

ifexpr                  :       'if' cond=expr 'then' thenpart=expr 'else' elsepart=expr
					-> ^(IF $cond $thenpart $elsepart);
					
custom_terms		:	'(' expr ')' -> expr
                                | prefix_unop nl? expr -> ^(prefix_unop expr);
                                
term			:	( literal
				| fn
				| seq
				| ifexpr
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

type_of_type	:	name 'of' typeexpr 'to'? typeexpr  -> ^(CTOR name ^(SEQ typeexpr+));
typeexpr	:	literal | name_or_ctor | custom_terms | type_of_type;

trailer                 :       '(' arglist? ')' -> ^(CALL arglist)
                        |       '.' name         -> ^(LOOKUP name)
	                |	'[' literal ']'  -> ^(SUBSCRIPT literal);

arglist                 :       expr (',' nl? expr)* -> expr+;

seq			:	'{' nl* exprlist? nl* '}' -> ^(SEQ exprlist);
exprlist        :       expr ((sep | nl) nl* expr)* sep? -> expr+;
sep		:	';' | ',';

binop			:	'+' | '-' | '*' | '/' | '..' | '='
			|	'<' | '<=' | '>=' | '>' | '==' | '!='
			|	'bitand' | 'bitor' | 'bitxor' | 'shl' | 'lshr' | 'ashr'
			|	AND | OR | '+=' | '-=' | '*=' | '/=';

prefix_unop		:	'-' | 'not' | COMPILES | UNPACK;

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

COMMENT			:	'//' ~('\n'|'\r')* '\r'?  /*'\n'*/ {$channel=HIDDEN;} ;

fragment ESC_SEQ	:	'\\' ('t'|'n'|'r'|'"'|'\''|'\\') | UNICODE_ESC;
fragment UNICODE_ESC    :	'\\' ('u' | 'U') HEX_DIGIT HEX_DIGIT HEX_DIGIT HEX_DIGIT;
fragment HEX_DIGIT 	: 	('0'..'9'|'a'..'f'|'A'..'F');

NEWLINE : '\n';
WS  :   ( ' '
        | '\t'
        | '\r'
        ) {$channel=HIDDEN;}
    ;
