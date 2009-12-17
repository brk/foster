grammar foster;

/*
options {
	language = Python;
}
*/

tokens {
	AS='as'; AT='at'; DO='do'; ID='id'; IF='if'; IN='in'; IS='is'; TO='to';
	FOR='for'; NIL='nil'; TRUE='true'; FALSE='false'; AND='and'; OR='or';
	// __compiles
}

program			:	exp EOF;

fn			:	'fn' (idlist ('to' idlist)?)? seq requires? ensures?;
requires		:	'requires' seq;
ensures			:	'ensures' seq;
num			:	int_num | rat_num;
idlist			:	IDENT+ | '(' IDENT (','? IDENT)* ')';

exp			:	(NIL | FALSE | TRUE | num | STRING | fn | prefixexp | seq | prefix_unop exp) (binop exp | postfix_unop)*;
//exp			:	(NIL | FALSE | TRUE | num | STRING | fn | prefixexp | seq | exp binop exp | prefix_unop exp | exp postfix_unop;

STRING
    :  '\'' ( ESC_SEQ | ~('\\'|'\'') )* '\''
    |  '"'  ( ESC_SEQ | ~('\\'|'"' ) )* '"'
    ;
/*
prefixexp		:	prefixexp '.' IDENT | prefixexp '[' exp ']' // var
			|	prefixexp args | prefixexp ':' IDENT args // funcall
			|	'(' exp ')';
*/

prefixexp		:	'(' exp ')'    ;//  ('.' IDENT | '[' exp ']' | args | ':' IDENT args)*;

//args			:	'(' explist? ')' | seq | STRING;

//explist			:	exp (',' exp)*;
/*
paramlist		:	namelist? '...'?;
namelist		:	IDENT (','? IDENT)*;
*/
seq			:	'{' fieldlist? '}';
fieldlist		:	field (fieldsep field)* fieldsep;
field			:	'[' exp ']' '=' exp | IDENT '=' exp | exp;
fieldsep		:	(',' | ';')?;

binop			:	'+' | '-' | '*' | '/' | '..'
			|	'<' | '<=' | '>=' | '>' | '==' | '!='
			|	AND | OR | '+=' | '-=' | '*=' | '/=';
			
prefix_unop		:	'-' | 'not' | '#';
postfix_unop		:	'^';


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

COMMENT			:	'//' ~('\n'|'\r')* '\r'? '\n' {$channel=HIDDEN;} ;

fragment ESC_SEQ	:	'\\' ('t'|'n'|'r'|'\"'|'\''|'\\') | UNICODE_ESC;
fragment UNICODE_ESC    :	'\\' ('u' | 'U') HEX_DIGIT HEX_DIGIT HEX_DIGIT HEX_DIGIT;
fragment HEX_DIGIT 	: 	'0'..'9'|'a'..'f'|'A'..'F';

WS  :   ( ' '
        | '\t'
        | '\r'
        | '\n'
        ) {$channel=HIDDEN;}
    ;