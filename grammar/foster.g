grammar foster;

options {
  //language = C;
  output = AST;
}

tokens {
	AS='as'; AT='at'; DO='do'; ID='id'; IF='if'; IN='in'; IS='is'; IT='it'; TO='to';
	FOR='for'; NIL='nil'; TRUE='true'; FALSE='false'; AND='and'; OR='or';
	// __compiles
}

program			:	exp+ EOF;

fn			:	'fn' (idlist ('to' idlist)?)? seq requires? ensures?;
requires		:	'given' seq;
ensures			:	'gives' seq;
num			:	int_num | rat_num;
idlist			:	IDENT+ | '(' IDENT (','? IDENT)* ')';


literal			:	TRUE | FALSE | num;


exp			:	(literal | fn | prefixexp | seq | prefix_unop exp) (binop exp)*;


prefixexp		:	IDENT;

seq			:	'{' fieldlist? '}';
fieldlist		:	field (fieldsep field)* fieldsep;
field			:	'[' exp ']' '=' exp | IDENT '=' exp | exp;
fieldsep		:	(',' | ';')?;

binop			:	'+' | '-' | '*' | '/' | '..'
			|	'<' | '<=' | '>=' | '>' | '==' | '!='
			|	AND | OR | '+=' | '-=' | '*=' | '/=';
			
prefix_unop		:	'-' | 'not';


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

STRING
    :  '\'' ( ESC_SEQ | ~('\\'|'\'') )* '\''
    |  '"'  ( ESC_SEQ | ~('\\'|'"' ) )* '"'
    ;
    
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
