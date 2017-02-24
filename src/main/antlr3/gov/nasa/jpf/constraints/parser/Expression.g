grammar Expression;

options {
  output=AST;
  ASTLabelType=CommonTree;
  backtrack=true;
}

tokens {
	QUANTIFIER_VAR_LIST;
	QUANTIFIER_VAR;
	TYPED_VAR;
	TYPED_VAR_LIST;
	UNARY_MINUS;
	UNARY_PLUS;
	TYPE_CAST;
	BVXOR;
	ROOT;
}

@header {
package gov.nasa.jpf.constraints.parser;
}



@lexer::header {
package gov.nasa.jpf.constraints.parser;
}

start
	: (root_lexpression | root_declare_stmt ) EOF!
	;

start_aexpression
	: root_aexpression EOF!;

start_variable
	: root_variable EOF!;

root_declare_stmt
	: declare_var_list -> ^(ROOT declare_var_list)
	;
declare_var_list
	: DECLARE! typed_var_list
	;
	
root_lexpression
	: declare_stmt? lexpression -> ^(ROOT declare_stmt? lexpression)
	;
	
root_aexpression
	: declare_stmt? aexpression -> ^(ROOT declare_stmt? aexpression)
	;

root_variable
	: typed_var -> ^(ROOT typed_var)
	;

declare_stmt
	:	DECLARE! typed_var_list IN!
	;

	
lexpression
    : lexpr_quantifier
    ;

	
lexpr_quantifier
	: (FORALL | EXISTS)^ LPAREN! quantifier_var_list RPAREN! COLON! lexpr_quantifier
	| lexpr_cmp
	;
	
lexpr_cmp:
	lexpr_or ((LIMP|LEQ)^ lexpr_or)*
	;
	
lexpr_or
	: lexpr_and (LOR^ lexpr_and)*
	;
	
lexpr_and
	: lexpr_xor (LAND^ lexpr_xor)*
	;
	
lexpr_xor
	: lexpr_unary (LXOR^ lexpr_unary)*
	;
	
lexpr_unary
	: LNOT^ lexpr_unary
	| lexpr_atomic;
	
lexpr_atomic
	: (TRUE|FALSE)^
	| aexpression ((EQ|NE|LE|LT|GE|GT)^ aexpression)?
	| aexpression ((EQ|NE)^ (TRUE|FALSE))
	;
	
aexpression
	: aexpr_bvor;
	
aexpr_bvor
	: aexpr_bvxor (BVOR^ aexpr_bvxor)*
	;

aexpr_bvxor
	: aexpr_bvand (LXOR aexpr_bvand)+ -> ^(BVXOR aexpr_bvand*)
	| aexpr_bvand
	;
	
aexpr_bvand
	: aexpr_bvshift (BVAND^ aexpr_bvshift)*
	;
	
aexpr_bvshift
	: aexpr_add ((BVSHL|BVSHR|BVSHUR)^ aexpr_add)*
	;
	
aexpr_add
	: aexpr_mul ((ADD|SUB)^ aexpr_mul)*
	;

aexpr_mul
	: aexpr_unary ((MUL|DIV|REM)^ aexpr_unary)*
	;

aexpr_unary
	: SUB aexpr_unary -> ^(UNARY_MINUS aexpr_unary)
	| ADD aexpr_unary -> ^(UNARY_PLUS aexpr_unary)
	| BVNEG^ aexpr_unary
	| LPAREN ID RPAREN aexpr_unary -> ^(TYPE_CAST ID aexpr_unary)
	| aexpr_atomic
	;
	
aexpr_atomic
	: aexpr_literal
	| identifier
	| LPAREN! lexpression RPAREN!
	;

aexpr_literal
	: (BYTE_LITERAL|SHORT_LITERAL|INT_LITERAL|LONG_LITERAL|BIGINT_LITERAL|FLOAT_LITERAL|DOUBLE_LITERAL|BIGDECIMAL_LITERAL)^
	;
	            
    
identifier
	:	ID^
	|	QID^;
        
typed_var
    : identifier COLON ID -> ^(TYPED_VAR identifier ID)
    ;

quantifier_var
	:	identifier COLON ID -> ^(TYPED_VAR identifier ID)
	| identifier -> ^(QUANTIFIER_VAR identifier)
	;
	
quantifier_var_list
	: quantifier_var (COMMA quantifier_var)* -> ^(QUANTIFIER_VAR_LIST quantifier_var+)
	;

typed_var_list
	: typed_var (COMMA typed_var)* -> ^(TYPED_VAR_LIST typed_var+)
	;
	

DECLARE	:	'declare';
IN	:	'in';

LPAREN 	: '(';
RPAREN 	: ')';

COLON	: ':';
COMMA	: ',';

EQ  : '==';
NE  : '!=';
GE  : '>=';
LE  : '<=';
GT  : '>';
LT  : '<';


LAND : '&&';
LOR  : '||';
LNOT  : '!';
LIMP	: '->';
LEQ	: '<->';
LXOR	: '^';

ADD : '+';
SUB : '-';
MUL : '*';
DIV : '/';
REM : '%';

BVSHL	:	'<<';
BVSHR	:	'>>';
BVSHUR	:	'>>>';

BVNEG	:	'~';
BVAND	:	'&';
BVOR	:	'|';

TRUE  : 'true'
      ;

FALSE : 'false'
      ;
      
FORALL 	: 'forall'
	;
	
EXISTS	: 'exists'
	;
	
	
	
ID  :	('a'..'z'|'A'..'Z'|'_') ('a'..'z'|'A'..'Z'|'0'..'9'|'_'|'.')*
    ;

fragment NZDIGIT
	:	'1'..'9';
	
fragment DIGIT
	:	'0'|NZDIGIT;

fragment INTEGER
	:	('0'|NZDIGIT DIGIT*);
	
BYTE_LITERAL
	:	INTEGER 'b';
	
SHORT_LITERAL
	:	INTEGER 's';
	
INT_LITERAL
	:	INTEGER;
	
LONG_LITERAL
	:	INTEGER 'L';
	
BIGINT_LITERAL
	:	INTEGER 'I';
	

fragment DECIMAL
	:	INTEGER? '.' DIGIT+;
	
fragment REAL	:	(INTEGER|DECIMAL) EXPONENT?;


	
FLOAT_LITERAL
	:	REAL 'f';
	
DOUBLE_LITERAL
	:	REAL 'd';
	
BIGDECIMAL_LITERAL
	:	REAL;
	


    
fragment QUOTE
            :   '\'';
fragment SPACE
            :   (' '|'\r'|'\t'|'\u000C'|'\n');

WS      :   SPACE+ {$channel=HIDDEN;};
QID  :   QUOTE (options {greedy=false;} : . )* QUOTE;
    	


fragment
EXPONENT : ('e'|'E') ('+'|'-')? ('0'..'9')+ ;