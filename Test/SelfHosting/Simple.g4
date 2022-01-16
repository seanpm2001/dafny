grammar Simple;
options { language=CSharp; }

prog : (s+=stmt ';')*;

stmt : 'print' '(' e=expr ')' # Print;

expr : c=INT # Const
     | l=expr '+' r=expr # Add;

INT  : [0-9]+;
WS   : [ \t\n\r]+ -> skip;


