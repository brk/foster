%token <int> INT
%token NUM STR
%token SARROW DARROW
%token LPAREN RPAREN
%token LCURLY RCURLY
%token LBRACK RBRACK
%token CARET BANG BACKTICK HASH PERCENT EQUAL COMMA UNDERSCORE SEMI COLON DCOLON DOLLAR
%token SYMBOL OPRNAME
%token SMALLIDENT UPPERIDENT UNDERIDENT
%token CASE END OF OR IF AS THEN ELSE LET REC INCLUDE
%token TYPE EFFECT FOREIGN IMPORT COMPILES PRIM FORALL HANDLE
%token EOF

%start <unit> transunit

%%

transunit:
  | imports* item* EOF {()}

imports:
  | INCLUDE SEMI {()}

item:
  | x DCOLON t      SEMI {()}
  | x EQUAL  phrase SEMI {()}
  | TYPE CASE tyformal  parens(tyformal)*   datactor* SEMI {()}
  | EFFECT    tyformal  parens(tyformal)* effectctor* SEMI {()}
  | FOREIGN IMPORT x asid? DCOLON t SEMI {()}
  | FOREIGN TYPE  tyformal SEMI {()}

asid: AS id {()}

datactor:
  | OF dctor tatom* {()}

effectctor:
  | OF dctor tatom* preceded(DARROW, t)? {()}

dctor:
  | DOLLAR ctor  {()}

ctor:
  | x {()}

parens(thing):
  | LPAREN thing RPAREN {()}

x: id {()}
a: id {()}
pid: id {()}

xid:
  | id {()}
  | OPRNAME {()}

id:
  | SMALLIDENT {()}
  | UPPERIDENT {()}
  | UNDERIDENT {()}

stmts: stmt_start stmt_cont* {()}
stmt_start:
  | REC pbinding {()}
  | ext_pbinding {()}
stmt_cont:
  | SEMI stmt_start? {()}

ext_pbinding:
  | e              {()}
  | e      EQUAL e {()}
  | patlhs EQUAL e {()}

pbinding:
  | patbind EQUAL e {()}

patbind:
  | xid {()}
  | patlhs {()}

patlhs:
  | UNDERSCORE {()}
  | LET LPAREN separated_list(COMMA, p) RPAREN {()}



e:
  |        phrase binops? {()}
  | SYMBOL phrase binops? {()}

binops: binop_phrase+ {()}
binop:
  | SYMBOL {()}
  | BACKTICK x BACKTICK {()}

binop_phrase: binop phrase {()}

phrase:
  | lvalue+ {()}
  | PRIM nopr lvalue* {()}

nopr:
  | x {()}
  | SYMBOL {()}

lvalue: atom suffix* {()}

suffix:
  | CARET {()}
  | LBRACK e RBRACK {()}
  | BANG {()}

atom:
  | x {()}
  | lit {()}
  | ifexpr {()}
  | CASE e of_pmatch+ END {()}
  | LPAREN RPAREN {()}
  | LPAREN COMPILES stmts RPAREN {()}
  | tuple {()}
  | handler {()}
  | valabs {()}

valabs:
  | LCURLY foralls? formals stmts? RCURLY {()}

formals:
  |                       {()}
  | formals formal DARROW {()}

foralls: FORALL tyformal* COMMA {()}

formal:
  | pid         {()}
  | pid COLON t {()}

handler:
  | HANDLE e effmatch*      END {()}
  | HANDLE e effmatch* AS e END {()}

effmatch:
  | OF patside SARROW stmts {()}

of_pmatch:
  | OF pmatch {()}

pmatch:
  | p      SARROW stmts {()}
  | p IF e SARROW stmts {()}

tuple:
  | LPAREN stmts AS t RPAREN {()}
  | LPAREN stmts comma_e* RPAREN hash? {()}

comma_e: COMMA e {()}
hash: HASH {()}

p:
  | patside orpatside+ {()}
  | patside {()}

patside:
  | dctor patom* {()}
  | patom {()}

orpatside: OR patside {()}

patom:
  | x {()}
  | UNDERSCORE {()}
  | lit {()}
  | LPAREN RPAREN {()}
  | LPAREN separated_nonempty_list(COMMA, p) RPAREN {()}

lit:
  | NUM {()}
  | STR {()}

ifexpr:
  | IF stmts THEN stmts ELSE stmts END {()}
  | IF stmts THEN stmts            END {()}

tyformal:
  | x colonkind? {()}

colonkind: COLON kind {()}

kind:
  | x {()}

t:
  | PERCENT x COLON tp COLON e {()}
  | tp {()}

tp:
  | tatom tatom+ {()}
  | tatom {()}

tatom:
  | a {()}
  | LPAREN RPAREN {()}
  | LPAREN separated_nonempty_list(COMMA, t) RPAREN hash? {()}
  | LCURLY separated_nonempty_list(DARROW, t) RCURLY {()}


