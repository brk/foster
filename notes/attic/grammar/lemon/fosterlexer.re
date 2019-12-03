// For definitions of Token and Scanner
#include "fosterlexer.h"

// For token names, generated by lemon.
#include "parser.h"

#include <stdio.h>

// Macros for RE2C's so-called custom API.
#define   YYCTYPE     unsigned char
#define   YYMARKER    s->ptr

#define  YYCURSOR         s->cur

#define  YYPEEK()         s->buf[YYCURSOR]
#define  YYSKIP()         ++YYCURSOR
#define  YYBACKUP()       s->ptr = YYCURSOR
#define  YYBACKUPCTX()    YYCTXMARKER = YYCURSOR
#define  YYRESTORE()      YYCURSOR = s->ptr
#define  YYRESTORECTX()   YYCURSOR = YYCTXMARKER
#define  YYRESTORERAG(t)  YYCURSOR = t
#define  YYLESSTHAN(n)    (buff_end - s->cur) < n
#define  YYSTAGP(t)       t = s->cur
#define  YYSTAGN(t)       t = NULL

void makeToken(Token* t, int tok, Scanner* scanner) {
  t->tok = tok;
  t->line = scanner->line;
  t->col = scanner->top - scanner->linepos;
  if (t->col < 0) t->col = 0;
          //(scanner->top == scanner->linepos ? scanner->linepos_prev : scanner->linepos);
}

// mk(TOKENTYPE) initializes the scan() function's output Token.
#define mk(typ) makeToken(t, typ, s)

void saw_newline_at(Scanner* s, int pos) {
    s->line++;
    s->linepos_prev = s->linepos;
    s->linepos = pos;
}

void report_lexical_error(Scanner* s, Token* t, const char* msg, int buff_end) {
    int offset = s->cur - s->linepos;
    printf("While %s, unexpected character on line %d:\n", msg, s->line);
    int line_length = offset;
    while ((line_length < 82)
        && (s->linepos + line_length < buff_end)
        && (s->buf[s->linepos + line_length] != '\n')) { ++line_length; }

    fwrite(&s->buf[s->linepos], 1, line_length, stdout);
    if (line_length == 81) {
      printf("...\n"); // (probably) too much to display, show a prefix
    } else {
      printf("\n");
    }
    for (int i = 0; i < offset; ++i) { printf(" "); }
    printf("^\n");

    // TODO inspect characters around YYCURSOR, taking source location/msg
    // into account, to diagnose lexical errors, esp. malformed escape codes.

    s->num_errors++;
}

void scan_token_start(Scanner* s, Token* t, int buff_end, YYCTYPE* yych) {

regular:
  if (s->cur >= buff_end) { return mk(FINI); }
  s->top = s->cur;

/*!re2c
  re2c:yyfill:enable = 0;
  re2c:yych:emit = 0;
  re2c:variable:yych = '*yych';

  whitespace = [ \t\v\f]+;
  dig = [0-9];
  lower = [a-z];
  upper = [A-Z];
  let = [a-zA-Z_];
  hex = [a-fA-F0-9];
  any = [\000-\377];
  sign = "+" | "-";
  symbolcommon = [+*?<>!-];
  symmultistart = "=" | symbolcommon;
  identcontinue = dig | let | symmultistart;
  lowerid = lower identcontinue*;
  upperid = upper identcontinue*;
  underid = "_"   identcontinue*;
  hexclump = (dig hex*) | lowerid | upperid;
  scinotation = [eE] sign? dig+;

  strtag = [rb];

  unicodeinner = [a-zA-Z0-9_ +\-];
  backslash = [\\];
  escseq = backslash [^ux]
         | backslash "u" "{" unicodeinner* "}"
         | backslash "x" hex hex;

  tickstrcontents = [^\\']* (escseq [^\\']*)*;
  tick = "'";
  tickstr = strtag? tick tickstrcontents tick;

  dquostrcontents = [^\\"]* (escseq [^\\"]*)*;
  dquo = '"';
  dquostr = strtag? dquo dquostrcontents dquo;

  afterpipe = "/" | "^" | "_" | symmultistart;
  symbolcontinuendig = afterpipe | [a-zA-Z];
  symbolcontinue = symbolcontinuendig | dig;
  symbol = symbolcommon
         | "|" (afterpipe symbolcontinue*)?
         | symmultistart symbolcontinuendig symbolcontinue*;

  backtick = '`';
*/

/*!re2c
  "/*"                  { ++s->commentdepth; mk(BLOCKCOMMENT); goto comment; }
  "//"                  { mk(LINECOMMENT); goto linecomment; }
  '('                   { return mk(LPAREN); }
  ")"                   { return mk(RPAREN); }
  "{"                   { return mk(LCURLY); }
  "}"                   { return mk(RCURLY); }
  "["                   { return mk(LBRACK); }
  "]"                   { return mk(RBRACK); }
  ";"                   { return mk(SEMI); }
  ","                   { return mk(COMMA); }
  ":"                   { return mk(COLON); }
  "="                   { return mk(EQUAL); }
  "`"                   { return mk(BACKTICK); }
  "@"                   { return mk(HASH); }

  "$"                   { return mk(DOLLAR); }
  "%"                   { return mk(PERCENT); }
  "!"                   { return mk(BANG); }
  "^"                   { return mk(CARET); }
  "#"                   { return mk(HASH); }
  "_"                   { return mk(UNDERSCORE); }

  "=>"                  { return mk(DARROW); }
  "->"                  { return mk(SARROW); }

  "if"                  { return mk(IF); }
  "of"                  { return mk(OF); }
  "or"                  { return mk(OR); }
  "as"                  { return mk(AS); }
  "rec"                 { return mk(REC); }
  "let"                 { return mk(LET); }
  "end"                 { return mk(END); }
  "else"                { return mk(ELSE); }
  "type"                { return mk(TYPE); }
  "case"                { return mk(CASE); }
  "prim"                { return mk(PRIM); }
  "effect"              { return mk(EFFECT); }
  "handle"              { return mk(HANDLE); }
  "forall"              { return mk(FORALL); }
  "include"             { return mk(INCLUDE); }
  "foreign"             { return mk(FOREIGN); }
  "compiles"            { return mk(COMPILES); }

  symbol                { return mk(SYMBOL); }

  upperid               { return mk(UPPERIDENT); }
  lowerid               { return mk(SMALLIDENT); }
  underid               { return mk(UNDERIDENT); }
  tickstr               { return mk(STR); }
  dquostr               { return mk(STR); }

  strtag? '"""'         { mk(STR); goto tridquo; }
  strtag? "'''"         { mk(STR); goto trisquo; }

  whitespace            { return mk(WHITESPACE); }

    sign? "0" [xb] hexclump? (backtick hexclump)* ('.' hexclump* (backtick hexclump+)* )?
  | sign? dig      dig*      (backtick dig+    )* ('.' dig*      (backtick dig+     )* )? scinotation?
                        { return mk(NUM); }

  "\r\n"|"\n"
  {
    mk(NEWLINE);
    saw_newline_at(s, YYCURSOR);
    return;
  }

  *
  { report_lexical_error(s, t, "parsing", buff_end);
    goto regular;
  }
*/

linecomment:
/*!re2c
  "\n"          { saw_newline_at(s, YYCURSOR); return; }
  *             { goto linecomment; }
*/

comment:
/*!re2c
  "*/"          { if (--s->commentdepth == 0) { return; } else goto comment; }
  "/*"          { ++s->commentdepth; goto comment; }
  "\n"          { saw_newline_at(s, YYCURSOR); goto comment; }
  *             { goto comment; }
*/

/* The disadvantage of treating newline-containing strings as monolithic lexemes within a re2c block
   is that we'd have to re-inspect the string to find newlines to report proper line numbers
   in case of error messages. Yuck! Comments don't have the problem because they do not have any
   internal lexical structure to get wrong (e.g. escape sequences). */
trisquo:
/*!re2c
  "'''"         { return; }
  "\n"          { saw_newline_at(s, YYCURSOR); goto trisquo; }
  escseq        { goto trisquo; }
  "'"           { goto trisquo; }
  [^\\\n']+     { goto trisquo; }
  *             { report_lexical_error(s, t, "parsing triple quoted string", buff_end); goto trisquo; }
*/

tridquo:
/*!re2c
  '"""'         { return; }
  "\n"          { saw_newline_at(s, YYCURSOR); goto tridquo; }
  escseq        { goto tridquo; }
  '"'           { goto tridquo; }
  [^\\\n"]+     { goto tridquo; }
  *             { report_lexical_error(s, t, "parsing triple quoted string", buff_end); goto tridquo; }
*/
}

int scan_token(Scanner* scanner, Token* t, int buffer_size, YYCTYPE* yych) {
    scan_token_start(scanner, t, buffer_size, yych);

    int typ = t->tok;
    int chan = 0;
    if (typ == WHITESPACE || typ == NEWLINE || typ == LINECOMMENT || typ == BLOCKCOMMENT) chan = 99;

    int endLine = scanner->line;
    int endCol = (scanner->cur == 0 ? 1 : scanner->cur) -
                 (scanner->cur == scanner->linepos ? scanner->linepos_prev : scanner->linepos);

    if (typ == LINECOMMENT || typ == NEWLINE) {
      // These tokens increment scanner.line, to establish the proper state for the following
      // tokens, but we want the "old" version.
      --endLine;
    }

    t->endline = endLine;
    t->endcol = endCol;

    return chan;
}