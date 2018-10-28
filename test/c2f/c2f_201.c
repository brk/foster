extern int printf (const char *format, ...);
extern int getchar(void);

int main(void)
{
  int n=0;
  const char* s = "hello";
loop: if(s[n])
      {
        n++;
        goto loop;
      }
  printf("%d\n",n);
  // No return statement; we'll translate it to an implicitly-returned unit value.
}
