extern int printf (const char *format, ...);

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
  return 0;
}
