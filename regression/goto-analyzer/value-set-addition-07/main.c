int unknown();

int main(int argc, char argv[]) 
{
  int p;
  int q;
  int r = 20;

  if (unknown()) p = 2; else p = 3;
  if (unknown()) q = 5; else q = 10;
  if (unknown()) r = 20; else r = 30;

  int t = p + q + r;
}
