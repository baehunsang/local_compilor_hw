{
  int size;
  int[100] a;
  int i;
  int j;
  int cnt;

  i = 0;
  cnt = 0;
  while (i<100) {
    a[i] = cnt;
    cnt++;
    i++;
  }
  print (a[10]);
  print (a[20]);
}
