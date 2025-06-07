{
    int x;
    int y;
    int temp;
    int n;
    int i;
    int[10] fib;
    
    x = 0;
    y = 1;
    i = 0;
    n = 10;
    
    while (i < n) {
        if (i == 0 || i == 1) {
            fib[i] = i;
        } else {
            temp = x + y;
            x = y;
            y = temp;
            fib[i] = y;
        }
        i++;
    }
    
    i = 0;
    while (i < n) {
        print(fib[i]);
        i++;
    }
}