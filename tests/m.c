int add(int a, int b) { return a + b; }
int sq(int x) { return x * x; }

int main() {
    int a = 3, b = 4;
    printf("add=%d, sq=%d\n", add(a, b), sq(b));
    return 0;
}
