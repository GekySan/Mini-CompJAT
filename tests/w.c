int main() {
    int i = 0;
    while (i < 5) {
        i = i + 1;
        if (i == 3) continue;
        printf("while i=%d\n", i);
    }

    int j = 0;
    do {
        j = j + 1;
        if (j == 2) continue;
        if (j > 3) break;
        printf("do j=%d\n", j);
    } while (j < 5);

    return 0;
}
