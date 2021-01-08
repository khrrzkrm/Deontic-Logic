int abs(int x);

int max(int x, int y);

int max_abs(int x, int y) {
x = abs(x);
y = abs(y);
return max(x, y);
}
