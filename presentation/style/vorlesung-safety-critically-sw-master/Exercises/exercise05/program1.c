int x, y, z, w;

int main() {
  do {
    x = y;
    if (w != 1)
      x++;
    z = w - 1;
  } while (x != y);

  if (z) {
  ERROR:
    return 1;
  }

  return 0;
}