int __VERIFIER_assert(int cond) {
  if (!(cond)) {
  ERROR:
    return 1;
  }
  return 0;
}

int glob_arr[] = {1, 2, 3, 4, 5};

int sum_arr(int *from, int *to) {
  int result = 0;
  while (from < to) {
    //    printf("%p\n", from);
    result += *(from++);
  }
  return result;
}

int main() {
  int sum = sum_arr(glob_arr, glob_arr + 5);
  //  printf("%d\n", sum);
  return __VERIFIER_assert(sum == 15);
}
