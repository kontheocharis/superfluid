function fizzbuzz(n) {
  if (n % 15 == 0) {
    return "fizzbuzz";
  }
  if (n % 3 == 0) {
    return "fizz";
  }
  if (n % 5 == 0) {
    return "buzz";
  }
  return "nothing!";
}

function repeat(n, f) {
  if (n == 0) {
    return;
  }
  f(n);
  repeat(n - 1, f);
}

repeat(10000, (n) => {
  console.log(fizzbuzz(n));
});
