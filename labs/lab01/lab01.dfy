// function examples
function Abs(x: int): int {
  if x < 0 then -x else x
}
function Max(a: int, b: int): int {
  if a > b then a else b
}
function Fib(n: nat): nat {
  if n < 2 then n else Fib(n-1) + Fib(n-2)
}

// function Bad(n: nat): nat {
//   Bad(n)
// }



// lemma examples
lemma AbsNonNeg(x: int)
  ensures Abs(x) >= 0
{

}

lemma MaxCommutative(a: int, b: int)
  ensures Max(a, b) == Max(b, a)
{

}



// inductive lemma
function Sum(n: nat): nat {
  if n == 0 then 0 else n + Sum(n - 1)
}

lemma SumFormula(n: nat)
  ensures Sum(n) == n * (n + 1) / 2
{

}



// assertion examples
lemma AssertionDemo(x: int)
  requires x > 100
{
  // (1) This is a proof obligation: Dafny must prove x > 50 from x > 100
  assert x > 50;
  // (2) From here on, x > 50 becomes a known fact (alongside x > 100)
  assert x - 49 > 0;   // derivable using x > 50
  assert x + 50 > 100; // derivable using x > 100
}

lemma Demo(n: int)
  requires n >= 0
{
  var m := n * n;   // m is a fresh name for n*n
  assert m >= 0;    // (1) Dafny proves: any square is >= 0
  // (2) now m >= 0 is a known fact available below
  assert m + 1 >= 1; // uses m >= 0
}

lemma AssumeVsAssert()
{
  assume false;   // Dafny accepts it without checking, pretending false is true
  assert 1 == 2;  // now this "verifies"! Because from false, anything follows
}