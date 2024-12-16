
method ComputeFact(n : nat) returns (res : nat)
  requires n > 0
  ensures res == fact(n)
 {
  res := 1;
  var i := 2;
  while (i <= n)
  invariant res == fact(i - 1)
  invariant 1 < i <= n + 1
  // unclear if we need the decreases variant here.
  decreases n - i
  {
    res := res * i;
    i := i + 1;
  }
 }

// Helper ghost function used to prove ComputeFact
ghost function fact(n : nat) : nat
  requires n > 0
  ensures fact(n) > 0
{
  if(n == 1) then n else fact(n-1) * n
}
