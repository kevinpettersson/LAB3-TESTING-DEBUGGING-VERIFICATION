
method ComputeFact(n : nat) returns (res : nat)
  requires n > 0
  ensures res == fact(n)
{
  res := 1;
  var i := 2;
  while (i <= n)
  invariant res == fact(i - 1)
  invariant 2 <= i <= n + 1 
  decreases n - i // Ensures termination, unsure if we need the varaint here or if Dafny automatically verifies this.
  {
    res := res * i;
    i := i + 1;
  }
}

// Helper ghost function to ComputeFact
ghost function fact(n : nat) : nat
  requires n > 0
  ensures fact(n) > 0 
  decreases n // Same as above, unsure if we need the varaint here or if Dafny automatically verifies this.
{
  if(n == 1) then n else fact(n-1) * n
}
