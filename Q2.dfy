
method ComputeFact(n : nat) returns (res : nat)
  requires n > 0;
  ensures res == fact(n);
 {
  res := 1;
  var i := 2;
  while (i <= n) 
  {
    res := res * i;
    i := i + 1;
  }
 }

method fact(n : nat) returns (res : nat)

{
  res := n * fact(n-1);
  if(n == 1){
    return res;
  }
  
}