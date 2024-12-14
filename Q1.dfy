
/* 
  Answer Question 1a here:
  Error: a postcondition could not be proved on this return path
  Could not prove: a > b

  Dafny reports an error beacuse the post-condition (ensures a > b),
  guarantees that (a) will be greater than (b) after the method executes.
  However, the current implementation fails beacuse it fails to handle the case where (x == y).
  In this case neither of the branches can guarantee that the post-condition (a > b) can hold. 
  To fix this there needs to be an pre-condition like (requires x != y), 
  this way Dafny can prove that all inputs except when (x == y) is allowed and then the post-condition will hold.
*/
method M(x : int, y : int) returns (a : int, b : int) 
  ensures a > b
{
  if (x > y){
    a := x;
    b := y;
  }
  else{
    a := y; 
    b := x;
  }
}

// Changed the post-condition, the method now allows the output to be equal.
method M1(x : int, y : int) returns (a : int, b : int) 
  ensures a >= b
{
  if (x > y) {
    a := x;
    b := y;
  } else{
    a := y; 
    b := x;
  }
}

// Added pre-condition, the methods require that the inputs aren't equal.
method M2(x : int, y : int) returns (a : int, b : int) 
  requires x != y 
  ensures a > b
{
  if (x > y){
    a := x;
    b := y;
  } else{
    a := y; 
    b := x;
  }
}

// increment x with 1 in the case x >= y satisfy the post-condition a > b.
method M3(x : int, y : int) returns (a : int, b : int) 
  ensures a > b
{
  if (x >= y){
    a := x + 1;
    b := y;
  }
  else{
    a := y; 
    b := x;
  }
}