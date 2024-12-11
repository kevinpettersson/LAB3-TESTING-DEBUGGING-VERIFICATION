
/* 
Answer Question 1a here:

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
  if (x > y){
    a := x;
    b := y;
  }
  else{
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
  }
  else{
    a := y; 
    b := x;
  }
}