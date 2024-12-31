Definition sum5 := 
  fun x0 x1 x2 x3 x4 : nat =>
    x0 + x1 + x2 + x3 + x4.

Check sum5.

Eval compute in sum5 1 2 3 4 5.