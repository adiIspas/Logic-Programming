fth TOSET is
  including TRIV .
  including BOOL .
  op _<=_ : Elt Elt -> Bool .
  vars X Y Z : Elt .
  eq X <= X = true [nonexec] .
  eq X <= Z = X <= Y and Y <= Z [nonexec] .
  ceq X = Y if X <= Y and Y <= X [nonexec] .
  eq X <= Y = not Y <= X and not X == Y [nonexec] .
endfth