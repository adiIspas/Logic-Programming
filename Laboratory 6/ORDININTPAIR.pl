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
fmod PAIR { X :: TOSET, Y :: TOSET} is
  sort Pair {X,Y} .
  op (_,_) : X$Elt Y$Elt -> Pair{X,Y} .
  op _<=_ : Pair{X,Y} Pair{X,Y} -> Bool .
  vars F1 F2 : X$Elt .
  vars S1 S2 : Y$Elt .
  eq (F1,S1) <= (F2,S2) = (F1 <= F2 and F1 =/= F2) or (F1 == F2 and S1 <= S2) .
endfm
  
view INTOSET from TOSET to INT is
  sort Elt to Int .
endv
  
fmod ORDINTPAIR is
  protecting PAIR{INTOSET, INTOSET} .
endfm
  
red (2,5) <= (3,7) .
red (3,5) <= (2,7) .