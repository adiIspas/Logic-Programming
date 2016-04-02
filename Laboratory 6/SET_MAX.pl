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

fmod SET1 {X :: TRIV} is
  sort Set{X} .
  subsort X$Elt < Set{X} .
  op vid : -> Set{X} .
  op _;_ : Set{X} Set{X} -> Set{X} [assoc id: vid comm] .
  var A : X$Elt .
  vars L1 L2 L3 : Set{X} .
  eq L1 ; A ; L2 ; A ; L3 = L1 ; A ; L2 ; L3 .
endfm

view Toset from TRIV to TOSET is
endv
  
fmod SET_MAX {T :: TOSET} is
  protecting SET1{Toset}{T} .
  op MAX : Set {Toset}{T} -> T$Elt .
  var E : T$Elt .
  var S : Set{Toset}{T} .
  eq MAX(E ; S) = if MAX(S) <= E then E else MAX(S) fi [owise].
  eq MAX(E) = E .
endfm