fth TRIVconst is
  including TRIV .
  op @ : -> Elt .
endfth
  
fmod LIST1 {X :: TRIVconst} is
  sort List {X} .
  subsort X$Elt < List{X} .
  op empty : -> List{X} .
  op _ _ : List{X} List{X} -> List{X} [id: empty assoc]
  op delete : X$Elt List{X} -> List{X} .
  op add : X$Elt List{X} -> List{X} .
  vars E1 E2 : X$Elt .
  var L : List{X} .
  eq delete(E1,E2 L) = if E1 == E2 then @ delete(E1,L) else E2 delete(E1,L) fi .
  eq delete(E1,empty) = empty .
  eq add(E1, E2 L) = if E2 == @ then E1 add(E1, L) else E2 add(E1,L) fi .
  eq add(E1, empty) = empty .
endfm
  
view CHARconst from TRIVconst to STRING is
  sort Elt to String .
  op @ to term "[]" .
endv
  
fmod CHARLIST is
  protecting  LIST1{CHARconst} .
endfm
  
red add( "a" , delete ( "b" , "abc" "b" "bbb" "b" )) .