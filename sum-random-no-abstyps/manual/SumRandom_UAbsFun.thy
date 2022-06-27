theory SumRandom_UAbsFun
  imports SumRandom_Update

begin

context SumRandom begin

section "First Order"

fun \<xi>u0 :: "(funtyp, abstyp, ptrtyp) uabsfuns" 
  where
  "\<xi>u0 x y z = 
    (if x = ''rand_with_seed'' then rand_with_seed_u y z
     else False)" 

end (* of context *)

end