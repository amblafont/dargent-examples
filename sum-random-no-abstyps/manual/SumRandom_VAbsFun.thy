theory SumRandom_VAbsFun
  imports SumRandom_Value

begin

context SumRandom begin

section "First Order"

fun \<xi>v0 :: "(funtyp, vtyp) vabsfuns" 
  where
  "\<xi>v0 x y z = 
    (if x = ''rand_with_seed'' then rand_with_seed_v y z
     else False)" 

end (* of context *)

end