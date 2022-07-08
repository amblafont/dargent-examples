theory SumRandom_Update
  imports SumRandom_Abstractions

begin

context SumRandom begin

section random_with_seed
(*


definition
  abbreviatedType1 :: " Cogent.type"
where
  "abbreviatedType1 \<equiv> 
      TRecord [(''seed'',  (TPrim (Num U64), Present)), 
               (''value'', (TPrim (Num U64), Present))] Unboxed"

lemmas abbreviated_type_defs =
  abbreviatedType1_def

definition
  rand_with_seed_type :: " Cogent.kind list \<times>  Cogent.type \<times>  Cogent.type"
where
  "rand_with_seed_type \<equiv> ([], (TPrim (Num U64), abbreviatedType1))"

*)
thm rand_with_seed'_def
term rand_with_seed'        
term val_rel
term "rand_with_seed' 1"
find_theorems val_rel

print_locale SumRandom
print_locale Random_seed_cogent_shallow

thm Random_seed_ACInstall.random_seed.rand_with_seed'_ac_corres
find_theorems "_::((lifted_globals, 'a) nondet_monad \<Rightarrow>_)"
definition rand_with_seed_u:: "(funtyp, abstyp, ptrtyp) ufundef" where
  "rand_with_seed_u x y \<equiv>
      let (\<sigma>, s) = x;
         (\<sigma>', sv) = y
     
      in 
         \<exists> (seed::8 word) (seed'::8 word) (v::8 word) . 
           s = UPrim (LU8 seed) \<and>
           sv = URecord [ (UPrim (LU8 seed'), RPrim (Num U8)), 
                           (UPrim (LU8 v), RPrim (Num U8))] \<and>
           val_rel 
           \<sigma>' = \<sigma>"

lemma rand_with_seed_u_preservation:
  "\<lbrakk>upd.uval_typing \<Xi>' \<sigma> v (TCon ''WordArray'' [t] (Boxed ReadOnly ptrl)) r w;
    rand_with_seed_u (\<sigma>, v) (\<sigma>', v')\<rbrakk>
    \<Longrightarrow> \<exists>r' w'. upd.uval_typing \<Xi>' \<sigma>' v' (TPrim (Num U32)) r' w' \<and> r' \<subseteq> r \<and> upd.frame \<sigma> w \<sigma>' w'"
  apply ( simp add: rand_with_seed_u_def elim: upd.uval_typing.cases)

end (* of context *)

end