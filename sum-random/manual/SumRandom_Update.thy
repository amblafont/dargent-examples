theory SumRandom_Update
  imports SumRandom_Abstractions

begin

context SumRandom begin

section random_with_seed

                                                 
definition rand_with_seed_u:: "(funtyp, abstyp, ptrtyp) ufundef" where
  "rand_with_seed_u x y \<equiv>
      let (\<sigma>, s) = x;
         (\<sigma>', sv) = y
      in \<exists>  (p::ptrtyp)  (v::8 word) (seed::ptrtyp) (seed'::ptrtyp). 
           s = UPtr p (RCon ''Seed'' []) \<and>
           sv =  URecord [ (UPtr p (RCon ''Seed'' []), RPtr (RCon ''Seed'' [])),
                           (UPrim (LU8 v), RPrim (Num U8))] \<and> 
           \<sigma> p = Some (UAbstract (Abs_utyp (TSeed seed)))\<and>
           \<sigma>' = \<sigma>(p := Some (UAbstract (Abs_utyp (TSeed seed'))))"

lemma rand_with_seed_u_preservation:
  "\<lbrakk>upd.uval_typing \<Xi>' \<sigma> v (TCon ''WordArray'' [t] (Boxed ReadOnly ptrl)) r w;
    rand_with_seed_u (\<sigma>, v) (\<sigma>', v')\<rbrakk>
    \<Longrightarrow> \<exists>r' w'. upd.uval_typing \<Xi>' \<sigma>' v' (TPrim (Num U32)) r' w' \<and> r' \<subseteq> r \<and> upd.frame \<sigma> w \<sigma>' w'"
  by (fastforce simp: rand_with_seed_u_def elim: upd.uval_typing.cases)

end (* of context *)

end