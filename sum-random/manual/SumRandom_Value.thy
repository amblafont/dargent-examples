theory SumRandom_Value
  imports SumRandom_Abstractions

begin


context SumRandom begin

section random_with_seed

definition rand_with_seed_v :: "(funtyp, vtyp) vval \<Rightarrow> (funtyp, vtyp) vval \<Rightarrow> bool"
  where
  "rand_with_seed_v x y = 
      (\<exists>s s'. x = VAbstract (VSeed s) \<and> 
              y = VAbstract (VSeed s'))" 

lemma rand_with_seed_v_rename_monoexpr_correct:
  "\<lbrakk>rand_with_seed_v (val.rename_val rename' (val.monoval v)) v'; 
    val.proc_env_matches \<xi>\<^sub>v \<Xi>'; 
    proc_ctx_wellformed \<Xi>'\<rbrakk> \<Longrightarrow> 
     v' = val.rename_val rename' (val.monoval v') \<and> 
    rand_with_seed_v v v'"
  by (clarsimp simp: rand_with_seed_v_def) 
     (case_tac v; clarsimp)

lemma rand_with_seed_v_preservation:
  "\<lbrakk>val.vval_typing \<Xi>' v t; rand_with_seed_v v v'\<rbrakk>
    \<Longrightarrow> val.vval_typing \<Xi>' v' t"
  by (fastforce elim: val.vval_typing.cases 
                intro: val.v_t_abstract 
                simp: rand_with_seed_v_def seed_abs_typing_v_def) 

end (* of context *)

end