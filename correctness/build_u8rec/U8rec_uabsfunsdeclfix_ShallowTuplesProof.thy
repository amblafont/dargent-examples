(*
This file is generated by Cogent

*)

theory U8rec_uabsfunsdeclfix_ShallowTuplesProof
imports "U8rec_uabsfunsdeclfix_Shallow_Desugar"
"U8rec_uabsfunsdeclfix_Shallow_Desugar_Tuples"
"CogentShallow.ShallowTuples"
begin

ML \<open>
structure ShallowTuplesRules_U8rec_uabsfunsdeclfix =
  Named_Thms (
    val name = Binding.name "ShallowTuplesRules_U8rec_uabsfunsdeclfix"
    val description = ""
  )
\<close>
setup \<open> ShallowTuplesRules_U8rec_uabsfunsdeclfix.setup \<close>


ML \<open>
structure ShallowTuplesThms_U8rec_uabsfunsdeclfix =
  Named_Thms (
    val name = Binding.name "ShallowTuplesThms_U8rec_uabsfunsdeclfix"
    val description = ""
  )
\<close>
setup \<open> ShallowTuplesThms_U8rec_uabsfunsdeclfix.setup \<close>


overloading shallow_tuples_rel_T0 \<equiv> shallow_tuples_rel begin
  definition "shallow_tuples_rel_T0 (x :: ('x1) U8rec_uabsfunsdeclfix_ShallowShared.T0) (xt :: ('xt1) U8rec_uabsfunsdeclfix_ShallowShared_Tuples.T0) \<equiv>
    shallow_tuples_rel (U8rec_uabsfunsdeclfix_ShallowShared.T0.a\<^sub>f x) (U8rec_uabsfunsdeclfix_ShallowShared_Tuples.T0.a\<^sub>f xt)"
end
lemma shallow_tuples_rule_make__T0 [ShallowTuplesRules_U8rec_uabsfunsdeclfix]:
  "\<lbrakk>
     shallow_tuples_rel x1 xt1
  \<rbrakk> \<Longrightarrow> shallow_tuples_rel (U8rec_uabsfunsdeclfix_ShallowShared.T0.make x1) \<lparr>U8rec_uabsfunsdeclfix_ShallowShared_Tuples.T0.a\<^sub>f = xt1\<rparr>"
  by (simp add: shallow_tuples_rel_T0_def U8rec_uabsfunsdeclfix_ShallowShared.T0.defs U8rec_uabsfunsdeclfix_ShallowShared_Tuples.T0.defs)
lemma shallow_tuples_rule__T0__a\<^sub>f [ShallowTuplesThms_U8rec_uabsfunsdeclfix]:
  "shallow_tuples_rel (x :: ('x1) U8rec_uabsfunsdeclfix_ShallowShared.T0) (xt :: ('xt1) U8rec_uabsfunsdeclfix_ShallowShared_Tuples.T0) \<Longrightarrow>
   shallow_tuples_rel (U8rec_uabsfunsdeclfix_ShallowShared.T0.a\<^sub>f x) (U8rec_uabsfunsdeclfix_ShallowShared_Tuples.T0.a\<^sub>f xt)"
  by (simp add: shallow_tuples_rel_T0_def)
lemma shallow_tuples_rule__T0__a\<^sub>f__update [ShallowTuplesRules_U8rec_uabsfunsdeclfix]:
  "\<lbrakk> shallow_tuples_rel (x :: ('x1) U8rec_uabsfunsdeclfix_ShallowShared.T0) (xt :: ('xt1) U8rec_uabsfunsdeclfix_ShallowShared_Tuples.T0);
     shallow_tuples_rel v vt
   \<rbrakk> \<Longrightarrow>
   shallow_tuples_rel (U8rec_uabsfunsdeclfix_ShallowShared.T0.a\<^sub>f_update (\<lambda>_. v) x) (U8rec_uabsfunsdeclfix_ShallowShared_Tuples.T0.a\<^sub>f_update (\<lambda>_. vt) xt)"
  by (simp add: shallow_tuples_rel_T0_def)


lemma shallow_tuples__main [ShallowTuplesThms_U8rec_uabsfunsdeclfix]:
  "shallow_tuples_rel U8rec_uabsfunsdeclfix_Shallow_Desugar.main U8rec_uabsfunsdeclfix_Shallow_Desugar_Tuples.main"
  apply (rule shallow_tuples_rel_funI)
  apply (unfold U8rec_uabsfunsdeclfix_Shallow_Desugar.main_def U8rec_uabsfunsdeclfix_Shallow_Desugar_Tuples.main_def id_def)
  apply ((unfold take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t_def Let\<^sub>d\<^sub>s_def Let_def split_def)?,(simp only: fst_conv snd_conv)?)
  by (assumption |
      rule shallow_tuples_basic_bucket ShallowTuplesRules_U8rec_uabsfunsdeclfix
           ShallowTuplesThms_U8rec_uabsfunsdeclfix ShallowTuplesThms_U8rec_uabsfunsdeclfix[THEN shallow_tuples_rel_funD])+


end
