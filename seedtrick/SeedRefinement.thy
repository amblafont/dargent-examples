theory SeedRefinement
imports "lib/CogentMonad"
"lib/CogentCorres"
"build_random_seed/Random_seed_master_Shallow_Normal"
begin
definition
  arand :: "(8 word) cogent_monad"
where
 "arand \<equiv> UNIV"

text{* iget_res is the value-relation for the spec-SS correspondence for the function iget*}
definition
 irand_res :: "8 word \<Rightarrow>  SeedValue\<^sub>T \<Rightarrow> bool"
where
 "irand_res x y \<equiv> x = value\<^sub>f y"
term cogent_corres
term rand_with_seed
lemma refine_irand :
"\<And>s. cogent_corres irand_res
         arand (rand_with_seed s)"
  apply(simp add:cogent_corres_def irand_res_def)
  by (simp add:cogent_corres_def irand_res_def arand_def)

(*  SeedValue\<^sub>T *)
axiomatization
where
  rand_with_seed_def : "rand_with_seed s = \<lparr> seed\<^sub>f = s + 1, value\<^sub>f = s \<rparr>"
(* 

*)