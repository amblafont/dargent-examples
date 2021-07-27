(*
This file is generated by Cogent

*)

theory Random_seed_master_Shallow_Desugar
imports "Random_seed_master_ShallowShared"
begin

definition
  main :: " Seed \<Rightarrow>  SeedValue\<^sub>T"
where
  "main ds\<^sub>0 \<equiv> HOL.Let ds\<^sub>0 (\<lambda>seed. HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t (rand_with_seed seed) SeedValue.seed\<^sub>f) (\<lambda>(seed,r). HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t (rand_with_seed seed) SeedValue.seed\<^sub>f) (\<lambda>(seed,r2). SeedValue.make seed ((+) (SeedValue.value\<^sub>f r) (SeedValue.value\<^sub>f r2)))))"

end
