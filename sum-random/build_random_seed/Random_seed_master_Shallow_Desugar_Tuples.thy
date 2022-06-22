(*
This file is generated by Cogent

*)

theory Random_seed_master_Shallow_Desugar_Tuples
imports "Random_seed_master_ShallowShared_Tuples"
begin

definition
  main :: " Seed \<Rightarrow>  SeedValue\<^sub>T"
where
  "main ds\<^sub>0 \<equiv>
    let r = rand_with_seed ds\<^sub>0;
      seed = SeedValue.seed\<^sub>f r;
      r2 = rand_with_seed seed;
      seed = SeedValue.seed\<^sub>f r2
    in \<lparr>
        SeedValue.seed\<^sub>f = seed,
        value\<^sub>f = (+) (SeedValue.value\<^sub>f r) (SeedValue.value\<^sub>f r2)
      \<rparr>"

end