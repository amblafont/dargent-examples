(*
This file is generated by Cogent

*)

theory Random_seed_ShallowShared_Tuples
imports "Cogent.Util"
"CogentShallow.ShallowUtil"
begin

typedecl  Seed

record ('a, 'b) SeedValue =
  seed\<^sub>f :: "'a"
  value\<^sub>f :: "'b"

type_synonym  SeedValue\<^sub>T = "( Seed, 8 word) SeedValue"

consts rand_with_seed :: " Seed \<Rightarrow>  SeedValue\<^sub>T"

end
