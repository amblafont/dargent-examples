(*
This file is generated by Cogent
*)
theory Random_seed_ACInstall
imports
  "AutoCorres.AutoCorres"

begin

declare [[record_codegen = false]]
declare [[use_anonymous_local_variables=true]]

new_C_include_dir "/home/ouguir/cogent/branches/supplementalnonanon/cogent/lib"



install_C_file "random_seed.c"
autocorres [keep_going, ts_rules = nondet, no_opt, skip_word_abs] "random_seed.c"

end

