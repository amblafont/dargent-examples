(*
This file is generated by Cogent
*)
theory U8rec_uabsfunsdeclfix_ACInstall
imports
  "AutoCorres.AutoCorres"

begin

declare [[record_codegen = false]]
declare [[use_anonymous_local_variables=true]]
new_C_include_dir "/home/ouguir/cogent/branches/uabsfunsdeclfix/cogent/lib"
install_C_file "u8rec_uabsfunsdeclfix.c"
autocorres [keep_going, ts_rules = nondet, no_opt, skip_word_abs] "u8rec_uabsfunsdeclfix.c"

end

