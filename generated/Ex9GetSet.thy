theory Ex9GetSet
  imports Main "HOL-Word.Word" "Word_Lib.Word_Lib" 
 "build_ex9/Ex9_dargentfull_CorresSetup"
(* "../GetSet" *)
begin 
context Ex9_dargentfull begin
local_setup \<open>
local_setup_getter_correctness "ex9_dargentfull.c"
\<close>
thm abbreviated_type_defs
thm
thm GetSetSanity[simplified abbreviated_type_defs[symmetric]]
end


context Ex9_dargentfull begin


definition type_def : "type = abbreviatedType1"
lemmas type_defs = type_def abbreviatedType1_def
lemma  "valid_tags (layout_from_trecord type) (data_C t) \<Longrightarrow>  val_rel (uval_from_array_toplevel type (data_C t)) t"
  apply (simp only:type_defs)
  apply(tactic \<open>solve_corres_getters @{context} 1\<close>)
  done
end
end