(*

This file deals with custom getters and setters in case of custom layouts.
It also register uvals read from the table file in the theory.

The two main functions are
- generate_isa_getset_records_for_file: generates a direct and non monadic definition of custom
getters and setters by inspecting the C (monadic) definition

- local_setup_getset_lemmas which generates the get/set lemmas and prove them (similarly
to local_setup_take_put_member_case_esac_specialised_lemmas)

To show the get/set lemmas that ought to be proven, use the following snippset:
ML \<open> val lems = mk_getset_lems "variant_dargentisa.c" @{context} \<close>
ML \<open>lems  |> map (string_of_getset_lem @{context})|> map tracing\<close>

These get/set lemmas should be proven before the Take, Put, .. lemmas.


*)
theory Complements
  imports AutoCorres.AutoCorres
begin



(* Why is it necessary to prove this lemma *)
lemma unat_ucast_32_8 : "unat ( (UCAST(32 \<rightarrow> 8) x))
         <  2147483648"
  apply(unat_arith)
  apply (simp add: unat_ucast_up_simp)
  done

lemma unat_ucast_32_16 : "unat (UCAST(32 \<rightarrow> 16) x) < 2147483648"
  apply(unat_arith)
  apply (simp add: unat_ucast_up_simp)
  done



end