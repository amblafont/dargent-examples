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

find_theorems "UCAST(_ \<rightarrow> _) "

lemma unat_8 : "unat (x :: 8 word) < 0x80000000"
  apply(unat_arith)
  by (simp add: unat_ucast_up_simp)
 
lemma unat_16 : "unat (x :: 16 word) < 0x80000000"
  apply(unat_arith)
  by (simp add: unat_ucast_up_simp)



(* These lemmas seem necessary to prove some
get/set lemmas (more exactly, to prove the correspondence between
the monadic and the direct definitions of custom getter/setters).
It is added to the set of simplification lemmas.

Strangely enough, the statement "unat (x :: 8 word) < 0x80000000"
is not enough for the proof of the get/set lemma.
 *)
lemma unat_ucast_8  : "unat (UCAST(('a :: len0) \<rightarrow> 8)  x) < 0x80000000"
  by(rule unat_8)
lemma unat_ucast_16 : "unat (UCAST(('a :: len0) \<rightarrow> 16) x) < 0x80000000"
  by(rule unat_16)






end