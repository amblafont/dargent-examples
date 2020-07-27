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


(* Vincent's complements for his tactic *)

lemma index_update_eq:
  fixes f :: "'a[('b :: finite)]"
  assumes "k < CARD('b)"
  shows
  "(Arrays.update f n x.[k]) = (if n = k then x else f.[k])"
  using assms
  by simp

lemma ucast_and_distrib:
  "UCAST(('a::len) \<rightarrow> ('b::len)) (a && b) = UCAST('a \<rightarrow> 'b) a && UCAST('a \<rightarrow> 'b) b"
  unfolding ucast_def Word.bitAND_word.abs_eq uint_and
  by simp

lemma neg_disj_pos_conj_iff:
  "\<not> A \<and> (A \<or> B) \<longleftrightarrow> \<not> A \<and> B"
  by blast

lemma pos_disj_neg_conj_iff:
  "A \<or> (\<not>A \<and> B) \<longleftrightarrow> A \<or> B"
  by blast

lemma pos_disj_neg_conj_iff2:
  "A \<or> (B \<and> \<not>A) \<longleftrightarrow> A \<or> B"
  by blast

lemma posA_B_negA_iff:
  "A \<or> B \<or> \<not> A \<longleftrightarrow> True"
  by blast


lemma xANDyANDx_eq: "x && y && x = y && x"
  by (metis AND_twice word_bw_comms(1))



lemma ucast_down_shiftr_distrib:
  "LENGTH('b) \<le> LENGTH('a) \<Longrightarrow> UCAST(('a::len) \<rightarrow> ('b::len)) (a << n) = UCAST('a \<rightarrow> 'b) a << n"
  apply (simp add: ucast_def uint_shiftl word_size shiftl_int_def)
  apply (simp add: wi_bintr wi_hom_syms)
  apply (simp add: shiftl_t2n word_of_int_2p)
  done

lemma ucast_up_shiftr_distrib:
  "LENGTH('b) \<ge> LENGTH('a) \<Longrightarrow> UCAST(('a::len) \<rightarrow> ('b::len)) (a << n) = (UCAST('a \<rightarrow> 'b) a << n) && mask LENGTH('a)"
  apply (simp add: ucast_def uint_shiftl word_size shiftl_int_def)
  apply (simp add: and_mask_wi[symmetric])
  apply (simp add: wi_hom_syms)
  apply (simp add: shiftl_t2n word_of_int_2p)
  apply (simp add: semiring_normalization_rules(7))
  done


lemma max_and_word_simps:
  "\<And>a::8 word. 0xFF && a = a"
  "\<And>a::16 word. 0xFFFF && a = a"
  "\<And>a::32 word. 0xFFFFFFFF && a = a"
  "\<And>a::64 word. 0xFFFFFFFFFFFFFFFF && a = a"
  by (simp add: word_and_max_simps word_bw_comms)+

(* 
Vincent's tactic.

Originally, it is designed to prove the following get/set lemmas
in the presence of variants:

1. val_rel x v \<Rightarrow> val_rel x (get_a (set_a p v))
2. get_a \<circ> set_b = get_a

It turns out that it may be working (for the second case) even when
no variants are involved.

*)
ML\<open>
(* This tactic was created using the "throw things in and see if it works" strategy.
 * Eventually, we should write something more principled. ~ v.j. / 2020-07-15
 *)
fun solve_dargent_bitwise_tac ctxt tags_distinct i =
  let
  ; val reduce_variant1 (* only *) =  @{thms if_False if_True refl index_update_eq card_bit0 card_bit1}
  ; val reduce_variant2 = tags_distinct @ @{thms disj_imp[symmetric] Inductive.imp_conj_iff
                                 neg_disj_pos_conj_iff pos_disj_neg_conj_iff}
  ; val word_distrib_simpset =
    @{thms word_bool_alg.conj_disj_distrib word_bool_alg.conj_disj_distrib2
           shiftr_over_or_dist shiftr_over_and_dist
           shiftl_over_or_dist shiftl_over_and_dist
           word_bool_alg.conj.assoc
           word_bool_alg.disj.assoc
           ucast_and_distrib ucast_or_distrib ucast_ucast_mask}
  ; val word_simps2 =
    @{thms xANDyANDx_eq and_mask2 word_size ucast_or_distrib mask_def ucast_id word_and_max_simps
           max_and_word_simps}
  ; val word_join_simps =
    @{thms word_bool_alg.conj_disj_distrib[symmetric] word_and_max_simps max_and_word_simps}
  ; val word_left_right_shift_simps =
    @{thms and_mask2 and_not_mask[symmetric] mask_def
           word_bool_alg.conj.assoc word_bool_alg.disj.assoc}
  ; val cleanup_simps =
    @{thms pos_disj_neg_conj_iff pos_disj_neg_conj_iff2 posA_B_negA_iff}
   in ((simp_tac ((clear_simpset ctxt) addsimps reduce_variant1)
        THEN' simp_tac ((clear_simpset ctxt) addsimps reduce_variant2)
        THEN' (fn i => REPEAT_DETERM (DETERM (CHANGED (
          (simp_tac ((clear_simpset ctxt) addsimps word_distrib_simpset)
          THEN' simp_tac (ctxt addsimps word_simps2)
          ) i
        ))))
        THEN' (fn i => (TRY (
          (simp_tac (ctxt addsimps word_left_right_shift_simps)
          THEN' simp_tac (ctxt addsimps word_join_simps)
          THEN' (fn i => TRY (simp_tac (ctxt addsimps cleanup_simps) i))) i
      )))) i)
  end;
fun getput_variant_tac ctxt tags_distinct =
  let val tags_cleanup =
    tags_distinct @ @{thms  if_False if_True refl disj_imp[symmetric] neg_disj_pos_conj_iff}
   in TRYALL (fn i => CHANGED (
        (simp_tac (ctxt addsimps tags_cleanup)
        THEN' solve_dargent_bitwise_tac ctxt tags_distinct) i))
  end;
\<close>



end