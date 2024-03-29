(*
This file is generated by Cogent

*)

theory Random_seed_TypeProof
imports "Cogent.TypeProofGen"
"Cogent.AssocLookup"
begin

definition
  abbreviatedType1 :: " Cogent.type"
where
  "abbreviatedType1 \<equiv> TRecord [(''seed'', (TCon ''Seed'' [] (Boxed Writable None), Present)), (''value'', (TPrim (Num U8), Present))] Unboxed"

lemmas abbreviated_type_defs =
  abbreviatedType1_def

definition
  rand_with_seed_type :: " poly_type"
where
  "rand_with_seed_type \<equiv> (0, [], {}, TCon ''Seed'' [] (Boxed Writable None), abbreviatedType1)"

definition
  main_type :: " poly_type"
where
  "main_type \<equiv> (0, [], {}, TCon ''Seed'' [] (Boxed Writable None), abbreviatedType1)"

definition
  main :: "string Cogent.expr"
where
  "main \<equiv> Let (Var 0) (Let (App (AFun ''rand_with_seed'' [] []) (Var 0)) (Take (Var 0) 0 (Let (App (AFun ''rand_with_seed'' [] []) (Var 0)) (Take (Var 0) 0 (Let (Member (Var 4) 1) (Let (Member (Var 2) 1) (Let (Prim (Plus U8) [Var 1, Var 0]) (Struct [TCon ''Seed'' [] (Boxed Writable None), TPrim (Num U8)] [Var 3, Var 0]))))))))"

ML \<open>
val Cogent_functions = ["main"]
val Cogent_abstract_functions = ["rand_with_seed"]
\<close>

definition
  \<Xi> :: " string \<Rightarrow>  poly_type"
where
  "\<Xi> \<equiv> assoc_lookup [(''rand_with_seed'', rand_with_seed_type), (''main'', main_type)] (0, [], {}, TUnit, TUnit)"

definition
  "\<xi> \<equiv> assoc_lookup [(''rand_with_seed'', (\<lambda>_ _. False))]"

definition
  "main_typetree \<equiv> TyTrSplit (Cons (Some TSK_L) []) [] TyTrLeaf [Some (TCon ''Seed'' [] (Boxed Writable None))] (TyTrSplit (Cons (Some TSK_L) (Cons None [])) [] TyTrLeaf [Some abbreviatedType1] (TyTrSplit (Cons (Some TSK_L) (append (replicate 2 None) [])) [] TyTrLeaf [Some (TCon ''Seed'' [] (Boxed Writable None)), Some (TRecord [(''seed'', (TCon ''Seed'' [] (Boxed Writable None), Taken)), (''value'', (TPrim (Num U8), Present))] Unboxed)] (TyTrSplit (Cons (Some TSK_L) (Cons (Some TSK_R) (append (replicate 3 None) []))) [] TyTrLeaf [Some abbreviatedType1] (TyTrSplit (Cons (Some TSK_L) (Cons None (Cons (Some TSK_R) (append (replicate 3 None) [])))) [] TyTrLeaf [Some (TCon ''Seed'' [] (Boxed Writable None)), Some (TRecord [(''seed'', (TCon ''Seed'' [] (Boxed Writable None), Taken)), (''value'', (TPrim (Num U8), Present))] Unboxed)] (TyTrSplit (Cons (Some TSK_R) (Cons (Some TSK_R) (append (replicate 2 None) (Cons (Some TSK_L) (append (replicate 3 None) []))))) [] TyTrLeaf [Some (TPrim (Num U8))] (TyTrSplit (Cons (Some TSK_R) (Cons (Some TSK_R) (Cons (Some TSK_L) (append (replicate 6 None) [])))) [] TyTrLeaf [Some (TPrim (Num U8))] (TyTrSplit (Cons (Some TSK_L) (Cons (Some TSK_L) (Cons (Some TSK_R) (append (replicate 7 None) [])))) [] TyTrLeaf [Some (TPrim (Num U8))] TyTrLeaf)))))))"

ML \<open> open TTyping_Tactics \<close>

ML_quiet \<open>
val typing_helper_1_script : tac list = [
(ForceTac @{thms kinding_def kinding_all_def kinding_variant_def kinding_record_def matches_fields_layout_def upt_def match_repr_layout_simps match_constraint_def size_ptr_def})
] \<close>


lemma typing_helper_1[unfolded abbreviated_type_defs] :
  "kinding 0 [] {} (TCon ''Seed'' [] (Boxed Writable None)) {E}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic \<open> map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_1_script |> EVERY \<close>)
  done

ML_quiet \<open>
val typing_helper_2_script : tac list = [
(ForceTac @{thms kinding_def kinding_all_def kinding_variant_def kinding_record_def matches_fields_layout_def upt_def match_repr_layout_simps match_constraint_def size_ptr_def})
] \<close>


lemma typing_helper_2[unfolded abbreviated_type_defs] :
  "kinding 0 [] {} abbreviatedType1 {E}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic \<open> map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_2_script |> EVERY \<close>)
  done

ML_quiet \<open>
val typing_helper_3_script : tac list = [
(ForceTac @{thms matches_fields_layout_def upt_def match_repr_layout_simps match_constraint_def size_ptr_def})
] \<close>


lemma typing_helper_3[unfolded abbreviated_type_defs] :
  "type_wellformed 0 0 {} (TCon ''Seed'' [] (Boxed Writable None))"
  apply (unfold abbreviated_type_defs)?
  apply (tactic \<open> map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_3_script |> EVERY \<close>)
  done

ML_quiet \<open>
val typing_helper_4_script : tac list = [
(RTac @{thm typing_subst}),
(SimpSolveTac ([],[])),
(SimpTac ([],[(nth @{thms HOL.simp_thms} (25-1)),(nth @{thms HOL.simp_thms} (26-1))]))
] \<close>


lemma typing_helper_4[unfolded abbreviated_type_defs] :
  "subst_wellformed 0 [] {} [] [] 0 [] {}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic \<open> map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_4_script |> EVERY \<close>)
  done

ML_quiet \<open>
val typing_helper_5_script : tac list = [
(ForceTac @{thms matches_fields_layout_def upt_def match_repr_layout_simps match_constraint_def size_ptr_def})
] \<close>


lemma typing_helper_5[unfolded abbreviated_type_defs] :
  "type_wellformed 0 0 {} (TFun (TCon ''Seed'' [] (Boxed Writable None)) abbreviatedType1)"
  apply (unfold abbreviated_type_defs)?
  apply (tactic \<open> map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_5_script |> EVERY \<close>)
  done

ML_quiet \<open>
val typing_helper_6_script : tac list = [
(ForceTac @{thms kinding_def kinding_all_def kinding_variant_def kinding_record_def matches_fields_layout_def upt_def match_repr_layout_simps match_constraint_def size_ptr_def})
] \<close>


lemma typing_helper_6[unfolded abbreviated_type_defs] :
  "kinding 0 [] {} (TRecord [(''seed'', (TCon ''Seed'' [] (Boxed Writable None), Taken)), (''value'', (TPrim (Num U8), Present))] Unboxed) {E, S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic \<open> map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_6_script |> EVERY \<close>)
  done

ML_quiet \<open>
val typing_helper_7_script : tac list = [
(ForceTac @{thms kinding_def kinding_all_def kinding_variant_def kinding_record_def matches_fields_layout_def upt_def match_repr_layout_simps match_constraint_def size_ptr_def})
] \<close>


lemma typing_helper_7[unfolded abbreviated_type_defs] :
  "kinding 0 [] {} (TPrim (Num U8)) {E, S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic \<open> map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_7_script |> EVERY \<close>)
  done

ML_quiet \<open>
val main_typecorrect_script : hints treestep list = [
StepDown,
Val (KindingTacs [(RTac @{thm typing_helper_1})]),
StepDown,
StepDown,
Val (KindingTacs [(RTac @{thm typing_helper_1})]),
StepUp,
Val (TypingTacs []),
StepDown,
StepDown,
Val (KindingTacs [(RTac @{thm typing_helper_2})]),
StepUp,
Val (TypingTacs [(RTac @{thm typing_app}),(SplitsTac [SOME [(RTac @{thm split_comp.right}),(RTac @{thm type_wellformed_prettyI}),(SimpTac ([],@{thms type_wellformed.simps})),(RTac @{thm typing_helper_3})],NONE]),(RTac @{thm typing_afun'}),(SimpTac ([@{thm \<Xi>_def},@{thm rand_with_seed_type_def[unfolded abbreviated_type_defs]}],[])),(RTac @{thm typing_helper_4}),(SimpSolveTac ([],[])),(SimpSolveTac ([],[])),(RTac @{thm type_wellformed_prettyI}),(SimpTac ([],@{thms type_wellformed.simps})),(RTac @{thm typing_helper_5}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac []),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_1}]),(SimpSolveTac ([],[]))]),
StepDown,
StepDown,
Val (KindingTacs [(RTac @{thm typing_helper_1})]),
Val (KindingTacs [(RTac @{thm typing_helper_6})]),
StepUp,
Val (TypingTacs []),
Val (KindingTacs [(RTac @{thm typing_helper_1})]),
StepDown,
StepDown,
Val (KindingTacs [(RTac @{thm typing_helper_2})]),
StepUp,
Val (TypingTacs [(RTac @{thm typing_app}),(SplitsTac [SOME [(RTac @{thm split_comp.right}),(RTac @{thm type_wellformed_prettyI}),(SimpTac ([],@{thms type_wellformed.simps})),(RTac @{thm typing_helper_3})],NONE]),(RTac @{thm typing_afun'}),(SimpTac ([@{thm \<Xi>_def},@{thm rand_with_seed_type_def[unfolded abbreviated_type_defs]}],[])),(RTac @{thm typing_helper_4}),(SimpSolveTac ([],[])),(SimpSolveTac ([],[])),(RTac @{thm type_wellformed_prettyI}),(SimpTac ([],@{thms type_wellformed.simps})),(RTac @{thm typing_helper_5}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac []),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_1}]),(SimpSolveTac ([],[]))]),
StepDown,
StepDown,
Val (KindingTacs [(RTac @{thm typing_helper_1})]),
Val (KindingTacs [(RTac @{thm typing_helper_6})]),
StepUp,
Val (TypingTacs []),
Val (KindingTacs [(RTac @{thm typing_helper_1})]),
StepDown,
StepDown,
Val (KindingTacs [(RTac @{thm typing_helper_7})]),
StepUp,
Val (TypingTacs [(RTac @{thm typing_member}),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_6}]),(SimpSolveTac ([],[])),(RTac @{thm typing_helper_6}),(SimpSolveTac ([],[])),(SimpSolveTac ([],[])),(SimpSolveTac ([],[]))]),
StepDown,
StepDown,
Val (KindingTacs [(RTac @{thm typing_helper_7})]),
StepUp,
Val (TypingTacs [(RTac @{thm typing_member}),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_6}]),(SimpSolveTac ([],[])),(RTac @{thm typing_helper_6}),(SimpSolveTac ([],[])),(SimpSolveTac ([],[])),(SimpSolveTac ([],[]))]),
StepDown,
StepDown,
Val (KindingTacs [(RTac @{thm typing_helper_7})]),
StepUp,
Val (TypingTacs []),
Val (TypingTacs []),
StepUp,
StepUp,
StepUp,
StepUp,
StepUp,
StepUp,
StepUp,
StepUp,
StepUp
] \<close>


ML_quiet \<open>
val main_ttyping_details_future = get_all_typing_details_future false @{context} "main"
   main_typecorrect_script
\<close>


lemma main_typecorrect :
  "\<Xi>, prod.fst main_type, prod.fst (prod.snd main_type), prod.fst (prod.snd (prod.snd main_type)), (main_typetree, [Some (prod.fst (prod.snd (prod.snd (prod.snd main_type))))]) T\<turnstile> main : prod.snd (prod.snd (prod.snd (prod.snd main_type)))"
  apply (tactic \<open> resolve_future_typecorrect @{context} main_ttyping_details_future \<close>)
  done

ML_quiet \<open>
val (_, main_typing_tree, main_typing_bucket)
= Future.join main_ttyping_details_future
\<close>


end
