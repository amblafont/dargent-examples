(*
This file is generated by Cogent

*)

theory U8rec_uabsfunsdeclfix_CorresSetup
imports "CogentCRefinement.Deep_Embedding_Auto"
"CogentCRefinement.Cogent_Corres"
"CogentCRefinement.Tidy"
"CogentCRefinement.Heap_Relation_Generation"
"CogentCRefinement.Type_Relation_Generation"
"U8rec_uabsfunsdeclfix_ACInstall"
"U8rec_uabsfunsdeclfix_TypeProof"
begin

(* C type and value relations *)

instantiation unit_t_C :: cogent_C_val
begin
  definition type_rel_unit_t_C_def: "\<And> r. type_rel r (_ :: unit_t_C itself) \<equiv> r = RUnit"
  definition val_rel_unit_t_C_def: "\<And> uv. val_rel uv (_ :: unit_t_C) \<equiv> uv = UUnit"
  instance ..
end

instantiation bool_t_C :: cogent_C_val
begin
definition type_rel_bool_t_C_def: "\<And> typ. type_rel typ (_ :: bool_t_C itself) \<equiv> (typ = RPrim Bool)"
definition val_rel_bool_t_C_def:
   "\<And> uv x. val_rel uv (x :: bool_t_C) \<equiv> (boolean_C x = 0 \<or> boolean_C x = 1) \<and>
     uv = UPrim (LBool (boolean_C x \<noteq> 0))"
instance ..
end
context update_sem_init begin
lemmas corres_if = corres_if_base[where bool_val' = boolean_C,
                     OF _ _ val_rel_bool_t_C_def[THEN meta_eq_to_obj_eq, THEN iffD1]]
end
(* C heap type class *)
class cogent_C_heap = cogent_C_val +
  fixes is_valid    :: "lifted_globals \<Rightarrow> 'a ptr \<Rightarrow> bool"
  fixes heap        :: "lifted_globals \<Rightarrow> 'a ptr \<Rightarrow> 'a"
(* Put manual type and value relations below here *)
(* Put manual type and value relations above here *)

local_setup \<open> local_setup_val_rel_type_rel_put_them_in_buckets "u8rec_uabsfunsdeclfix.c" [] \<close>
local_setup \<open> local_setup_instantiate_cogent_C_heaps_store_them_in_buckets "u8rec_uabsfunsdeclfix.c" \<close>
locale U8rec_uabsfunsdeclfix = "u8rec_uabsfunsdeclfix" + update_sem_init
begin

(* Relation between program heaps *)
definition
  heap_rel_ptr ::
  "(funtyp, abstyp, ptrtyp) store \<Rightarrow> lifted_globals \<Rightarrow>
   ('a :: cogent_C_heap) ptr \<Rightarrow> bool"
where
  "\<And> \<sigma> h p.
    heap_rel_ptr \<sigma> h p \<equiv>
   (\<forall> uv.
     \<sigma> (ptr_val p) = Some uv \<longrightarrow>
     type_rel (uval_repr uv) TYPE('a) \<longrightarrow>
     is_valid h p \<and> val_rel uv (heap h p))"

lemma heap_rel_ptr_meta:
  "heap_rel_ptr = heap_rel_meta is_valid heap"
  by (simp add: heap_rel_ptr_def[abs_def] heap_rel_meta_def[abs_def])

local_setup \<open> local_setup_heap_rel "u8rec_uabsfunsdeclfix.c" [] [] \<close>

definition state_rel :: "((funtyp, abstyp, ptrtyp) store \<times> lifted_globals) set"
where
  "state_rel  = {(\<sigma>, h). heap_rel \<sigma> h}"

lemmas val_rel_simps[ValRelSimp] =
  val_rel_word
  val_rel_ptr_def
  val_rel_unit_def
  val_rel_unit_t_C_def
  val_rel_bool_t_C_def
  val_rel_fun_tag
(* Put manual value relation definitions below here *)
(* Put manual value relation definitions above here *)

lemmas type_rel_simps[TypeRelSimp] =
  type_rel_word
  type_rel_ptr_def
  type_rel_unit_def
  type_rel_unit_t_C_def
  type_rel_bool_t_C_def
(* Put manual type relation definitions below here *)
(* Put manual type relation definitions above here *)

(* Generating the specialised take and put lemmas *)

local_setup \<open> local_setup_take_put_member_case_esac_specialised_lemmas "u8rec_uabsfunsdeclfix.c" \<close>
local_setup \<open> fold tidy_C_fun_def' Cogent_functions \<close>

end (* of locale *)


end
