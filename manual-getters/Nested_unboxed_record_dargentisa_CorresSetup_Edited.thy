(*
This file is generated by Cogent

*)

theory Nested_unboxed_record_dargentisa_CorresSetup_Edited
imports "/home/laf027/cogent/branches/dargentisa/c-refinement/Deep_Embedding_Auto"
"/home/laf027/cogent/branches/dargentisa/c-refinement/Cogent_Corres"
"/home/laf027/cogent/branches/dargentisa/c-refinement/Tidy"
"/home/laf027/cogent/branches/dargentisa/c-refinement/Heap_Relation_Generation"
"/home/laf027/cogent/branches/dargentisa/c-refinement/Type_Relation_Generation"
"build_nested_unboxed_record/Nested_unboxed_record_dargentisa_ACInstall"
"build_nested_unboxed_record/Nested_unboxed_record_dargentisa_TypeProof"
"../Complements"
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


(* Non-generated stuff *)


ML \<open>val g = get_callgraph @{theory} "nested_unboxed_record_dargentisa.c"\<close>
ML \<open>val getter_name = "d3_get_aa"\<close>
ML \<open>val setter_name = "d9_set_aa"\<close>
ML \<open>val lget_aa = rec_called_funs g getter_name\<close>
ML \<open>val lset_aa = rec_called_funs g setter_name\<close>


context nested_unboxed_record_dargentisa begin
(* Tidy the definitions of getters *)
local_setup \<open>fold tidy_C_fun_def' (getter_name :: lget_aa)\<close>
end

ML \<open>fun prefix_loc s = "nested_unboxed_record_dargentisa." ^ s\<close>

(* Code to be used later to get the name of the heap getter/setter
ML \<open> (HeapInfo.get @{theory}) |> Symtab.keys \<close>
ML \<open>
val heap = Symtab.lookup (HeapInfo.get @{theory}) 
"nested_unboxed_record_dargentisa.c" |> the
           |> #heap_info  |> #heap_setters
|> (fn x => Typtab.lookup x 
  (Syntax.read_typ @{context} "t1_C"))
\<close>
*)

local_setup \<open>
fn ctxt =>
my_generate_fun "deref_d3_get_aa" ["w"]
 (generate_getter_term ctxt 
(prefix_loc getter_name) 
(List.map prefix_loc lget_aa)
 "heap_t1_C") ctxt
\<close>

(* TODO: move this lemma in the C-parser library, where t1_C_updupd_same
is generated (c-parser/recursive_records/recursive_record_package.ML)
*)
lemma heap_t1_C_update_comp[simp]:
  " heap_t1_C_update f o heap_t1_C_update f' = heap_t1_C_update (f o f')"
  by fastforce


local_setup \<open>
fn ctxt =>
my_generate_fun "deref_d9_set_aa" ["w", "v"]
 (generate_setter_term ctxt 
(prefix_loc setter_name) 
(List.map prefix_loc lset_aa)
 "heap_t1_C_update") ctxt
\<close>



lemma get_set_aa[GetSetSimp] : "deref_d3_get_aa (deref_d9_set_aa b v) = v"
  apply(simp add:deref_d3_get_aa_def deref_d9_set_aa_def)
  apply(cases v)
  apply simp
  by word_bitwise


(* Getter/Setter relate to their C counterparts *)


context nested_unboxed_record_dargentisa begin

(* !! How to make this proof shorter *)
lemma aux1 : "unat (UCAST(8 \<rightarrow> 32 signed) (UCAST(32 \<rightarrow> 8) x))
         <  2147483648"

  apply (simp add:unat_ucast_up_simp)
  
  apply (rule Orderings.order_class.order.strict_trans1)
  thm WordPolish.INT_MIN_MAX_lemmas(30)[simplified UCHAR_MAX_def]
   apply (rule WordPolish.INT_MIN_MAX_lemmas(30)[simplified UCHAR_MAX_def])
  apply simp
  done


lemma aux3: "0 <=s UCAST(8 \<rightarrow> 32 signed) x"
  apply (rule zero_sle_ucast_up)
  by (simp add: is_down_def target_size source_size)
  


lemma d3_get_aa'_def_alt : "d3_get_aa' x' = do _ <- guard (\<lambda>s. is_valid_t1_C s x');
                                         gets (\<lambda>s. deref_d3_get_aa (heap_t1_C s x')) 
                                      od"

  apply(tactic \<open>  simp_tac
   (@{context} addsimps 
  (List.map (easy_def @{context}) (getter_name :: lget_aa)))  1 \<close>)
  apply(simp add:deref_d3_get_aa_def)
(*
  apply(simp add:d3_get_aa'_def'[simplified 
    d4_get_aa_bb'_def'
    d5_get_aa_bb_part0'_def'
    d6_get_aa_bb_part1'_def'
     d8_get_aa_cc_part0'_def' 
    d7_get_aa_cc'_def' 
 , simplified ]) *)
  
  apply(simp add:aux1 aux3)
  by monad_eq



lemma d9_set_aa'_def_alt :
"d9_set_aa' ptr v = (do _ <- guard (\<lambda>s. is_valid_t1_C s ptr);
        modify (heap_t1_C_update (\<lambda>a. a(ptr := deref_d9_set_aa (a ptr) v))) od )
"        
  apply(tactic \<open>  simp_tac
   (@{context} addsimps 
  (List.map (normal_def @{context}) (setter_name :: lset_aa)))  1 \<close>)

  apply (simp add: deref_d9_set_aa_def)
  apply(simp add:aux3)
  by (monad_eq simp add: comp_def)  
  
end


(* For the type/value relation *)


(* We need the typeclass instances cogent_C_val for t2 *)
local_setup \<open> local_setup_val_rel_type_rel_put_them_in_buckets_for_types "nested_unboxed_record_dargentisa.c" ["t2_C"]\<close>
(* obtained from the version without layout *)
instantiation t1_C :: cogent_C_val
begin
definition type_rel_t1_C_def[TypeRelSimp]: "\<And> typ. type_rel typ (_ :: t1_C itself) \<equiv> 
   (\<exists>aa. typ = RRecord [aa] \<and> type_rel aa TYPE(t2_C))"
definition val_rel_t1_C_def[ValRelSimp]:
    " val_rel uv (x :: t1_C) \<equiv> \<exists>aa. uv = URecord [aa] \<and> val_rel (fst aa) (deref_d3_get_aa x)"
instance ..
end


(* End of non-generated stuff *)

local_setup \<open> local_setup_val_rel_type_rel_put_them_in_buckets "nested_unboxed_record_dargentisa.c" \<close>
local_setup \<open> local_setup_instantiate_cogent_C_heaps_store_them_in_buckets "nested_unboxed_record_dargentisa.c" \<close>
locale Nested_unboxed_record_dargentisa = "nested_unboxed_record_dargentisa" + update_sem_init
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

local_setup \<open> local_setup_heap_rel "nested_unboxed_record_dargentisa.c" \<close>

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

lemmas type_rel_simps[TypeRelSimp] =
  type_rel_word
  type_rel_ptr_def
  type_rel_unit_def
  type_rel_unit_t_C_def
  type_rel_bool_t_C_def

(* 

Non-generated stuff

*)






(*

The following lemmas should be automatically generated by mk_lems (currently
mk_lems does not deal with layouts)

I have manually generated by examining corres_tac failures and getting inspiration
from the onefield_bits example

 *)


(* copied from the Onefield_bits_dargentisa_CorresSetup.

Changes: the type relation for the field, and the getter

In fact useless
 *)
(*
lemma corres_member_t1_C_aa_writable :
"\<Gamma>' ! x = Some (TRecord typ (Boxed ReadOnly ptrl)) \<Longrightarrow>
 val_rel (\<gamma> ! x) x' \<Longrightarrow>
 type_rel (type_repr (TRecord typ (Boxed ReadOnly ptrl))) TYPE(t1_C ptr) \<Longrightarrow>
 type_rel (type_repr (fst (snd (typ ! 0)))) TYPE(t2_C) \<Longrightarrow>
 \<Xi>', [], \<Gamma>' \<turnstile> Member (Var x) 0 : te \<Longrightarrow>
 \<Xi>', [], \<Gamma>' \<turnstile> Var x : TRecord typ (Boxed ReadOnly ptrl) \<Longrightarrow>
 corres state_rel (Member (Var x) 0) (do _ <- guard (\<lambda>s. is_valid_t1_C s x');
                                         gets (\<lambda>s. deref_d3_get_aa (heap_t1_C s x'))
                                      od)
  \<xi>' \<gamma> \<Xi>' \<Gamma>' \<sigma> s 
"
  by(tactic \<open>corres_take_boxed_tac @{context} 1\<close>)
*)

(* Same version corrected from the corres_tac failure *)
lemma corres_member_t1_C_aa_writable[MemberReadOnly] :
"\<Gamma>' ! x = Some (TRecord typ (Boxed ReadOnly ptrl)) \<Longrightarrow>
 val_rel (\<gamma> ! x) x' \<Longrightarrow>
 type_rel (type_repr (TRecord typ (Boxed ReadOnly ptrl))) TYPE(t1_C ptr) \<Longrightarrow>
 type_rel (type_repr (fst (snd (typ ! 0)))) TYPE(t2_C) \<Longrightarrow>
 \<Xi>', [], \<Gamma>' \<turnstile> Member (Var x) 0 : te \<Longrightarrow>
 \<Xi>', [], \<Gamma>' \<turnstile> Var x : TRecord typ (Boxed ReadOnly ptrl) \<Longrightarrow>
 corres state_rel (Member (Var x) 0) (do z <- d3_get_aa' x';
                                               gets (\<lambda>_. z)
                                            od)
  \<xi>' \<gamma> \<Xi>' \<Gamma>' \<sigma> s 
"
  apply(simp add:d3_get_aa'_def_alt)
  by(tactic \<open>corres_take_boxed_tac @{context} 1\<close>)

(* I changed the value relation of v' *)
lemma corres_put_t1_C_aa_writable[PutBoxed] :
"[] \<turnstile> \<Gamma>' \<leadsto> \<Gamma>x | \<Gamma>e \<Longrightarrow>
\<Gamma>' ! x = Some (TRecord typ (Boxed Writable ptrl)) \<Longrightarrow>
type_rel (type_repr (TRecord typ (Boxed Writable ptrl))) TYPE(t1_C ptr) \<Longrightarrow>
val_rel (\<gamma> ! x) x' \<Longrightarrow>
val_rel (\<gamma> ! v) (v' :: t2_C) \<Longrightarrow>
\<Xi>', [], \<Gamma>' \<turnstile> Put (Var x) 0
               (Var v) : TRecord
                          (typ[0 := (fst (typ ! 0), fst (snd (typ ! 0)),
                                     Present)])
                          (Boxed Writable ptrl) \<Longrightarrow> 

length typ = 1 \<Longrightarrow>
corres state_rel (Put (Var x) 0 (Var v))
 (do ptr <- gets (\<lambda>_. x');
     _ <- d9_set_aa' ptr v'
      ;
     _ <- gets (\<lambda>_. ());
     gets (\<lambda>_. ptr)
  od)
 \<xi>' \<gamma> \<Xi>' \<Gamma>' \<sigma> s "

  apply( simp add:d9_set_aa'_def_alt bind_assoc)
by  (tactic \<open>corres_put_boxed_tac @{context} 1\<close>)


(* 

End of non-generated

*)

(* Generating the specialised take and put lemmas *)

local_setup \<open> local_setup_take_put_member_case_esac_specialised_lemmas_ignore_types "nested_unboxed_record_dargentisa.c" ["t1_C"] \<close>
local_setup \<open> fold tidy_C_fun_def' Cogent_functions \<close>

end (* of locale *)


end
