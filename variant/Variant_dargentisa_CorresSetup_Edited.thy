(*
This file is generated by Cogent

*)

theory Variant_dargentisa_CorresSetup_Edited
imports "CogentCRefinement.Deep_Embedding_Auto"
"CogentCRefinement.Cogent_Corres"
"CogentCRefinement.Tidy"
"CogentCRefinement.Heap_Relation_Generation"
"CogentCRefinement.Type_Relation_Generation"
"CogentCRefinement.Dargent_Custom_Get_Set"
"build_variant/Variant_dargentisa_ACInstall"
"build_variant/Variant_dargentisa_TypeProof"
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

(*
Non-generated
*)




(* 
This ML function generate custom getters/setters in Isabelle from
the C custom getters/setters.

More precisely, the involved steps are:
1. get the names of custom C getters/setters from the table file
2. prove a simplified definition of them by unfolding the auxiliary 
   called C functions and using Tidy lemmas (thus produces Cgetter_def' 
   lemmas in the context). 
3. infer an isabelle definition of custom getter/setters by inspecting
   these simplified definition (and performing further simplification, such
   as removing all guards)

The simplified definitions are thought to be used later when proving that
the C and isabelle custom getters/setters match.

 *)


setup \<open>generate_isa_getset_records_for_file "variant_dargentisa.c" @{locale variant_dargentisa} \<close>


context variant_dargentisa begin

(* This prints the get/set lemmas that should be proven *)
ML \<open> val lems = mk_getset_lems "variant_dargentisa.c" @{context} \<close>
ML \<open>lems  |> map (string_of_getset_lem @{context})|> map tracing\<close>

(* This proves the get/set lemmas (currently by cheating) *)
(*
local_setup \<open>local_setup_getset_lemmas "variant_dargentisa.c"\<close>
*)
end

context variant_dargentisa begin



(* Example: 
 1 original C getter definition, 
 2 simplified unfolded definition
 3 isabelle C getter definition
*)
thm d3_get_a'_def d3_get_a'_def' deref_d3_get_a_def


end
(* the value/type relation were adapted to custom layouts *)
local_setup \<open> local_setup_val_rel_type_rel_put_them_in_buckets "variant_dargentisa.c" \<close>
thm val_rel_t1_C_def

(* 
Now are the various lemmas regarding custom getter/setters. We call them get/set lemmas

It is easy to automate the generation of the statements. The proof automation is, I think, the
remaining hard part (because we never know if we have addressed all the cases). 




https://github.com/amblafont/AutoCorres
* Different kind of lemmas

There are 4 different types of lemmas. I write the naive version below

1. `get o set = id`
2. `get_a o set_b = get_a`
3. `C_get = isabelle_get`
4. `C_set = isabelle_set`

(r : Simple)
get_b (set_b r (B u)) <> B u

B u = { tag = B, A_field = ?, B_field = u, .. }

get_b (r' : bytes[n]) = { tag = B, A_field = ?, B_field = . ,  }

r' = [ . . . . . ]
        [  A  ]
      [ B  ]
 
The first is too naive because it does not hold for variants: if a field is a variant,
then the associated getter erases the irrelevant fields. Thus equality is too strong,
but we can replace them with value relation preservation:

1. `val_rel x new_val \<Longrightarrow> val_rel x (get (set t new_val))`




* Where to generate these lemmas

I have written a function similar to mk_lems which generate get/set lemmas.

The reason I did not extend mk_lems is that the lemmas that mk_lems automatically proves about records
require the get/set lemmas to be proven first. But then, these lemmas are proven in an unspecified
order.  I did not dare breaking the "invariant" that lemmas generated by mk_lems can be proven in 
any order.

 *)

context variant_dargentisa begin

(* This prints the get/set lemmas that should be proven *)
ML \<open> val lems = mk_getset_lems "variant_dargentisa.c" @{context} \<close>
ML \<open>lems  |> map (string_of_getset_lem @{context})|> map tracing\<close>

(* This proves the get/set lemmas (currently by cheating) *)
(*
local_setup \<open>local_setup_getset_lemmas "variant_dargentisa.c"\<close>
*)


(* Here we try to prove the get/set lemmas manually.
This is the hard part to automate.
*)


lemma get_set_a' : 
(* The value relation is only there to ensure that the tag
is the right one *)
  "val_rel x v \<Longrightarrow> deref_d3_get_a (deref_d27_set_a b v) = v"
  apply(simp add:deref_d3_get_a_def deref_d27_set_a_def)
  apply(cases v)
  apply simp
  apply(rule conjI)
   apply (simp add:ValRelSimp)
   apply blast   
  by (word_bitwise)

lemma get_set_a [GetSetSimp] : 
(* The value relation is only there to ensure that the tag
is the right one *)
  "val_rel x v \<Longrightarrow> val_rel x (deref_d3_get_a (deref_d27_set_a b v))"
  apply(simp add:get_set_a')
  done



lemma aux : "(UCAST(32 \<rightarrow> 8)
          ((data_C b.[4] && 0xFF00FFFF ||
            (0xFF && UCAST(8 \<rightarrow> 32)  x6 && 0xFF << 16) >>
            16) &&
           0xFF) = x6)"
  by word_bitwise
lemma aux2 : "(A \<and> (A \<longrightarrow> B)) \<longleftrightarrow> A \<and> B "
  by fastforce

lemma aux3 : " ((x && 0xFF00FFFF || 0x10000) && 0xFFFFFF ||
        (0xFF && UCAST(8 \<rightarrow> 32) w && 0xFF << 24) >>
        16) &&
       0xFF =
       1"
  apply word_bitwise
  done

lemma stupid : "P \<Longrightarrow> (Q \<longrightarrow> P)"
  by fast


lemma get_set_b[GetSetSimp]  : "val_rel x v \<Longrightarrow> val_rel x (deref_d9_get_b (deref_d32_set_b b v))"

  apply(simp only:deref_d9_get_b_def deref_d32_set_b_def )
  apply (simp only: HOL.if_split)
 
  apply safe
 
  find_theorems "?P (if _ then _ else _) \<longleftrightarrow> _"
  apply (simp only: ValRelSimp)
  apply (simp add:TAG_ENUM_A_def TAG_ENUM_B_def TAG_ENUM_C_def TAG_ENUM_D_def TAG_ENUM_E_def )

  apply (simp add:aux3)
  apply (elim exE conjE disjE)
      apply (simp)
  thm back_subst
      apply(rule_tac P="val_rel uval"  in back_subst )
       apply assumption
      apply (thin_tac _)+
      apply word_bitwise


  
      apply (simp add:aux2)

      apply (intro conjI)
          apply(thin_tac _)+
          apply word_bitwise
   

  
(*  apply (simp add:aux3) *)
  thm impI
 
    apply word_bitwise



      apply clarsimp
      apply(subgoal_tac "
(data_C b.[0] && 0xFF00FFFF || 0x10000) && 0xFFFFFF ||
        (0xFF && UCAST(8 \<rightarrow> 32) z && 0xFF << 24) >>
        16) &&
       0xFF) = z")
   
  apply (intro impI)
(*  this removes a lot of impossible cases  *)
  
  
  apply(cases v)

  apply (rule conjI impI)+
     apply(clarsimp)
    apply(clarsimp)
    apply(rule_tac P="val_rel uval" and a=x3  in back_subst )
     apply assumption
    apply word_bitwise
   apply clarsimp
   apply word_bitwise

  apply (rule conjI impI)+
     apply(clarsimp)
     apply word_bitwise

    apply(clarsimp)  
    apply(rule FalseE)
    apply word_bitwise
   apply clarsimp
   apply (rule conjI impI)+
    apply(rule_tac P="val_rel uval" and a=x4 in back_subst )
     apply assumption
    apply word_bitwise
   apply word_bitwise

  apply (rule conjI impI)+

     apply clarsimp
     apply word_bitwise
    apply clarsimp
    apply(rule FalseE)
    apply word_bitwise
   apply clarsimp
   apply (rule conjI impI)+
    apply word_bitwise
   apply (rule conjI impI)+
    apply(rule_tac P="val_rel uval" and a=x5 in back_subst )
     apply assumption
    apply word_bitwise
   apply (word_bitwise)

  apply (rule conjI impI)+
     apply clarsimp
     apply word_bitwise
    apply clarsimp
    apply(rule FalseE)
    apply word_bitwise
   apply clarsimp
   apply (rule conjI impI)+
    apply word_bitwise
   apply (rule conjI impI)+
    apply word_bitwise
   apply (rule conjI impI)+
    apply(rule_tac P="val_rel uval" and a=x6 in back_subst )
     apply assumption    
    apply (simp  add:aux)
   apply word_bitwise

  apply (rule conjI impI)+
    apply clarsimp
    apply word_bitwise
   apply clarsimp
   apply(rule FalseE)
   apply word_bitwise

  apply (rule conjI impI)+
    apply clarsimp
    apply word_bitwise
   apply clarsimp
   apply(rule FalseE)
   apply word_bitwise

  apply (rule conjI impI)+
    apply clarsimp
    apply word_bitwise
   apply clarsimp
   apply(rule FalseE)
   apply word_bitwise

  apply clarsimp
  apply (rule conjI impI)+
    
   apply word_bitwise
  apply (rule conjI impI)+

  apply(rule_tac P="val_rel uval" and a=x2 in back_subst )
   apply assumption
  apply word_bitwise
  done





lemma aux': "UCAST(32 \<rightarrow> 8) ((x && 0xFF00FFFF || 0x20000 >> 8) && 0xFF) =
    UCAST(32 \<rightarrow> 8) ((x >> 8) && 0xFF)"
  by word_bitwise


lemma get_a_set_b[GetSetSimp] : "deref_d3_get_a (deref_d32_set_b b v) = deref_d3_get_a b"
  apply(simp add:deref_d3_get_a_def deref_d32_set_b_def
)
(* This removes contradictory cases, such as TAG_ENUM_B = TAG_ENUM_C *)
  apply (simp add:TAG_ENUM_A_def TAG_ENUM_B_def TAG_ENUM_C_def TAG_ENUM_D_def TAG_ENUM_E_def )
  apply (rule conjI impI)+  
(* why doesn't it work ? *)
   apply (word_bitwise)
   apply (simp add:aux')

  apply (rule stupid conjI)+
   apply word_bitwise
  apply (rule stupid conjI)+
   apply word_bitwise
  apply (rule stupid conjI)+
   apply word_bitwise
  apply (rule stupid conjI)+
  apply word_bitwise
  done

lemma get_b_set_a[GetSetSimp] : "deref_d9_get_b (deref_d27_set_a b v) = deref_d9_get_b b"
apply(simp add:deref_d9_get_b_def deref_d27_set_a_def)
(* This removes contradictory cases, such as TAG_ENUM_B = TAG_ENUM_C *)
  apply (simp add:TAG_ENUM_A_def TAG_ENUM_B_def TAG_ENUM_C_def TAG_ENUM_D_def TAG_ENUM_E_def )


  apply (rule conjI impI)+
   apply word_bitwise
  apply (rule conjI impI)+
   apply word_bitwise
  apply (rule conjI impI)+
   apply word_bitwise
  apply (rule conjI impI)+
   apply word_bitwise
  apply (rule conjI impI)+
   apply word_bitwise
  apply (rule conjI impI)+
   apply word_bitwise
  apply (rule conjI impI)+
   apply word_bitwise
  apply (rule conjI impI)+
   apply word_bitwise
  apply (rule conjI impI)+
   apply word_bitwise
  apply (rule conjI impI)+
   apply word_bitwise
  done


(* 
These lemmas correspond to these kind of statements

3. `C_get = isabelle_get`
4. `C_set = isabelle_set
*)

lemma d3_get_a_def_alt[GetSetSimp] : "d3_get_a' x' = do _ <- guard (\<lambda>s. is_valid_t1_C s x');
                                         gets (\<lambda>s. deref_d3_get_a (heap_t1_C s x')) 
                                      od"
by (tactic \<open>custom_get_set_monadic_direct_tac @{context} 1\<close>)


lemma d9_get_b_def_alt[GetSetSimp] : "d9_get_b' x' = do _ <- guard (\<lambda>s. is_valid_t1_C s x');
                                         gets (\<lambda>s. deref_d9_get_b (heap_t1_C s x')) 
                                      od"
by (tactic \<open>custom_get_set_monadic_direct_tac @{context} 1\<close>)

lemma d27_set_a'_def_alt[GetSetSimp] :
"d27_set_a' ptr v = (do _ <- guard (\<lambda>s. is_valid_t1_C s ptr);
        modify (heap_t1_C_update (\<lambda>a. a(ptr := deref_d27_set_a (a ptr) v))) od )
"    
by (tactic \<open>custom_get_set_monadic_direct_tac @{context} 1\<close>)

lemma d32_set_b'_def_alt[GetSetSimp] :
"d32_set_b' ptr v = (do _ <- guard (\<lambda>s. is_valid_t1_C s ptr);
        modify (heap_t1_C_update (\<lambda>a. a(ptr := deref_d32_set_b (a ptr) v))) od )
"        
by (tactic \<open>custom_get_set_monadic_direct_tac @{context} 1\<close>)
end

(*

Once the get/set lemmas have been proven, the rest follows, as 
- the lemma statement generation has been adapted to record with custom layouts
- the specialised tactics have been adapted to take into account custom layouts,
using the lemma bucket GetSetSimp.

*)

(*

In summary, the remaining tasks are:
1. (easy) automate the generation of value/type relations for custom layouts
2. (easy) automate the generation of get/set lemma statements
3. (hard) automate the proof of get/set lemmas

*)


(* 
End of non-generated
*)

local_setup \<open> local_setup_val_rel_type_rel_put_them_in_buckets "variant_dargentisa.c" \<close>
local_setup \<open> local_setup_instantiate_cogent_C_heaps_store_them_in_buckets "variant_dargentisa.c" \<close>
locale Variant_dargentisa = "variant_dargentisa" + update_sem_init
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

local_setup \<open> local_setup_heap_rel "variant_dargentisa.c" \<close>

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

(* Generating the specialised take and put lemmas *)

local_setup \<open> local_setup_take_put_member_case_esac_specialised_lemmas "variant_dargentisa.c" \<close>
local_setup \<open> fold tidy_C_fun_def' Cogent_functions \<close>

end (* of locale *)


end
