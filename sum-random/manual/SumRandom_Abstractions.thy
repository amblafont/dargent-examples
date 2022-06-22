(*
  This file contains the locale WordArray which includes the locale generated by AutoCorres from
  the C file containing the word array functions.
  
  This file also includes the proof that the WordArray locale is a subset of the top level 
  correspondence locale.

  This file also contains the various abstractions for the word array functions.
*)

(* NEED TO FIX COGENT Update Semantics TO INCLUDE STORE in FFI locale similar to FFI branch  *)

theory SumRandom_Abstractions
imports 
  "../build_random_seed/Random_seed_master_AllRefine"
  CogentCRefinement.Value_Relation
begin

section "SumRandom Locale Definition"

text \<open>Embedding of values of abstract types in the Value semantics\<close>

text \<open>
Essentially, you want to say that type 
C 
is isomorphic to type 
string. 
Normally, you would do that with the command typedef in Isabelle, 
which declares a new type and establishes the isomorphism with the 
non-empty set. This is the very basic mechanism to introduce new types in 
HOL, i.e., every other package for type declarations (like record and 
datatype) build on typedef. The isomorphism is established by declaring 
two constants Abs and Reps between the old type and the new type and by 
asserting the axiom type_definition Rep Abs A where A is the non-empty 
subset of the old type. Thus, if you want to later refine C to type string, 
you can just declare new functions 
  Abs_C :: string => C and 
  Rep_C :: C => string 
and axiomatise type_definition Rep_C Abs_C UNIV using axiomatization. 
After that, you know that C is isomorphic to string and you can use Abs_C 
and Rep_C as coercions.\<close>

datatype utyp = TSeed ptrtyp  | TOther

consts Abs_utyp :: "utyp \<Rightarrow> abstyp"
consts Rep_utyp :: "abstyp \<Rightarrow> utyp" 

axiomatization
where
  utyp_eq: "type_definition Rep_utyp Abs_utyp UNIV"

declare utyp_eq [simp]

datatype vtyp = VSeed word8 | VOther
(*
consts Abs_vtyp :: "vtyp \<Rightarrow> abstyp"
consts Rep_vtyp :: "abstyp \<Rightarrow> vtyp" 

axiomatization
where
  vtyp_eq: "type_definition Rep_vtyp Abs_vtyp UNIV"

declare vtyp_eq [simp]
*)

locale SumRandom = random_seed_master_pp_inferred 
begin

text \<open>maps an abstract type to it type representation\<close>


definition 
  seed_abs_repr :: "abstyp \<Rightarrow> name \<times> repr list" where
  "seed_abs_repr a \<equiv> 
    case (Rep_utyp a) of
       TSeed _ \<Rightarrow> (''Seed'', [])
    | _ \<Rightarrow> (''Unknown Abstract Type'', [])"


text \<open>"Value typing for word arrays in the Update semantics\<close>

definition 
  seed_abs_typing_u' :: 
   "utyp \<Rightarrow> name \<Rightarrow> type list \<Rightarrow> sigil \<Rightarrow> ptrtyp set \<Rightarrow> ptrtyp set \<Rightarrow> 
    bool" (* NEED TO FIX COGENT FFI TO INCLUDE STORE and pass as argument (funtyp, abstyp, ptrtyp) store \<Rightarrow> *)
where
  "seed_abs_typing_u' a name \<tau>s sig r w  \<equiv>
   (case a of
      TSeed s \<Rightarrow> 
        name = ''Seed'' \<and> 
        \<tau>s = [] \<and> 
        ((sig \<noteq> Unboxed \<and> sigil_perm sig = option.Some Writable \<and> w = {s} \<and> r = {}) \<or>
         (sig \<noteq> Unboxed \<and> sigil_perm sig = option.Some ReadOnly \<and> w = {} \<and> r = {s})) \<and>
         (\<forall>(\<sigma>::(funtyp, abstyp, ptrtyp) store) x. \<sigma> s = option.Some (UPrim x) \<and> lit_type x = Num U8)
      | _ \<Rightarrow> 
        name = ''Unknown Abstract Type'' \<and> \<tau>s = [] \<and> 
        sig = Unboxed \<and> r = {} \<and> w = {})"

definition "seed_abs_typing_u \<equiv> seed_abs_typing_u' \<circ> Rep_utyp"

end

section \<open>Sublocale Proof\<close>
(*
sublocale 
  SumRandom \<subseteq> 
   Random_seed_master _ seed_abs_typing_u seed_abs_repr
  apply (unfold seed_abs_typing_u_def seed_abs_repr_def, unfold_locales)

      
        apply   (case_tac "Rep_abstyp av", case_tac s; fastforce)+
apply   (case_tac "Rep_abstyp av", case_tac s) apply clarsimp
  apply fastforce
  apply (auto )
  apply
 sigil.distinct(1) sigil_perm.simps(1))
  apply clarsimp
  apply   (case_tac "Rep_abstyp av"; (split sigil.splits)?; simp)
apply   (case_tac "Rep_abstyp av"; (split sigil.splits)?; simp)
*)
print_locale Random_seed_master_cogent_shallow
print_locale Random_seed_master

context SumRandom
begin

text \<open>Value typing for word arrays in the Value semantics\<close>

definition 
  seed_abs_typing_v :: "vtyp \<Rightarrow> name \<Rightarrow> type list \<Rightarrow> bool"
where
  "seed_abs_typing_v a name \<tau>s \<equiv>
   (case a of
      VSeed _ \<Rightarrow> 
        name = ''Seed'' \<and> \<tau>s = []  
      | _ \<Rightarrow> 
        name = ''Unknown Abstract Type'' \<and> \<tau>s = [])"


text \<open>Value relation for word arrays between the Update and Value semantics\<close>

definition 
  seed_abs_upd_val' ::
   "utyp \<Rightarrow> vtyp \<Rightarrow> name \<Rightarrow> Cogent.type list \<Rightarrow> sigil \<Rightarrow> 
    ptrtyp set \<Rightarrow> ptrtyp set \<Rightarrow>  bool" (*FIX: (funtyp, abstyp, ptrtyp) store \<Rightarrow> *)
where
  "seed_abs_upd_val' au av name \<tau>s sig r w  \<equiv>
    (seed_abs_typing_u' au name \<tau>s sig r w  \<and>
     seed_abs_typing_v av name \<tau>s \<and>
     (case au of
      TSeed p \<Rightarrow> (\<forall>(\<sigma>::(funtyp, abstyp, ptrtyp) store). \<exists>w. \<sigma> p = option.Some (UPrim (LU8 w)) \<and> av = VSeed w)
      | TOther \<Rightarrow> av= VOther ))"

definition "seed_abs_upd_val \<equiv> seed_abs_upd_val' \<circ> Rep_utyp"

text 
\<open>The value typing and value relation satisfy Cogent's FFI constraints\<close>

(* Value Semantics locale assumption *)

lemma seed_abs_typing_bang_v : 
  "seed_abs_typing_v av n \<tau>s \<Longrightarrow> 
   seed_abs_typing_v av n (map bang \<tau>s)" 
   (*     
  apply    (case_tac "Rep_abstyp av"; 
         clarsimp simp add: seed_abs_repr_def seed_abs_typing_u_def; 
case_tac s; clarsimp) using seed_abs_repr_def seed_abs_typing_u_def sledgehammer
*)
  sorry

(* Update Semantics update_sem locale assumptions *)

lemma seed_abs_typing_bang_u: 
  "seed_abs_typing_u av n \<tau>s s r w \<Longrightarrow> 
   seed_abs_typing_u av n (map bang \<tau>s) (bang_sigil s) (r \<union> w) {}"
  sorry

lemma seed_abs_typing_noalias: 
  "seed_abs_typing_u av n \<tau>s s r w \<Longrightarrow> 
   r \<inter> w = {}"
  sorry

lemma seed_abs_typing_readonly: 
  "sigil_perm s \<noteq> Some Writable \<Longrightarrow> 
   seed_abs_typing_u av n \<tau>s s r w \<Longrightarrow> w = {}"
  sorry

lemma seed_abs_typing_escape: 
  "\<lbrakk> sigil_perm s \<noteq> Some ReadOnly; 
     [] \<turnstile>* \<tau>s :\<kappa> k; E \<in> k; 
     seed_abs_typing_u av n \<tau>s s r w\<rbrakk> \<Longrightarrow> 
   r = {}"
  sorry
lemma seed_abs_typing_valid: 
  "seed_abs_typing_u av n \<tau>s s r w \<Longrightarrow> p \<in> r \<union> w \<Longrightarrow> \<sigma> p \<noteq> None"
  sorry

lemma seed_abs_typing_unique_repr:
 "\<lbrakk> seed_abs_typing_u av n \<tau>s s r w;
    seed_abs_typing_u av n' \<tau>s' s' r' w'\<rbrakk> \<Longrightarrow>
  type_repr (TCon n \<tau>s s) = type_repr (TCon n' \<tau>s' s')"
  sorry

lemma seed_abs_typing_repr : 
  "seed_abs_typing_u av n \<tau>s s r w \<Longrightarrow> seed_abs_repr av = (n, map type_repr \<tau>s)"
  sorry


(* Correspondance locale assumptions *)


lemma seed_abs_upd_val_to_vval_typing: 
  "seed_abs_upd_val u v n \<tau>s s l r \<Longrightarrow> seed_abs_typing_v v n \<tau>s"
  sorry

lemma seed_abs_upd_val_to_uval_typing: 
  "seed_abs_upd_val u v n \<tau>s s l r \<Longrightarrow> seed_abs_typing_u u n \<tau>s s l r"
  sorry

lemma seed_abs_upd_val_bang : 
  "seed_abs_upd_val au av n \<tau>s s r w \<Longrightarrow> 
    seed_abs_upd_val au av n (map bang \<tau>s) (bang_sigil s) (r \<union> w) {}"
  sorry

end

section \<open>Sublocale Proof\<close>

text 
\<open>The value typing and value relation satisfy Cogent's FFI constraints\<close>

sublocale 
  SumRandom \<subseteq>  
   Random_seed_master_cogent_shallow _ 
       seed_abs_repr 
       seed_abs_typing_v 
       seed_abs_typing_u 
       seed_abs_upd_val
  apply  (unfold_locales)
            apply (simp add: seed_abs_typing_bang_v) 
           apply (simp add: seed_abs_typing_bang_u) 
          apply (simp add: seed_abs_typing_noalias) 
         apply (simp add: seed_abs_typing_readonly) 
        apply (simp add: seed_abs_typing_escape) 
       apply (simp add: seed_abs_typing_valid) (*FIX sigma in FFI*)
      apply (rule seed_abs_typing_unique_repr, assumption, assumption)
     apply (simp add: seed_abs_typing_repr) 
    apply (simp add: seed_abs_upd_val_to_vval_typing)
   apply (simp add: seed_abs_upd_val_to_uval_typing)
  apply (simp add: seed_abs_upd_val_bang)
  done


end