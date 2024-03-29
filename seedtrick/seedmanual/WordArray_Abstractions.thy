(*
  This file contains the locale WordArray which includes the locale generated by AutoCorres from
  the C file containing the word array functions.
  
  This file also includes the proof that the WordArray locale is a subset of the top level 
  correspondence locale.

  This file also contains the various abstractions for the word array functions.
*)

theory WordArray_Abstractions
  imports "../build_random_seed/Random_seed_master_AllRefine"
begin

section "Helper Word Lemmas"

lemma word_mult_cancel_left: 
  fixes a b c :: "('a::len) word"
  assumes "uint c * uint a \<le> uint (max_word :: ('a::len) word)"
  assumes "uint c * uint b \<le> uint (max_word :: ('a::len) word)"
  shows "c * a = c * b \<longleftrightarrow> c = 0 \<or> a = b"
  apply (rule iffI)
   using assms
   apply (unfold word_mult_def word_of_int_def)
    apply (clarsimp simp:Abs_word_inject max_word_def uint_word_of_int m1mod2k uint_0_iff )
   apply fastforce
   done

lemma word_mult_cancel_left_bounded: 
  fixes a b c d :: "('a::len) word"
  assumes "a \<le> d" "b \<le> d"
  assumes "unat c * unat d \<le> unat (max_word :: ('a::len) word)"
  shows "c * a = c * b \<longleftrightarrow> c = 0 \<or> a = b"
  using assms
  apply -
  apply (clarsimp simp: word_le_nat_alt)
  apply (frule_tac i = "unat a" and j = "unat d" and k = "unat c" in mult_le_mono2)
  apply (drule_tac i = "unat b" and j = "unat d" and k = "unat c" in mult_le_mono2)
  by (metis (mono_tags, hide_lams) assms(3) le_unat_uoi mult_left_cancel mult_zero_left not_less_iff_gr_or_eq unat_0 unat_mono word_arith_nat_mult)

section "Helper Functions"

fun is_prim_type :: "type \<Rightarrow> bool"
  where
"is_prim_type (TPrim _) = True" |
"is_prim_type _ = False"

fun is_num_type :: "prim_type \<Rightarrow> bool"
  where
"is_num_type (Num _) = True" |
"is_num_type _ = False"

fun size_of_num_type :: "num_type \<Rightarrow> ptrtyp"
  where
"size_of_num_type U8 = 1" |
"size_of_num_type U16 = 2" |
"size_of_num_type U32 = 4" |
"size_of_num_type U64 = 8"

lemma size_of_num_type_not_zero:
  "size_of_num_type t \<noteq> 0"
  by (case_tac t; clarsimp)

fun zero_num_lit :: "num_type \<Rightarrow> lit"
  where
"zero_num_lit U8 = LU8 0" |
"zero_num_lit U16 = LU16 0" |
"zero_num_lit U32 = LU32 0" |
"zero_num_lit U64 = LU64 0"

fun funarg_type :: "type \<Rightarrow> type"
  where
"funarg_type (TFun a b) = a" |
"funarg_type _ = undefined"

fun funret_type :: "type \<Rightarrow> type"
  where
"funret_type (TFun a b) = b" |
"funret_type _ = undefined"

fun present_type :: "name \<times> type \<times> record_state \<Rightarrow> type"
  where
"present_type (_, t, Present) = t" |
"present_type (_, _, Taken) = undefined"

fun rec_type_list :: "type \<Rightarrow> (name \<times> type \<times> record_state) list"
  where
"rec_type_list (TRecord ts _) = ts" |
"rec_type_list _ = undefined"

fun is_uval_fun :: "('f, 'a, 'l) uval \<Rightarrow> bool"
  where
"is_uval_fun (UFunction _ _) = True" |
"is_uval_fun (UAFunction _ _) = True" |
"is_uval_fun _ = False"

fun uvalfun_to_exprfun :: "('f, 'a, 'l) uval \<Rightarrow> 'f expr"
  where
"uvalfun_to_exprfun (UFunction f ts) = Fun f ts" |
"uvalfun_to_exprfun (UAFunction f ts) = AFun f ts" |
"uvalfun_to_exprfun _ = undefined"

fun is_vval_fun :: "('f, 'a) vval \<Rightarrow> bool"
  where
"is_vval_fun (VFunction _ _) = True" |
"is_vval_fun (VAFunction _ _) = True" |
"is_vval_fun _ = False"

fun vvalfun_to_exprfun :: "('f, 'a) vval \<Rightarrow> 'f expr"
  where
"vvalfun_to_exprfun (VFunction f ts) = Fun f ts" |
"vvalfun_to_exprfun (VAFunction f ts) = AFun f ts" |
"vvalfun_to_exprfun _ = undefined"


section "Helper Frame Lemmas"

lemma valid_ptr_not_in_frame_same:
  "\<lbrakk>frame \<sigma> w \<sigma>' w'; p \<notin> w; \<sigma> p = option.Some x\<rbrakk> \<Longrightarrow> \<sigma>' p = option.Some x"
  apply (clarsimp simp: frame_def)
  apply (erule_tac x = p in allE)
  apply clarsimp
  done

lemma readonly_not_in_frame:
  "\<lbrakk>frame \<sigma> w \<sigma>' w'; \<sigma> p = option.Some v; p \<notin> w\<rbrakk> \<Longrightarrow> p \<notin> w'"
  apply (frule_tac p = p in valid_ptr_not_in_frame_same; simp?)
  by (clarsimp simp: frame_def)

lemma frame_expand:
  "\<lbrakk>frame \<sigma> w \<sigma>' w'; \<sigma> p \<noteq> option.None\<rbrakk> \<Longrightarrow> frame \<sigma> (insert p w) \<sigma>' (insert p w')"
  "\<lbrakk>frame \<sigma> w \<sigma>' w'; \<forall>p\<in>s. \<sigma> p \<noteq> option.None\<rbrakk> \<Longrightarrow> frame \<sigma> (s \<union> w) \<sigma>' (s \<union> w')"
   apply (clarsimp simp: frame_def)
   apply (rule conjI; clarsimp)
  apply (clarsimp simp: frame_def)
  apply (rule conjI; clarsimp)
  done
ML \<open>\<close>
section "WordArray Locale Definition"

text "Embedding of values of abstract types in the Value semantics"
datatype vatyp = VSeed  | VTOther
type_synonym vabstyp = vatyp

locale WordArray = main_pp_inferred begin

  text
  "Maps an abstract type to it type representation."
  definition "wa_abs_repr a \<equiv> case a of
      UWA (TPrim (Num t)) _ _ \<Rightarrow> (''WordArray'', [RPrim (Num t)])
    | _ \<Rightarrow> (''Unknown Abstract Type'', [])"

  text
  "Value typing for word arrays in the Update semantics"
  definition "wa_abs_typing_u a name \<tau>s sig (r :: ptrtyp set) (w :: ptrtyp set) \<sigma> \<equiv>
    (case a of
      UWA (TPrim (Num t)) len arr \<Rightarrow> name = ''WordArray'' \<and> \<tau>s = [TPrim (Num t)] \<and> sig \<noteq> Unboxed \<and>
                      (sigil_perm sig = option.Some ReadOnly \<longrightarrow> w = {} \<and> 
                        r = {arr + size_of_num_type t * i | i. i < len}) \<and>
                      (sigil_perm sig = option.Some Writable \<longrightarrow> r = {} \<and> 
                        w = {arr + size_of_num_type t * i | i. i < len}) \<and>
                      (\<forall>i < len. \<exists>x. \<sigma>(arr + size_of_num_type t * i) = option.Some (UPrim x) \<and> lit_type x = Num t) \<and> 
                      unat (size_of_num_type t)  * unat len \<le> unat (max_word :: ptrtyp)
    | _ \<Rightarrow> name = ''Unknown Abstract Type'' \<and> \<tau>s = [] \<and> r = {} \<and> w = {} \<and> sig = Unboxed)"

  text 
  "Value typing for word arrays in the Value semantics "
  definition "wa_abs_typing_v a name \<tau>s \<equiv>
    (case a of
      VWA (TPrim (Num t)) xs \<Rightarrow> name = ''WordArray'' \<and> \<tau>s = [TPrim (Num t)] \<and> 
      (\<forall>i < length xs. \<exists>x. xs ! i = VPrim x \<and>  lit_type x = Num t)
    | _ \<Rightarrow> name = ''Unknown Abstract Type'' \<and> \<tau>s = [])"


  text 
  "Value relation for word arrays between the Update and Value semantics "
  definition  "wa_abs_upd_val au av name \<tau>s sig (r :: ptrtyp set) (w :: ptrtyp set) \<sigma> \<equiv>
    wa_abs_typing_u au name \<tau>s sig r w \<sigma> \<and> wa_abs_typing_v av name \<tau>s \<and>
    (case au of
      UWA (TPrim (Num t)) len arr \<Rightarrow>
        (case av of 
          VWA (TPrim (Num t)) xs \<Rightarrow> unat len = length xs \<and> \<tau>s = [TPrim (Num t)] \<and>
          (\<forall>i < len. \<exists>x. \<sigma> (arr + size_of_num_type t * i) = option.Some (UPrim x) \<and> xs ! unat i = VPrim x \<and> lit_type x = Num t)
          | _ \<Rightarrow> False)
      | _ \<Rightarrow> (case av of
                VTOther _ \<Rightarrow> True
             |  _ \<Rightarrow> False))"


  text "Helper lemma to show that two indexes in an array are distinct"
  lemma distinct_indices:
    "wa_abs_typing_u (UWA (TPrim (Num t)) len arr) n ts s r w \<sigma> \<Longrightarrow> 
      \<forall>i < len. \<forall>j < len. i = j \<longleftrightarrow> size_of_num_type t * i = size_of_num_type t * j"
  apply clarsimp
  apply (rule iffI)
   apply clarsimp
  apply (clarsimp simp: wa_abs_typing_u_def)
  apply (cut_tac a = i and b = j and c = "size_of_num_type t" and d = len in word_mult_cancel_left_bounded; simp)
  apply (erule disjE; clarsimp)
  apply (case_tac t; clarsimp)
  done

  lemma wa_abs_typing_u_elims:
    "wa_abs_typing_u a ''WordArray'' \<tau>s s r w \<sigma> 
      \<Longrightarrow> \<exists>len arr t. a = UWA (TPrim (Num t)) len arr \<and> \<tau>s = [TPrim (Num t)]"
    "wa_abs_typing_u (UWA (TPrim (Num t)) len arr) n \<tau>s (Boxed ReadOnly ptrl) r w \<sigma>
    \<Longrightarrow> r = {arr + size_of_num_type t * i | i. i < len} \<and> w = {}"
    "wa_abs_typing_u (UWA (TPrim (Num t)) len arr) n \<tau>s (Boxed Writable ptrl) r w \<sigma>
      \<Longrightarrow> r = {} \<and> w = {arr + size_of_num_type t * i | i. i < len}"
    "wa_abs_typing_u a ''WordArray'' \<tau>s s r w \<sigma> \<Longrightarrow> s \<noteq> Unboxed"
    "wa_abs_typing_u (UWA (TPrim (Num t)) len arr) n \<tau>s s r w \<sigma>
      \<Longrightarrow> \<forall>i < len. \<exists>x. \<sigma> (arr + size_of_num_type t * i) = option.Some (UPrim x) \<and> lit_type x = Num t"
    "wa_abs_typing_u (UWA (TPrim (Num t)) len arr) n \<tau>s s r w \<sigma>
      \<Longrightarrow> unat (size_of_num_type t) * unat len \<le> unat (max_word :: ptrtyp)"
    "wa_abs_typing_u (UWA (TPrim (Num t)) len arr) n \<tau>s s r w \<sigma> \<Longrightarrow> n = ''WordArray''"
  by (unfold wa_abs_typing_u_def[abs_def]; clarsimp split: atyp.splits type.splits prim_type.splits)+

lemma wa_abs_typing_v_elims:
  "wa_abs_typing_v a ''WordArray'' \<tau>s \<Longrightarrow> \<exists>t xs. a = VWA (TPrim (Num t)) xs \<and> \<tau>s = [TPrim (Num t)]"
  "wa_abs_typing_v (VWA (TPrim (Num t)) xs) n \<tau>s 
    \<Longrightarrow> \<forall>i < length xs. \<exists>x. xs ! i = VPrim x \<and> lit_type x = Num t"
  "wa_abs_typing_v (VWA (TPrim (Num t)) xs) n \<tau>s  \<Longrightarrow> n = ''WordArray''"
  by (unfold wa_abs_typing_v_def[abs_def]; clarsimp split: vatyp.splits type.splits prim_type.splits)+

lemma wa_abs_upd_val_elims:
  "wa_abs_upd_val au av n \<tau>s s r w \<sigma> \<Longrightarrow> wa_abs_typing_u au n \<tau>s s r w \<sigma>"
  "wa_abs_upd_val au av n \<tau>s s r w \<sigma> \<Longrightarrow> wa_abs_typing_v av n \<tau>s"
  "wa_abs_upd_val (UWA \<tau> len arr) (VWA \<tau> xs) n \<tau>s s r w \<sigma>
    \<Longrightarrow> unat len = length xs"
  "wa_abs_upd_val (UWA (TPrim (Num t)) len arr) (VWA (TPrim (Num t)) xs) n \<tau>s s r w \<sigma>
    \<Longrightarrow> \<forall>i < len. \<exists>x. \<sigma> (arr + size_of_num_type t * i) = option.Some (UPrim x) \<and> 
      xs ! unat i = VPrim x \<and> lit_type x = Num t"
  by (unfold wa_abs_upd_val_def[abs_def]; 
      clarsimp split: atyp.splits vatyp.splits type.splits prim_type.splits)+

lemma wa_abs_typing_u_update:
  "\<lbrakk>wa_abs_typing_u (UWA (TPrim (Num t)) len arr) n \<tau>s (Boxed Writable ptrl) r w \<sigma>;
    i < len; lit_type v = Num t\<rbrakk> 
    \<Longrightarrow> wa_abs_typing_u (UWA (TPrim (Num t)) len arr) n \<tau>s (Boxed Writable ptrl) r w 
      (\<sigma> ((arr + size_of_num_type t * i) \<mapsto> (UPrim v)))"
  by (clarsimp simp: wa_abs_typing_u_def)

lemma wa_abs_typing_v_update:
  "\<lbrakk>wa_abs_typing_v (VWA (TPrim (Num t)) xs) n \<tau>s; i < length xs; lit_type v = Num t\<rbrakk> 
    \<Longrightarrow> wa_abs_typing_v (VWA (TPrim (Num t)) (xs[i := VPrim v])) n \<tau>s"
  apply (clarsimp simp: wa_abs_typing_v_def)
  apply (erule_tac x = ia in allE)
  apply (clarsimp simp: nth_list_update)
  done

lemma wa_abs_upd_val_update:
  "\<lbrakk>wa_abs_upd_val (UWA (TPrim (Num t)) len arr) (VWA (TPrim (Num t)) xs) n \<tau>s (Boxed Writable ptrl) r w \<sigma>;
    i < len; lit_type v = Num t\<rbrakk>
    \<Longrightarrow> wa_abs_upd_val (UWA (TPrim (Num t)) len arr) (VWA (TPrim (Num t)) (xs[unat i := VPrim v])) n 
      \<tau>s (Boxed Writable ptrl) r w (\<sigma> ((arr + size_of_num_type t * i) \<mapsto> (UPrim v)))"
  apply (clarsimp simp: wa_abs_upd_val_def)
  apply (drule wa_abs_typing_u_update; simp?; clarsimp)
  apply (drule_tac i = "unat i" in wa_abs_typing_v_update; simp add: word_less_nat_alt; clarsimp)
  apply (rule conjI; clarsimp simp: nth_list_update)
  apply (cut_tac a = ia and b = i and c = "size_of_num_type t" and d = len in word_mult_cancel_left_bounded; simp?)
     apply (clarsimp simp: word_less_nat_alt word_le_nat_alt)+
   apply (fastforce dest: wa_abs_typing_u_elims(6))
  apply (case_tac t; clarsimp)
  done

end

section "Sublocale Proof"

text 
  "Here we prove that our value typing relations and value relations for word arrays satisfies
   Cogent's FFI constraints."

sublocale WordArray \<subseteq> Generated_cogent_shallow _ wa_abs_repr wa_abs_typing_v wa_abs_typing_u wa_abs_upd_val
  apply (unfold wa_abs_repr_def[abs_def] wa_abs_typing_v_def[abs_def] wa_abs_typing_u_def[abs_def] wa_abs_upd_val_def[abs_def])
  apply (unfold_locales; clarsimp split: vatyp.splits atyp.splits)
               apply (clarsimp split: type.splits prim_type.splits)
              apply (clarsimp split: type.splits prim_type.splits)
              apply (rename_tac s r w \<sigma> len arr t)
              apply (case_tac s; clarsimp; rename_tac perm ptrl; case_tac perm; clarsimp)
             apply (clarsimp split: type.splits prim_type.splits)
             apply (case_tac s; clarsimp; rename_tac perm; case_tac perm; clarsimp)
            apply (clarsimp split: type.splits prim_type.splits) 
            apply (case_tac s; clarsimp; rename_tac perm; case_tac perm; clarsimp)
           apply (clarsimp split: type.splits prim_type.splits)
           apply (case_tac s; clarsimp; rename_tac perm; case_tac perm; clarsimp)
          apply (clarsimp split: type.splits prim_type.splits)
          apply (case_tac s; clarsimp; rename_tac perm; case_tac perm; clarsimp; blast)
         apply (clarsimp split: type.splits prim_type.splits)
         apply (case_tac s; clarsimp; rename_tac perm; case_tac perm; clarsimp; case_tac s'; clarsimp)
        apply (clarsimp split: type.splits prim_type.splits)
       apply (clarsimp split: type.splits prim_type.splits)
       apply (rename_tac len arr t i)
       apply (erule_tac x = i in allE; clarsimp)
       apply (rule_tac x = x in exI)
       apply (clarsimp simp: frame_def)
       apply (erule_tac x = "arr + size_of_num_type t * i" in allE; clarsimp)
       apply (case_tac s; clarsimp; rename_tac perm; case_tac perm; clarsimp)
        apply (drule_tac x = "arr + size_of_num_type t * i" in orthD1; clarsimp)
        apply (rule_tac x = i in exI; clarsimp)
       apply (drule_tac x = "arr + size_of_num_type t * i" in orthD1; clarsimp)
       apply (rule_tac x = i in exI; clarsimp)
      apply (clarsimp split: type.splits prim_type.splits)
      apply (case_tac s; clarsimp; rename_tac perm; case_tac perm; clarsimp)
     apply (clarsimp split: type.splits prim_type.splits)
     apply (case_tac s; clarsimp; rename_tac perm ptrl; case_tac perm; clarsimp)
    apply (clarsimp split: type.splits prim_type.splits)
   apply (clarsimp split: type.splits prim_type.splits)
   apply (rename_tac xs len arr t)
   apply (rule conjI; clarsimp)
    apply (erule_tac x = i in allE; clarsimp)+
    apply (rule_tac x = x in exI)
    apply (clarsimp simp: frame_def)
    apply (erule_tac x = "arr + size_of_num_type t * i" in allE; clarsimp)
    apply (case_tac s; clarsimp; rename_tac perm; case_tac perm; clarsimp)
     apply (drule_tac x = "arr + size_of_num_type t * i" in orthD1; clarsimp)
     apply (rule_tac x = i in exI; clarsimp)
    apply (drule_tac x = "arr + size_of_num_type t * i" in orthD1; clarsimp)
    apply (rule_tac x = i in exI; clarsimp)
   apply (erule_tac x = i in allE; clarsimp)+
   apply (clarsimp simp: frame_def)
   apply (erule_tac x = "arr + size_of_num_type t * i" in allE; clarsimp)
   apply (case_tac s; clarsimp; rename_tac perm; case_tac perm; clarsimp)
    apply (drule_tac x = "arr + size_of_num_type t * i" in orthD1; clarsimp)
    apply (rule_tac x = i in exI; clarsimp)
   apply (drule_tac x = "arr + size_of_num_type t * i" in orthD1; clarsimp)
   apply (rule_tac x = i in exI; clarsimp)
  apply (clarsimp split: type.splits prim_type.splits)
  done

section "Helper Elim Lemmas"

context WordArray begin

inductive_cases u_t_primtE: "upd.uval_typing \<Xi>' \<sigma> u (TPrim l) r w"
inductive_cases u_t_unittE: "upd.uval_typing \<Xi>' \<sigma> u TUnit r w"
inductive_cases u_t_funafuntE: "upd.uval_typing \<Xi>' \<sigma> f (TFun a b) r w"
inductive_cases u_t_rectE: "upd.uval_typing \<Xi>' \<sigma> u (TRecord ts s) r w"
inductive_cases u_t_r_contE: "upd.uval_typing_record \<Xi>' \<sigma> us ts r w"
inductive_cases v_t_primtE : "val.vval_typing \<Xi>' v (TPrim l)"
inductive_cases u_v_t_primtE : "upd_val_rel \<Xi>' \<sigma> u v (TPrim l) r w"
inductive_cases u_v_t_funE: "upd_val_rel \<Xi>' \<sigma> (UFunction f ts) v t r w"
inductive_cases u_v_t_afunE: "upd_val_rel \<Xi>' \<sigma> (UAFunction f ts) v t r w"

end (* of context *)

end