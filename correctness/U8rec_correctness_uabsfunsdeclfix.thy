(*
This file is generated by Cogent

*)

theory U8rec_correctness_uabsfunsdeclfix
  imports "build_u8rec/U8rec_uabsfunsdeclfix_AllRefine"
Cogent.ValueSemantics
begin

lemmas type_simps = U8rec_uabsfunsdeclfix_TypeProof.main_type_def
  U8rec_uabsfunsdeclfix_TypeProof.abbreviatedType1_def
lemmas \<Xi>_simps =  \<Xi>_def assoc_lookup.simps type_simps


overloading \<xi>0 \<equiv> \<xi>_0
begin
definition \<xi>0 :: "(funtyp, abstyp, ptrtyp) uabsfuns"
  where
"\<xi>0 f x y = False"
  

end

definition val_abs_typing where "val_abs_typing \<equiv> \<lambda> _ _ _ _. False"
definition upd_abs_typing where "upd_abs_typing \<equiv> \<lambda> _ _ _ _ _ _ _  _. False"
definition abs_upd_val where "abs_upd_val \<equiv> \<lambda> _ _ _ _ _ _ _ _ _. False"
definition \<xi>\<^sub>m where "\<xi>\<^sub>m \<equiv> \<lambda> _ _ _. False"
definition \<xi>\<^sub>p where "\<xi>\<^sub>p \<equiv> \<lambda> _ _ _. False"
definition abs_repr where "abs_repr \<equiv> \<lambda> _. ([],[])"

lemmas abs_defs = val_abs_typing_def upd_abs_typing_def abs_upd_val_def \<xi>\<^sub>m_def \<xi>0_def

locale Abstract begin
end

sublocale Abstract \<subseteq> update_sem upd_abs_typing abs_repr
  by(simp add:abs_defs;unfold_locales;simp)

sublocale Abstract \<subseteq> update_sem_init upd_abs_typing abs_repr 
  by (unfold_locales)

sublocale Abstract \<subseteq> value_sem val_abs_typing
  by(simp add:abs_defs;unfold_locales;simp)

sublocale Abstract \<subseteq> U8rec_uabsfunsdeclfix _ upd_abs_typing abs_repr
  by (unfold_locales)

sublocale Abstract \<subseteq> correspondence abs_repr val_abs_typing upd_abs_typing abs_upd_val
  by (simp add:abs_defs;unfold_locales;simp)


sublocale Abstract \<subseteq> correspondence_init abs_repr val_abs_typing upd_abs_typing abs_upd_val
  by (unfold_locales)

sublocale Abstract \<subseteq> shallow val_abs_typing
  by (unfold_locales)

sublocale Abstract \<subseteq> U8rec_uabsfunsdeclfix_cogent_shallow _ abs_repr val_abs_typing upd_abs_typing abs_upd_val
  by (unfold_locales)

context Abstract begin
lemma abs_stuff :  
     "rename_mono_prog rename \<Xi> \<xi>\<^sub>m \<xi>\<^sub>p"
     "proc_env_matches \<xi>\<^sub>m \<Xi>"
     "proc_ctx_wellformed \<Xi>"
     "proc_env_u_v_matches   \<xi>_0 \<xi>\<^sub>m \<Xi>"
     "proc_env_matches_ptrs  \<xi>_0 \<Xi>"
      apply(subst rename_mono_prog_def, simp add:abs_defs)
     apply(subst proc_env_matches_def, simp add: abs_defs)
    apply(clarsimp simp add:proc_ctx_wellformed_def \<Xi>_simps)
   apply(subst proc_env_u_v_matches_def)
   apply(clarsimp simp add: \<Xi>_simps  abs_defs )
  apply(subst proc_env_matches_ptrs_def)
  apply(clarsimp simp add: \<Xi>_simps abs_defs )
  done

end




context Abstract begin


lemma assumes 
      "is_valid st p"
  and eqp': "(p', st') \<in> fst (main' p st)"
 shows
   "heap st' p' = heap st p"
proof -
  let ?vc = "heap st p"
  let ?a = "a_C ?vc"
  let ?vs = "\<lparr> a\<^sub>f = ?a \<rparr>"
  let ?pu = "UPtr (ptr_val p) (RRecord [RPrim (Num U8)])"
  let ?vu = "URecord [(UPrim (LU8 ?a), RPrim (Num U8))]" 
  let ?vv = "VRecord [VPrim (LU8 ?a)]" 
  let ?\<sigma> = "\<lambda> q. if q = ptr_val p then Some ?vu else None"
  let ?typ = "TRecord [(''a'', TPrim (Num U8), Present)] (Boxed Writable undefined)"

  have vv_typ: " vval_typing \<Xi> ?vv  ?typ"
    by (intro vval_typing_vval_typing_record.intros v_t_prim';simp)+

  have uv_rel : " upd_val_rel \<Xi> ?\<sigma> ?pu ?vv ?typ {} {ptr_val p}"
    apply(intro u_v_p_rec_w'[where w="{}" , simplified])
         apply simp_all
    apply(intro u_v_r_cons1[where r="{}" and r'="{}" and w="{}" and w'="{}", simplified])
      apply(intro u_v_prim';simp)
     apply(intro u_v_r_empty)
    apply simp
    done

  have uv_matches : "(u_v_matches \<Xi> ?\<sigma>
             [?pu] [?vv]
             [Some ?typ] {} {ptr_val p})" 
    apply(intro  u_v_matches_some[where r="{}" and r'="{}" and w="{ ptr_val p }" and w'="{}", simplified])
     apply(rule uv_rel)
    apply(intro u_v_matches.u_v_matches_empty)
    done
  have various_stuff:
     "matches \<Xi> [?vv] [Some ?typ]"
    " (?\<sigma>, st) \<in> state_rel"
   
     " val_rel_shallow_C  rename ?vs p  ?vv ?pu \<xi>\<^sub>p  ?\<sigma> \<Xi>"
    "matches_ptrs \<Xi> ?\<sigma> [?pu] [Some ?typ] {} { ptr_val p } "
        apply(subst matches_def,simp add:type_simps vv_typ)
       apply(simp add:state_rel_def heap_rel_def All_def heap_rel_ptr_def assms)

       apply(rule ext)
       apply (clarsimp simp add:TypeRelSimp ValRelSimp)
       apply blast

     apply(simp add:val_rel_shallow_C_def)
     apply(simp add:valRel_T0 ValRelSimp)
     apply(intro exI[where x = ?typ])
     apply(intro exI)
     apply(rule uv_rel)
    apply(rule u_v_matches_to_matches_ptrs )
    using uv_matches
    by blast



(* correspondence lemma from AllRefine *)
    have cor: "corres_shallow_C   rename state_rel 
 (U8rec_uabsfunsdeclfix_Shallow_Desugar.main ?vs) U8rec_uabsfunsdeclfix_TypeProof.main (main' p) \<xi>_0 \<xi>\<^sub>m \<xi>\<^sub>p
 [?pu] [?vv] \<Xi>
 [Some (fst (snd U8rec_uabsfunsdeclfix_TypeProof.main_type))]
 ?\<sigma> st"
      
      apply(rule corres_shallow_C_main[where 
   vv\<^sub>s = ?vs and uv\<^sub>C = p   and \<xi>\<^sub>m = \<xi>\<^sub>m and  \<xi>\<^sub>p =\<xi>\<^sub>p 
and uv\<^sub>m = ?pu and vv\<^sub>m = ?vv and ?vv\<^sub>p = ?vv and s = st and \<sigma> = ?\<sigma>]
    )
      apply(simp_all add:various_stuff abs_stuff type_simps)
            apply(unfold_locales; simp add:various_stuff abs_stuff)
      
      done

(* the meat: this block is where I need help. *)
  { 
    fix \<sigma>' pu' vv'
    assume u_eval:"
       \<xi>_0, [?pu] \<turnstile> (\<lambda>q. ?\<sigma> q,
                                 U8rec_uabsfunsdeclfix_TypeProof.main) \<Down>! (\<sigma>', pu')"
     and v_eval:  " \<xi>\<^sub>m  , [?vv] \<turnstile> U8rec_uabsfunsdeclfix_TypeProof.main \<Down> rename_val rename (monoval vv')"
     and st'_rel:  " (\<sigma>', st') \<in> state_rel"
    and v_cor:  " val_rel_shallow_C rename
        (U8rec_uabsfunsdeclfix_Shallow_Desugar.main ?vs) p' vv' pu' \<xi>\<^sub>p \<sigma>' \<Xi>"

(* unfolding v_cor *)
    obtain \<tau> r w repr where
     eq': "vv' = VRecord [VPrim (LU8 (a\<^sub>f (U8rec_uabsfunsdeclfix_Shallow_Desugar.main ?vs)))]"

      "pu' = UPtr (ptr_val p') repr"   
and  uv_rel':      "upd_val_rel \<Xi> \<sigma>' pu' (rename_val rename (monoval vv')) \<tau> r w"
      
      using v_cor      
      apply(simp add:val_rel_shallow_C_def valRel_T0 ValRelSimp)
      apply(elim exE conjE)
      by simp
 
  

(* the update value evaluation preserves typing *)
  obtain w' 
    where      "uval_typing \<Xi> \<sigma>' pu' ?typ {} w'"     
    and  \<sigma>'f:  "frame ?\<sigma> {ptr_val p} \<sigma>' w'"    
      using u_eval
      apply -
      apply(drule preservation_mono[rotated 3])
      apply(rule U8rec_uabsfunsdeclfix_AllRefine.main_typecorrect'[simplified type_simps]; simp)
      using preservation_mono abs_stuff  various_stuff 
      by force+
    

    (* can I show this without evaluating main in the value/update semantics? *)
    have  "heap st' p' = heap st p" 
 (* Help! *)
    by sorry
} 
  note meat = this



  show ?thesis
    using cor
    apply -
    apply(subst (asm) corres_shallow_C_def)        
    apply (elim impE)    
         apply(rule various_stuff abs_stuff )+
     apply(fastforce intro:uv_matches simp add:type_simps)
    apply(erule conjE)
    apply(thin_tac _)
    apply (elim allE)
    apply(erule impE)
     apply(rule eqp')
    apply(elim exE conjE)
    using meat
    apply blast
    done
qed
     




  
end

end
