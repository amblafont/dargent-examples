theory SeedRefinement
imports "lib/CogentMonad"
        "lib/CogentCorres"
        "build/Random_seed_AllRefine"
begin

section\<open> The shallow Cogent code refines a non-deterministic monad representing the set of all values \<close>

text \<open>This is trivial to prove as any program refines the set of all values but the set up should 
      allow for verifying a more interesting example involving for instance specifying the output of 
      a deterministic function that calls a non-deterministic one.\<close>


abbreviation "rand_with_seed_spec \<equiv> UNIV:: 64 word cogent_monad"
abbreviation "main_spec \<equiv> UNIV:: 64 word cogent_monad"

abbreviation "val_rel_monadic_shallow \<equiv> (\<lambda>(v:: 'b) sv:: ('a, 'b) SeedValue. v =  value\<^sub>f sv)"


(*NOTE that this is trivial*)
lemma all_functions_refine_UNIV :
  "\<And>s. cogent_corres val_rel_monadic_shallow UNIV (func s)"
by(simp add:cogent_corres_def)

(*NOTE that this is trivial -- any function would satisfy this spec *)
lemma rand_with_seed_corres_monad_shallow :
  "\<And>s. cogent_corres val_rel_monadic_shallow rand_with_seed_spec (rand_with_seed s)"
by(simp add:cogent_corres_def)

(*NOTE that this is trivial -- any function would satisfy this spec *)
lemma main_corres_monad_shallow :
  "\<And>s. cogent_corres val_rel_monadic_shallow main_spec (Random_seed_Shallow_Desugar.main s)"
  by(simp add:cogent_corres_def)



section\<open>Definitions for instantiating FFI correspondence locale\<close>
thm correspondence_def
section\<open>Refinement proofs of abstract functions from C to shallow Cogent\<close>


term "correspondence (\<lambda>a. ([],[])) (\<lambda>a b c d. False) (\<lambda>a b c d e f g h. False) (\<lambda>a b c d e f g h i. False)"
thm Random_seed_AllRefine.Random_seed_cogent_shallow.corres_shallow_C_main[no_vars]
thm random_seed.rand_with_seed'_def

thm Random_seed_cogent_shallow_def

lemma corres_shallow_C_main_no_assms:
  "Random_seed_cogent_shallow abs_repr val_abs_typing upd_abs_typing abs_upd_val
   \<Longrightarrow> (\<And>i \<gamma> v' \<Gamma>' \<sigma> st.
      i < length \<gamma> \<Longrightarrow>
      val_rel (\<gamma> ! i) v' \<Longrightarrow>
      \<Gamma>' ! i = Some (fst (snd (snd (snd Random_seed_TypeProof.rand_with_seed_type)))) \<Longrightarrow>
      update_sem_init.corres
        upd_abs_typing
        abs_repr
        Random_seed.state_rel
        (App (AFun ''rand_with_seed'' [] []) (Var i))
        ((random_seed.rand_with_seed' v') >>= (\<lambda>x. (gets (\<lambda>s. x))))
        \<xi>_0
        \<gamma>
        (assoc_lookup
          [ (''rand_with_seed'', Random_seed_TypeProof.rand_with_seed_type)
          , (''main'', Random_seed_TypeProof.main_type)]
          (0, [], {}, TUnit, TUnit))
        \<Gamma>'
        \<sigma>
        st)
  \<Longrightarrow> correspondence_init abs_repr val_abs_typing upd_abs_typing abs_upd_val
  \<Longrightarrow> value_sem.rename_mono_prog val_abs_typing rename \<Xi> \<xi>\<^sub>m \<xi>\<^sub>p
  \<Longrightarrow> vv\<^sub>m = value_sem.rename_val rename (value_sem.monoval vv\<^sub>p)
  \<Longrightarrow> correspondence_init.val_rel_shallow_C abs_repr abs_upd_val rename vv\<^sub>s uv\<^sub>C vv\<^sub>p uv\<^sub>m \<xi>\<^sub>p \<sigma> \<Xi>
  \<Longrightarrow> proc_ctx_wellformed \<Xi>
  \<Longrightarrow> value_sem.proc_env_matches val_abs_typing \<xi>\<^sub>m \<Xi>
  \<Longrightarrow> value_sem.matches val_abs_typing \<Xi> [vv\<^sub>m] [Some (fst (snd (snd (snd Random_seed_TypeProof.main_type))))]
  \<Longrightarrow> correspondence_init.corres_shallow_C
        abs_repr
        upd_abs_typing
        abs_upd_val
        rename
        Random_seed.state_rel
        (Random_seed_Shallow_Desugar.main vv\<^sub>s)
        Random_seed_TypeProof.main
        (random_seed.main' uv\<^sub>C)
        \<xi>_0
        \<xi>\<^sub>m
        \<xi>\<^sub>p
        [uv\<^sub>m]
        [vv\<^sub>m]
        \<Xi>
        [Some (fst (snd (snd (snd Random_seed_TypeProof.main_type))))]
        \<sigma>
        s"
  oops

theorem main_corres_monad_C:
  "True"
  oops
