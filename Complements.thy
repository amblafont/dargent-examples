
theory Complements
  imports AutoCorres.AutoCorres
begin

lemma gets_comp : "do x <- gets f ;
                     gets (f' x) od
                     =
                  gets (\<lambda> s . f' (f s) s)"
  by monad_eq


lemma gets_return : "do x <- gets f ;
                     return (g x) od = gets (g o f)"
  by monad_eq


ML \<open>
fun called_funs g fn_name =
    case Symtab.lookup g fn_name of
   SOME t => Binaryset.listItems t
   | NONE => []

fun rec_called_funs g fn_name =
  let
    val l =  called_funs g fn_name
  in
  l @ (List.map (rec_called_funs g) l
  |> List.concat)
end

fun get_callgraph thy Cfile =
 CalculateState.get_csenv thy Cfile
  |> the |> ProgramAnalysis.compute_callgraphs |> #callgraph


(*
fun called_funs_theory thy Cfile fn_name =
get_callgraph thy Cfile |> (fn g => rec_called_funs g fn_name)
*)
\<close>



ML \<open>val suffix_def_easy = "'_def'"\<close>
ML \<open>fun easy_def ctxt (name : string) : thm = 
Proof_Context.get_thm ctxt (name ^ suffix_def_easy)
\<close>

ML \<open>fun normal_def ctxt (name : string) : thm = 
Proof_Context.get_thm ctxt (name ^ "'_def")
\<close>

ML \<open>
fun my_of ctxt vars = 
  Rule_Insts.of_rule ctxt (List.map SOME vars, []) []

fun my_simp ctxt thms = 
Simplifier.asm_simplify ((* clear_simpset *) ctxt addsimps thms)

fun my_THEN thm2 thm1 =
thm1 RSN (1 , thm2) ;

fun my_OF thm1 thms =
thm1 OF thms ;
\<close>

lemma complicated : "\<And> P Q f. P f \<Longrightarrow> Q f \<Longrightarrow> Q f"
  by simp

ML \<open>
(* 
replace a goal A \<Rightarrow> B \<Rightarrow> P f with
A \<Rightarrow> B \<Rightarrow> Q f \<Rightarrow> Q f, for sP the string defining P
(typically a lambda, and sQ the string defining Q)
*)
fun unify_goal_and_prove ctxt sP sQ (* simps *) thm =
  thm |> my_THEN
(
Proof_Context.get_thm ctxt "complicated"
|> my_of ctxt [sP, "_", sQ]
|> Simplifier.asm_full_simplify
(ctxt (*addsimps simps *))
) 

(* 
replace a goal A \<Rightarrow> B \<Rightarrow> P f with
A \<Rightarrow> B \<Rightarrow> undefined = Q f \<Rightarrow> undefined = Q f,
 for sP the string defining P
(typically a lambda, and sQ the string defining Q)
*)
fun unify_goal_and_prove_eq ctxt sP sQ  =
  unify_goal_and_prove ctxt sP 
    ("\<lambda> f.  undefined = " ^ sQ ^ " f") 
\<close>


ML \<open>
(* generate the isabelle getter term depending on w by inspecting the
 C getter definition.
lget_aa is the list of constants to be unfolded in the
getter_name definition
*)
fun generate_getter_term ctxt getter_name lget_aa heap_getter =
easy_def ctxt getter_name
|> 
Rule_Insts.of_rule ctxt ([SOME "ptr"], []) [] |>
my_simp ctxt
([
(* We add this rewrite rule to remove the guards *)
  (Proof_Context.read_term_pattern ctxt 
   "\<And> (e :: lifted_globals \<Rightarrow> _). guard e = gets (\<lambda>_  . ())"
  |> Thm.cterm_of ctxt  |> Thm.assume)
  ] 
  @ @{thms gets_return gets_comp } 
 @ (List.map (easy_def ctxt) lget_aa))
(* Here we should have a conclusion of the shape
getter ptr = gets (\<lambda>s . f s)


*)
|> unify_goal_and_prove_eq ctxt 
("(\<lambda> f. " ^ getter_name ^ "' ptr = gets (\<lambda>s . f  (" ^ heap_getter ^ " s ptr)))")
"(\<lambda> f. f w)" 

|> Thm.concl_of 
|> Utils.rhs_of_eq
\<close>





lemma modify_comp: "do _ <- modify f ; modify f' od = modify (f' o f )"
  by (monad_eq)

lemma ptr_set_comp :
   "(\<lambda>x. x(ptr := f (x ptr))) o (\<lambda>x. x(ptr := f' (x ptr))) = (\<lambda>x. x(ptr := f (f' (x ptr))))"
(*  proof obtained by sledgehammer *)
proof -
have "\<forall>fa. ((\<lambda>fa. fa(ptr := f (fa ptr))) \<circ> (\<lambda>f. f(ptr := f' (f ptr)))) fa = fa(ptr := f (f' (fa ptr)))"
  by (simp add: fun_upd_same)
  then show ?thesis
    by blast
qed

ML \<open>
(* generate the isabelle getter term depending on w and (v the new value) by inspecting the
 C getter definition.
lget_aa is the list of constants to be unfolded in the
getter_name definition
*)
(*fun generate_setter_term ctxt setter_name lset_aa  =*)
fun generate_setter_term ctxt setter_name lset_aa heap_setter =
normal_def ctxt setter_name
|> 
Rule_Insts.of_rule ctxt ([SOME "ptr", SOME "v"], []) [] |>
my_simp ctxt
([
(* We add this rewrite rule to remove the guards *)
  (Proof_Context.read_term_pattern ctxt 
   "\<And> (e :: lifted_globals \<Rightarrow> _). guard e = gets (\<lambda>_  . ())"
  |> Thm.cterm_of ctxt  |> Thm.assume)
  ] 
  @ @{thms modify_comp (* heap_t1_C_update_comp *) ptr_set_comp
(* t1_C_updupd_same *)
 } 
 @ (List.map (normal_def ctxt) lset_aa))
(* Here we should have a conclusion of the shape
getter ptr = gets (\<lambda>s . f s)


*)
|> my_THEN @{thm  HOL.meta_eq_to_obj_eq}
|> unify_goal_and_prove_eq ctxt 
("(\<lambda> f. " ^ setter_name ^ 
"' ptr v = modify (" ^ heap_setter ^ " (\<lambda>x . x(ptr := f  (x ptr)))))")
"(\<lambda> f. f w)" 

|> Thm.concl_of 
|> Utils.rhs_of_eq
\<close>


ML \<open>
fun my_generate_fun name vars term ctxt = 
 case Utils.define_const_args name false term
(List.map (fn x => (x , Term.dummyT)) vars) ctxt of
   (_,_,ctxt) => ctxt 
 \<close>


end