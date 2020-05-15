
theory Complements
  imports AutoCorres.AutoCorres
"/home/laf027/cogent/branches/dargentisa/c-refinement/Tidy"
"/home/laf027/cogent/branches/dargentisa/c-refinement/Specialised_Lemma_Utils"
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
get_def_thm is the unfolded defintion of the C_function
*)
fun generate_getter_term ctxt getter_name  heap_getter get_def_thm =
get_def_thm
|> 
Rule_Insts.of_rule ctxt ([SOME "ptr"], []) [] |>
my_simp ctxt
([
(* We add this rewrite rule to remove the guards *)
  (Proof_Context.read_term_pattern ctxt 
   "\<And> (e :: lifted_globals \<Rightarrow> _). guard e = gets (\<lambda>_  . ())"
  |> Thm.cterm_of ctxt  |> Thm.assume)
  ] 
  @ @{thms gets_return gets_comp }  )
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
fun generate_setter_term ctxt setter_name heap_setter setter_thm  =
setter_thm
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
 )
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

ML \<open>fun normal_def fn_C_name ctxt =
  Proof_Context.get_thm ctxt (fn_C_name ^ "'_def")

type callgraph = Symtab.key Binaryset.set Symtab.table;

fun unfold_thm (g : callgraph) fn_name get_thm_def ctxt =
   let  
     val called_funs = rec_called_funs g fn_name 
    (* generate nice definitions of C getters *)
    val called_funs_def =  List.map (fn s => get_thm_def s ctxt) called_funs
in
   get_thm_def fn_name ctxt |> my_simp ctxt called_funs_def
end

\<close>


ML \<open>

fun generate_isa_get_or_set g fn_name args get_thm_def generator ctxt =
let   
    val isa_fn_name = "deref_" ^ fn_name
    val simplified_thm_name = fn_name ^ "'_def'"
    val _ = tracing ("generate_isa_get_or_set: generating " ^ isa_fn_name ^ " and " ^ simplified_thm_name)
    val fn_def_thm = unfold_thm g fn_name get_thm_def ctxt
    val term = generator fn_def_thm
    val ctxt = Utils.define_lemma simplified_thm_name fn_def_thm ctxt |> snd
in
 my_generate_fun isa_fn_name args term ctxt : Proof.context
end

(* adds the definition of getter in the context and
some unfoldings in the named_theorems getst_nm_thm *)
fun generate_isa_get g heap_fn fn_name ctxt =
generate_isa_get_or_set g fn_name ["w"] tidy_C_fun_def
  (generate_getter_term ctxt fn_name heap_fn) ctxt

fun generate_isa_set g heap_fn fn_name ctxt =
generate_isa_get_or_set g fn_name ["w", "v"] normal_def
  (generate_setter_term ctxt fn_name heap_fn) ctxt

fun generate_isa_getset g heap_getter heap_setter  (* ty *)
   ({ty = _ , getter = getter_name , setter = setter_name} : layout_field_info) 
   ctxt = 
  ctxt |>
   generate_isa_get g heap_getter getter_name
|> generate_isa_set g heap_setter setter_name ;

fun generate_isa_getset_record g (heap_info : HeapLiftBase.heap_info) (ty, l) ctxt =
  let
    val _ = tracing ("generate_isa_getset_record: generating getter/setter for " ^ ty)
    val heap_getter = ( Typtab.lookup (#heap_getters heap_info) 
        (Syntax.read_typ ctxt ty)) |> the |> fst
    val heap_setter = ( Typtab.lookup (#heap_setters heap_info) 
        (Syntax.read_typ ctxt ty)) |> the |> fst
  in
  fold (generate_isa_getset g heap_getter heap_setter  ) l ctxt
 end

fun generate_isa_getset_records g heap_info uvals ctxt =
   fold (generate_isa_getset_record g heap_info)
   (uvals |> get_uval_custom_layout_records 
 |> List.map (fn x => (get_ty_nm_C x, get_uval_custom_layout x)) |> rm_redundancy)
  ctxt
 \<close>   


end