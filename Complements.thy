
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

type callgraph = Symtab.key Binaryset.set Symtab.table;

fun get_callgraph thy Cfile : callgraph =
 CalculateState.get_csenv thy Cfile
  |> the |> ProgramAnalysis.compute_callgraphs |> #callgraph


(* returns the list of called functions in the body of
 fn_name *)
fun called_funs (g : callgraph) (fn_name : string) =
    case Symtab.lookup g fn_name of
   SOME t => Binaryset.listItems t
   | NONE => []

(* returns the list of called functions in the body of
 fn_name and recursively, the list of called functions
in the body of the called functions *)
fun rec_called_funs g (fn_name : string) =
  let
    val l =  called_funs g fn_name
  in
  l @ (List.map (rec_called_funs g) l
  |> List.concat)
end

\<close>





ML \<open>

(* thm[of t1 t2] ~ thm_of ctxt [t1, t2] thm *)
fun thm_of ctxt vars = 
  Rule_Insts.of_rule ctxt (List.map SOME vars, []) []

(* thm[simplified thms] ~ thm_simp ctxt thms thm 
(not exactly equivalent as the first version clears the
simplication set)
*)
fun thm_simp ctxt thms = 
Simplifier.asm_simplify (ctxt addsimps thms)

(* thm1[THEN thm2] ~ thm_THEN ctxt thm2 thm1 *)
fun thm_THEN thm2 thm1 =
thm1 RSN (1 , thm2) ;

(* thm1[OF thms] ~ thm_OF thm1 thms *)
fun thm_OF thm1 thms =
thm1 OF thms ;
\<close>

lemma unify_goal_auxiliary : "\<And> P Q f. P f \<Longrightarrow> Q f \<Longrightarrow> Q f"
  by simp

ML \<open>
(* 
replace a goal A \<Rightarrow> P f with
A \<Rightarrow> Q f \<Rightarrow> Q f, for sP the string defining P
(typically a lambda), and sQ the string defining Q
*)
fun unify_change_goal ctxt sP sQ (* simps *) thm =
  thm |> thm_THEN
(
@{thm unify_goal_auxiliary}
|> thm_of ctxt [sP, "_", sQ]
|> Simplifier.asm_full_simplify ctxt)

(* 
replace a goal A \<Rightarrow> P f with
A \<Rightarrow> undefined = Q f \<Rightarrow> undefined = Q f,
 for sP the string defining P
(typically a lambda), and sQ the string defining Q
*)
fun unify_change_goal_eq ctxt sP sQ  =
  unify_change_goal ctxt sP 
    ("\<lambda> f.  undefined = " ^ sQ ^ " f") 
\<close>




ML \<open>
(* generate the isabelle getter term, depending on an argument named w,
 by inspecting the C getter definition as given by get_def_thm (which should
be totally unfolded)
heap_getter: the name of the heap getter, e.g. heap_t1_C
*)
fun generate_getter_term ctxt getter_name  heap_getter get_def_thm =
get_def_thm
|> 
Rule_Insts.of_rule ctxt ([SOME "ptr"], []) [] |>
thm_simp ctxt
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
|> unify_change_goal_eq ctxt 
("(\<lambda> f. " ^ getter_name ^ "' ptr = gets (\<lambda>s . f  (" ^ heap_getter ^ " s ptr)))")
"(\<lambda> f. f w)" 
|> Thm.concl_of 
|> Utils.rhs_of_eq
\<close>

ML \<open>
(* generate the isabelle setter term, depending on arguments named w and v (the new value),
 by inspecting the C setter definition as given by set_def_thm (which should
be totally unfolded)

A simplification rule of the shape
 " heap_t1_C_update f o heap_t1_C_update f' = heap_t1_C_update (f o f')"
should be first added to the context.

heap_setter: the name of the heap setter, e.g. heap_t1_C_update
*)
fun generate_setter_term ctxt setter_name heap_setter setter_thm  =
setter_thm
|> 
Rule_Insts.of_rule ctxt ([SOME "ptr", SOME "v"], []) [] |>
thm_simp ctxt
([
(* We add this rewrite rule to remove the guards *)
  (Proof_Context.read_term_pattern ctxt 
   "\<And> (e :: lifted_globals \<Rightarrow> _). guard e = gets (\<lambda>_  . ())"
  |> Thm.cterm_of ctxt  |> Thm.assume)
  ] 
  @ @{thms modify_comp ptr_set_comp
 } 
 )
|> thm_THEN @{thm  HOL.meta_eq_to_obj_eq}
|> unify_change_goal_eq ctxt 
("(\<lambda> f. " ^ setter_name ^ 
"' ptr v = modify (" ^ heap_setter ^ " (\<lambda>x . x(ptr := f  (x ptr)))))")
"(\<lambda> f. f w)" 

|> Thm.concl_of 
|> Utils.rhs_of_eq
\<close>


ML \<open>
(* define an Isabelle function with a provided term depending on a
list of named variables. *)
fun define_function name vars term ctxt = 
 case Utils.define_const_args name false term
(List.map (fn x => (x , Term.dummyT)) vars) ctxt of
   (_,_,ctxt) => ctxt 
 \<close>

ML \<open>
(* given the name of a C function, returns the definition theorem*)
fun fn_C_def_thm fn_C_name ctxt =
  Proof_Context.get_thm ctxt (fn_C_name ^ "'_def")


(* returns a definition theorem for a C function named fn_named, where
all the recursively called functions in the body have been unfolded using
theorems provided by get_thm_def
 *)
fun unfold_thm (g : callgraph) (fn_name : string) 
   (get_thm_def : string -> Proof.context -> thm)  ctxt =
   let  
     val called_funs = rec_called_funs g fn_name 
    (* generate nice definitions of C getters *)
    val called_funs_def =  List.map (fn s => get_thm_def s ctxt) called_funs
in
   get_thm_def fn_name ctxt |> thm_simp ctxt called_funs_def
end

\<close>


ML \<open>

(* 
add to the context the definition of an isabelle getter/setter (depending
on the provided arguments get_thm_def, generator, and args) corresponding the
C getter/setter named fn_name.
also, adds a simplified definition theorem of the C getter/setter.
*)
fun generate_isa_get_or_set g fn_name args get_thm_def generator ctxt =
let   
    val isa_fn_name = "deref_" ^ fn_name
    val simplified_thm_name = fn_name ^ "'_def'"
    val _ = tracing ("generate_isa_get_or_set: generating " ^ isa_fn_name ^ " and " ^ simplified_thm_name)
    val fn_def_thm = unfold_thm g fn_name get_thm_def ctxt
    val term = generator fn_def_thm
    val ctxt = Utils.define_lemma simplified_thm_name fn_def_thm ctxt |> snd
in
 define_function isa_fn_name args term ctxt : Proof.context
end

(* heap_fn : the name of the heap getter, e.g. heap_t1_C *)
fun generate_isa_get g heap_fn fn_name ctxt =
generate_isa_get_or_set g fn_name ["w"] tidy_C_fun_def
  (generate_getter_term ctxt fn_name heap_fn) ctxt

(* heap_fn : the name of the heap setter, e.g. heap_t1_C_update *)
fun generate_isa_set g heap_fn fn_name ctxt =
generate_isa_get_or_set g fn_name ["w", "v"] fn_C_def_thm
  (generate_setter_term ctxt fn_name heap_fn) ctxt

fun generate_isa_getset g heap_getter heap_setter  (* ty *)
   ({ty = _ , getter = getter_name , setter = setter_name} : layout_field_info) 
   ctxt = 
  ctxt |>
   generate_isa_get g heap_getter getter_name
|> generate_isa_set g heap_setter setter_name ;

(* generate the isabelle setter/getters and simplified definitions of the C getter/setter
for a given record type ty with specified C getter/setters in l
*)
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

(* generate isabelle setter/getters and simplified definition of C getter/setters
induced by a list of uvals (typically read from a table file).
*)
fun generate_isa_getset_records g heap_info uvals ctxt =
   fold (generate_isa_getset_record g heap_info)
   (uvals |> get_uval_custom_layout_records 
 |> List.map (fn x => (get_ty_nm_C x, get_uval_custom_layout x)) |> rm_redundancy)
  ctxt
 \<close>   


end