(*

This file deals with custom getters and setters in case of custom layouts.
It also register uvals read from the table file in the theory.

The two main functions are
- generate_isa_getset_records_for_file: generates a direct and non monadic definition of custom
getters and setters by inspecting the C (monadic) definition

- local_setup_getset_lemmas which generates the get/set lemmas and prove them (similarly
to local_setup_take_put_member_case_esac_specialised_lemmas)

To show the get/set lemmas that ought to be proven, use the following snippset:
ML \<open> val lems = mk_getset_lems "variant_dargentisa.c" @{context} \<close>
ML \<open>lems  |> map (string_of_getset_lem @{context})|> map tracing\<close>

These get/set lemmas should be proven before the Take, Put, .. lemmas.


*)
theory Complements
  imports AutoCorres.AutoCorres
"CogentCRefinement.Tidy"
"CogentCRefinement.Specialised_Lemma_Utils"
"CogentCRefinement.Read_Table"
"CogentCRefinement.Value_Relation"
begin



(* Why is it necessary to prove this lemma *)
lemma unat_ucast_32_8 : "unat ( (UCAST(32 \<rightarrow> 8) x))
         <  2147483648"
  apply(unat_arith)
  apply (simp add: unat_ucast_up_simp)
  done

lemma unat_ucast_32_16 : "unat (UCAST(32 \<rightarrow> 16) x) < 2147483648"
  apply(unat_arith)
  apply (simp add: unat_ucast_up_simp)
  done

(* These lemmas help simplifying the monadic custom C getters and setters, that are inspected
to devise a corresponding direct (non monadic) definition.
 *)

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

(* Lemmas for variants (that involves conditions) *)
lemma condition_cst : " condition (\<lambda> _. b) u v = (if b then u else v)"
  by simp
  
lemma modify_if : "(if b then modify f else modify g) = 
  modify (\<lambda> x. if b then f x else g x)"
  by simp

lemma ptr_set_if :
   "(if b then x(ptr := t) else x(ptr := u)) = 
    x(ptr := if b then t else u)"
  by simp

ML \<open>
(* The callgraph is used to unfold any auxiliary function in the monadic definition of 
C getter/setter
*)
type callgraph = Symtab.key Binaryset.set Symtab.table;
(* TODO: use get_fun_info instead of c-parser callgraph *)
fun get_callgraph thy Cfile : callgraph =
 CalculateState.get_csenv thy Cfile
  |> Utils.the' ("get_callgraph: C file " ^ Cfile ^ " not loaded") 
|> ProgramAnalysis.compute_callgraphs |> #callgraph


(* returns the list of called functions in the body of
 fn_name *)
(* could also used FunctionInfo.callees in AutoCorres instead
of the callgraph *)
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

(* The purpose of this lemma is to unify a goal. More precisely, we provide P and Q and let isabelle
infer f *)
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
fun generate_getter_term ctxt getter_name heap_getter get_def_thm =
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
  @ @{thms gets_return gets_comp NonDetMonadEx.condition_gets }  )
|> thm_simp 
(* rewrite in the then and else statements *)
(Simplifier.add_cong @{thm if_cong} ctxt)
 @{thms comp_def }
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
(* This tackles conditions (if variants) *) 
|> thm_simp
 (* rewrite in the then and else statements *)
 (Simplifier.add_cong @{thm if_cong} ctxt)
 @{thms comp_def condition_cst modify_if ptr_set_if}
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
 (isa_fn_name, define_function isa_fn_name args term ctxt : Proof.context)
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
   (l : table_field_layout) 
   ctxt = 
 let
   val (isa_getter_name, ctxt) = generate_isa_get g heap_getter (# getter l) ctxt
   val (isa_setter_name, ctxt) = generate_isa_set g heap_setter (# setter l) ctxt
 in
   (((# getter l , isa_getter_name), (#setter l, isa_setter_name)), ctxt)
 end



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
    val (lays, ctxt) =   fold_map 
   (generate_isa_getset g heap_getter heap_setter)
     l ctxt
  in
    (lays, ctxt)
 end

(* generate isabelle setter/getters and simplified definition of C getter/setters
induced by a list of uvals (typically read from a table file).
*)
fun generate_isa_getset_records g heap_info uvals ctxt =
  let
    val (getsetl, ctxt) = 
     fold_map (generate_isa_getset_record g heap_info)
     (uvals |> get_uval_custom_layout_records 
   |> List.map (fn x => (get_ty_nm_C x, get_uval_custom_layout x)) |> rm_redundancy)
    ctxt
    val getsetMap = getsetl |> List.concat |>
       ListPair.unzip |> List.revAppend |>
      Symtab.make
      |> Symtab.map (fn _ => Syntax.read_term ctxt)
    val _ = tracing (@{make_string} getsetMap)
    fun make_uval (uval : table_field_layout uval) : field_layout uval =
       uval_map 
        (fn info => make_field_layout info 
      {
        isa_getter = (Symtab.lookup getsetMap (# getter info) |> Utils.the' "getter not found"),
        isa_setter = (Symtab.lookup getsetMap (# setter info) |> Utils.the' "setter not found")
     }
  )
       uval
    val uvals = List.map make_uval uvals
  in
    (uvals, ctxt)
  end



 \<close>

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
4. Put a uvals in a Theory Data so we don't need to read the table file again later.

The simplified definitions are thought to be used later when proving that
the C and isabelle custom getters/setters match.

 *)
ML \<open>
(* The additionnal parameter locale could certainly be removed *)
fun generate_isa_getset_records_for_file filename locale thy =
  let
    val uvals = read_table filename thy
    val g = get_callgraph thy filename : callgraph
    val heap_info = (Symtab.lookup (HeapInfo.get thy) 
     filename |> the  |> #heap_info)
    val ctxt = Named_Target.init locale thy
    val (uvals, ctxt) = generate_isa_getset_records g heap_info uvals ctxt
    val thy = Named_Target.exit ctxt
  in
    UVals.map (Symtab.update (filename, uvals)) thy
  end
 \<close> 

(*


Now, the mk_lems generation for getset


*)               
ML \<open>fn x => x : lem\<close>
ML \<open>
(* 1. `get o set = id`
2. `get_a o set_b = get_a`
3. `C_get = isabelle_get`
4. `C_set = isabelle_set`

more exactly, the first one is rather

1. `val_rel x new_val \<Longrightarrow> val_rel x (get (set t new_val))`

because get o set = id is too strict, as it does not hold for variants: if a field is a variant,
then the associated getter erases the irrelevant fields. Thus equality is too strong,
but we can replace them with value relation preservation
 *)
datatype getSetLemType = 
  GetSet | GetASetB | GetDef | SetDef

(* adapted from the lem type *)
type getset_lem = { prop : term, typ : getSetLemType, name : string, mk_tactic: Proof.context -> tactic} 
val cheat_tactic : Proof.context -> tactic = fn context => Skip_Proof.cheat_tac context 1

fun string_of_getset_lem ctxt (lem : getset_lem) =
  "lemma " ^ # name lem ^ "[GetSetSimp] : \"" ^
   Syntax.string_of_term ctxt (# prop lem) ^ "\""
  ^ "\n  sorry"

\<close>



ML \<open>
fun make_getset_prop_gen prms cncl ctxt : term =
  let
   val clean = HOLogic.mk_Trueprop o strip_atype
   val term = mk_meta_imps 
      (map clean prms) 
      (clean cncl) ctxt |> Syntax.check_term ctxt;
  in
     term
  end
\<close>



ML \<open>
fun mk_getset_prop (info : field_layout) ctxt : term =  
  let
   val prms = [ 
   @{term "val_rel x v"} 
]
   val cncl = @{term "\<lambda> getter setter. val_rel x (getter (setter b v))"}
         $ (# isa_getter info) $ (# isa_setter info)   
  in
     make_getset_prop_gen prms cncl ctxt
  end
\<close>

ML \<open>
fun mk_getdef_prop heap_getter is_valid_struct     
  (info : field_layout) ctxt : term =  
  let
   
   
   val field_getter    = #getter info ^ "'" |> Syntax.read_term ctxt;


   val cncl =
       @{term "\<lambda> isa_getter C_getter is_valid heap_getter. 
   C_getter ptr = do _ <- guard (\<lambda>s. is_valid s ptr);
                gets (\<lambda>s. isa_getter (heap_getter s ptr)) 
                od"}
         $ (# isa_getter info) $ field_getter $ is_valid_struct 
       $ heap_getter   
  in
     make_getset_prop_gen [] cncl ctxt
  end
\<close>

ML \<open>
fun mk_setdef_prop heap_setter is_valid_struct     
  (info : field_layout) ctxt : term =  
  let
   
   
   val field_setter    = #setter info ^ "'" |> Syntax.read_term ctxt;


   val cncl =
       @{term "\<lambda> isa_setter C_setter is_valid heap_setter. 
   C_setter ptr v = do _ <- guard (\<lambda>s. is_valid s ptr);
   modify (heap_setter (\<lambda>a. a(ptr := isa_setter (a ptr) v)))
                od"}
         $ (# isa_setter info) $ field_setter $ is_valid_struct 
       $ heap_setter   
  in
     make_getset_prop_gen [] cncl ctxt
  end
\<close>

ML \<open>
fun mk_getAsetB_prop (infoA : field_layout)(infoB : field_layout) ctxt : term =
  let
   val prms = [ ]
   val cncl = @{term "\<lambda> getter setter. getter (setter b v) = getter b"}
         $ (# isa_getter infoA) $ (# isa_setter infoB)
  in     
   make_getset_prop_gen prms cncl ctxt
  end
\<close>

(* analogous to mk_urecord_lems_for_uval *)
ML\<open> fun mk_getset_lems_for_rec file_nm ctxt name (infos : field_layout list) =
(* specialised-lemma generation for nth struct.*)
(* All uvals can reach this function. I have to filter them at some point.*)
 let
  
  val struct_C_nm = name;
  
  val _ = tracing ("mk_getset_lems_for_rec is generating lems for " ^ struct_C_nm)
  val heap            = Symtab.lookup (HeapInfo.get (Proof_Context.theory_of ctxt)) file_nm
                        |> Utils.the' "heap in mk_getset_lems_for_rec failed."
                        |> #heap_info;
  val struct_ty       = Syntax.read_typ ctxt struct_C_nm;
  val is_valid_struct = Typtab.lookup (#heap_valid_getters heap) struct_ty
             |> Utils.the' "is_valid_struct in take_member_default_mk_prog failed."
             |> Const;
   val heap_getter = Typtab.lookup (#heap_getters heap) struct_ty
             |> Utils.the' "heap_getter in take_member_default_mk_prog failed." |> Const
   val heap_setter = Typtab.lookup (#heap_setters heap) struct_ty
             |> Utils.the' "heap_getter in take_member_default_mk_prog failed." |> Const
       
  
  val (num_of_fields, field_names) = (List.length infos, List.map #name infos)
  val _ = tracing (@{make_string} (List.map #name infos))

  (* specialised_lemmas for each fields.
   * Three lemmas are generated if uval is of Writable.*)
  fun mk_lems_for_nth_field (field_num:int) =
   let
    val field_C_nm           = List.nth (field_names, field_num)
    val field_info           = List.nth (infos, field_num)
   in
    [{prop = mk_getdef_prop heap_getter is_valid_struct field_info ctxt,
      typ = GetDef, 
      name = # getter field_info ^ "_def_alt",
        mk_tactic = cheat_tactic},
{prop = mk_setdef_prop heap_setter is_valid_struct field_info ctxt,
      typ = SetDef, 
      name = # setter field_info ^ "_def_alt",
        mk_tactic = cheat_tactic}
 ]
   end;

  fun mk_lems_for_nth_fields (field_numA:int) (field_numB:int)
    : getset_lem list =
   let
    val field_C_nmA           = List.nth (field_names, field_numA)
    val field_infoA           = List.nth (infos, field_numA)
    val field_C_nmB           = List.nth (field_names, field_numB)
    val field_infoB           = List.nth (infos, field_numB)
    val lem_name = name ^ "_get_" ^ field_C_nmA ^
                          "_set_" ^ field_C_nmB
    val lem = 
      if field_numA = field_numB then
        {prop = mk_getset_prop field_infoA ctxt, typ = GetSet, 
        name = lem_name,
        mk_tactic = cheat_tactic}
      else
        {prop = mk_getAsetB_prop field_infoA field_infoB ctxt, 
        typ = GetASetB, 
        name = lem_name,
        mk_tactic = cheat_tactic}

   in
    [ lem  ]
   end;

  val lems1 = 
      List.tabulate (num_of_fields, fn field_numA =>
       List.tabulate (num_of_fields, fn field_numB  =>
       (let
        val _ = tracing ("  get o set for field numbers " ^ (Int.toString field_numA) ^
           " and " ^ (Int.toString field_numB))
       in
        mk_lems_for_nth_fields field_numA field_numB end))
       |> List.concat)

  val lems2 = 
        List.tabulate (num_of_fields, fn field_num => 
       (let
         val _ = tracing ("  get/set alternative def for field numbers " ^ (Int.toString field_num))
        in
         mk_lems_for_nth_field field_num end))

  val urecord_lems_for_nth_struct = 
    List.revAppend (lems1, lems2)
     |> List.concat 
     : getset_lem list;
 in
  urecord_lems_for_nth_struct : getset_lem list
 end;
\<close>

(* analogous to mk_lems *)
ML\<open> fun mk_getset_lems file_nm ctxt (* : {name : string, prop : term} *) =
 let
  val uvals = get_uvals file_nm (Proof_Context.theory_of ctxt) |> Utils.the' "mk_getset_lems"
  val names_infos =  (uvals |> get_uval_custom_layout_records 
    |> List.map (fn x => (get_ty_nm_C x, get_uval_custom_layout x)) |> rm_redundancy)
 (*  val uvals                 = read_table file_nm thy; *)
  val num_of_uvals          = List.length names_infos;
  fun get_nth_name_infos nth      = List.nth (names_infos, nth);
  val get_urecord_lems  = mk_getset_lems_for_rec file_nm ctxt;

  val (lemss:getset_lem list list) = List.tabulate (num_of_uvals, fn struct_num =>
     let
       val (name, infos) = get_nth_name_infos struct_num ;
     in  
     tracing ("mk_getset_lems started working for struct_number " ^ string_of_int struct_num ^
              " which corresponds to " ^ (*@{make_string}*) name);
    
     get_urecord_lems name infos  
    end) ;
 in
  List.concat lemss
  (* I don't know what does this part (copied from mk_lems) *)
(*
   |> map (fn v => (#name v, v))
   |> Symtab.make_list |> Symtab.dest
   |> map (fn (nm, xs) => let
       val fst_x = hd xs;
       val _ = map (fn x => (#prop x aconv #prop fst_x) orelse
             raise TERM ("lemmas: non duplicate for " ^ nm, [#prop x, #prop fst_x])) xs
       (* Why does Thomas want to have duplicate !? *)
      in hd xs end
    )*)
 end;
\<close>

ML \<open>


(* adapted from prove_put_in_bucket_non_esac_especialised_lemma *)
fun prove_put_in_bucket_getset_lemma (lem : getset_lem) lthy = 
   let
     val (lem_name, prop, mk_tac) = (#name lem, #prop lem, #mk_tactic lem);
     (* We want to have schematic variables rather than fixed free variables after registering this lemma.*)
     val names = Variable.add_free_names lthy prop [];
     val some_thm = (SOME (Goal.prove lthy names [] prop (fn {context, prems} => (mk_tac context))))
                 handle ERROR err => (warning lem_name; warning err; NONE);
   (* If proof goes well, register the proved lemma and putting it in the corresponding bucket.
    * If not, add the name of the thm in Unborn_Thms. *)
      val lthy = case some_thm of
               SOME thm =>
                  Local_Theory.note ((Binding.name lem_name, []), [thm]) lthy |> snd |>
                  GetSetSimp.add_local thm
             | NONE => Local_Theory.target (add_unborns lem_name) lthy;
  in
     lthy
  end


\<close>

ML \<open>
(* adapted from local_setup_take_put_member_case_esac_specialised_lemmas *)
fun local_setup_getset_lemmas file_nm lthy =
 let
  val lems:getset_lem list = mk_getset_lems file_nm  lthy;
  val lthy''  = fold prove_put_in_bucket_getset_lemma lems lthy;
 in
  lthy''
 end;

\<close>


end