theory SpreadGetSet
  imports Main
 "build_spread/Spread_dargentfull_CorresProof"

begin
context spread_dargentfull begin
definition find_position :: "nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat"
  where "find_position si offset  = (offset div si, offset mod si)"

definition get_bit :: "(('a::len0) word)['n::finite] \<Rightarrow> nat \<Rightarrow> bool"
  where "get_bit arr pos = 
                (let (byte, off) = find_position LENGTH('a) pos in
                 arr.[byte] !! off )"

definition raw_get_bit :: "(('a::len0) word)['n::finite] \<Rightarrow> nat \<Rightarrow> 'a word"
  where "raw_get_bit arr pos = 
                (let (byte, off) = find_position LENGTH('a) pos in
                 arr.[byte] && 2^off )"



definition size_of_arr :: "(('a::len0) word)['n::finite] \<Rightarrow> nat"
  where "size_of_arr _ = CARD('n)"

definition size_of_arr_bits :: "(('a::len0) word)['n::finite] \<Rightarrow> nat"
  where "size_of_arr_bits _ = LENGTH('a)*CARD('n)"

ML \<open>
fun getter_sanity_tac ctxt = 
 let
    val gets = Proof_Context.get_thms ctxt
    val get  = Proof_Context.get_thm ctxt
  in
  K (print_tac ctxt "debut_getter")
THEN' 
 (asm_full_simp_tac (ctxt addsimps [(get "find_position_def")])
THEN'
 (fn i => 
TRY (REPEAT_ALL_NEW (eresolve_tac ctxt @{thms exE conjE}) i))
(* THEN' K (print_tac ctxt "coucou") *)
THEN' custom_get_set_different_field_tac ctxt
) end
\<close>

lemma wesh : "x < LENGTH('a) \<Longrightarrow> (((2 ^ x) :: ('a :: len0)  word) !! n) = (x = n)"
  by sorry
ML \<open>
fun setter_sanity_tac ctxt = 
 let
    val gets = Proof_Context.get_thms ctxt
    val get  = Proof_Context.get_thm ctxt
  in
  K (print_tac ctxt "debut")
THEN' 
 (asm_full_simp_tac (ctxt addsimps
 [get "find_position_def", get "size_of_arr_bits_def"]))
THEN'
(asm_full_simp_tac ((clear_simpset ctxt) addsimps
 (gets "numeral.simps")))
THEN' asm_full_simp_tac ctxt
(* THEN'  K (print_tac ctxt "suite") *)
THEN'
 (fn i => 
TRY (REPEAT_ALL_NEW (eresolve_tac ctxt @{thms exE conjE}) i))
(* THEN'  K (print_tac ctxt "resuite") *)
 THEN'  (fn i => 
TRY (REPEAT_ALL_NEW (eresolve_tac ctxt @{thms less_zeroE less_SucE}) i)) 

 (* THEN' K (print_tac ctxt "coucou")  *)
THEN_ALL_NEW custom_get_set_different_field_tac (ctxt addsimps @{thms wesh})
 end
\<close>
ML \<open>
fun prove_thm ctxt assms concl tactic = 
let
val clean = HOLogic.mk_Trueprop o strip_atype
val thm0 = mk_meta_imps (map clean assms) (concl |> clean) ctxt
val names =  Variable.add_free_names ctxt thm0 []
in
Goal.prove ctxt names [] thm0
( fn {context, prems} => tactic context 1)
end
\<close>

ML \<open>
val uvals = 
Symtab.lookup (UVals.get @{theory}) "spread_dargentfull.c"
|> the
(* Filter those with custom layouts*)
 |> get_uval_custom_layout_records
\<close>
ML \<open>
 val uval0 = hd uvals
\<close>

ML \<open>
val (info0, lay0) = 
case get_uval_layout uval0 of
CustomLayout (info, 
Const ("Option.option.Some", _) $ 
( Const ("Cogent.ptr_layout.LayRecord", _) $ 
layout)) => 
(info, 
layout |> HOLogic.dest_list
|> map HOLogic.dest_prod
|> map (apfst HOLogic.dest_string)
|> Symtab.make
)

val field0 = hd info0
val layfield0 = Symtab.lookup lay0 (# name field0) |> the
\<close>

ML \<open>
val get_data =
get_uval_name uval0 ^ "_C.data_C"
\<close>

ML \<open>
fun make_getter_sanity_thm ctxt layfield (field_info : field_layout) = 
let
val ass = 
  @{term 
  "\<lambda>  lay data. 
   (\<forall> x\<in> set(layout_taken_bit_list lay). 
  get_bit (data s) x = get_bit (data t) x)
  "
  } $ layfield $ (Syntax.read_term ctxt get_data)
val concl = @{term "\<lambda> getter . getter s = getter t"  }
        $ # isa_getter field_info
in
prove_thm ctxt [ass] concl getter_sanity_tac
end

\<close>
ML \<open>
fun make_setter_sanity_thm ctxt layfield (field_info : field_layout) = 
let

 val data = Syntax.read_term ctxt get_data
val ass1 = 
  @{term 
  "\<lambda>  data .x < size_of_arr_bits (data s) 
  "
  } $ data
val ass2 = 
  @{term 
  "\<lambda>  lay .x \<notin> set (layout_taken_bit_list lay) 
  "
  } $ layfield
val concl = @{term "\<lambda> data setter . 
   raw_get_bit (data (setter s b)) x = raw_get_bit (data s) x"  }
        $ data
        $ # isa_setter field_info
in
prove_thm ctxt [ass1, ass2] concl (fn ctxt => fn _ => print_tac ctxt "coucuo" THEN cheat_tactic ctxt)(* setter_sanity_tac *)
end
\<close>

ML \<open>
fun make_getset_sanity_thms ctxt (uval : field_layout uval) : (thm * thm) list =
let
val (info, lays) = 
case get_uval_layout uval of
CustomLayout (info, 
Const ("Option.option.Some", _) $ 
( Const ("Cogent.ptr_layout.LayRecord", _) $ 
layout)) => 
(info, 
layout |> HOLogic.dest_list
|> map HOLogic.dest_prod
|> map (apfst HOLogic.dest_string)
|> Symtab.make
)
in
map (
fn field => 
let val lay = Symtab.lookup lays (# name field) |> the in
(make_getter_sanity_thm ctxt  lay field,
make_setter_sanity_thm ctxt lay field)
end
)
 
 info

end
\<close>

lemma raw_get_bit_eq : "raw_get_bit x n = raw_get_bit y n \<Longrightarrow> get_bit x n = get_bit y n"
  by sorry

lemma find_pos_split : " P (find_position q x)
  = ((\<forall> p r. find_position q x = (p, r) \<longrightarrow>
r < q \<longrightarrow> p < n div q \<longrightarrow>  P (p, r))
\<and> (\<forall> r. find_position q x = (n div q, r) \<longrightarrow> r < n mod q \<longrightarrow> P ( (n div q), r) )
\<and> (\<forall> p r. find_position q x = (p, r) \<longrightarrow> (x \<ge> n \<or> q = 0) \<longrightarrow> P ( p, r) )
)
"
  by sorry

lemma "x < size_of_arr_bits (data_C s) \<Longrightarrow>
    x \<notin> set (layout_taken_bit_list (LayBitRange (64, 2))) \<Longrightarrow>
    get_bit (data_C (deref_d21_set_b s b)) x = get_bit (data_C s) x "
  apply(rule raw_get_bit_eq )
apply(simp add:raw_get_bit_def)
apply( split find_pos_split[of _ _ _  32])

end

lemma "x < size_of_arr_bits (data_C s) \<Longrightarrow>
    x \<notin> set (layout_taken_bit_list
               (LayVariant (Suc 0, Suc 0) [(''A'', 0, LayBitRange (Suc 0, 0)), (''B'', Suc 0, LayBitRange (Suc 0, 67))])) \<Longrightarrow>
    raw_get_bit (data_C (deref_d14_set_a s b)) x = raw_get_bit (data_C s) x "
  apply(tactic \<open>setter_sanity_tac @{context} 1\<close> )
(* ca ne marche pas ! *)

lemma "x < size_of_arr_bits (data_C s) \<Longrightarrow>
    x \<notin> set (layout_taken_bit_list (LayBitRange (64, 2))) \<Longrightarrow>
    raw_get_bit (data_C (deref_d21_set_b s b)) x = raw_get_bit (data_C s) x "
apply(tactic \<open>setter_sanity_tac @{context} 1\<close> )

ML \<open>
val thms = make_getset_sanity_thms @{context} uval0
\<close>

end


end
