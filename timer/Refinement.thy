theory Refinement
  imports Main "HOL-Word.Word" "Word_Lib.Word_Lib" "TimerSpec"
(* should be dargentfull*)
 "build_ignore_volatile_wo_u23/Ignore_volatile_wo_u23_dargentfull_Shallow_Desugar"
begin

fun curry_T0 :: "(('a, 'b, 'c) T0 \<Rightarrow> 'z) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'z)" where
  "curry_T0 f a b c = f (\<lparr> T0.p1\<^sub>f = a, p2\<^sub>f = b, p3\<^sub>f = c \<rparr>)"

fun curry_T3 :: "(('a, 'b) T1 \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c)" where
  "curry_T3 f a b = f (\<lparr> T1.p1\<^sub>f = a, p2\<^sub>f = b \<rparr>)"

(*
definition chooses :: "'a set \<Rightarrow> 'a"
  where "chooses X = (SOME x. (x \<in> X))"

lemma "chooses x = chooses x"
  by simp
lemma "undefined = undefined"
  
  by simp
term "(\<lambda>x. y)(a\<^sub>1 := True, a\<^sub>2 := True)"
lemma some1_equality: "\<exists>x. P x \<Longrightarrow> P a \<Longrightarrow> (SOME x. P x) = a"
  quickcheck nitpick
  sorry
thm some1_equality[o

typedecl  P
typedecl volatile_seed
consts get_a :: " P \<Rightarrow> nat \<Rightarrow> bool"
consts get_a :: " P \<Rightarrow> nat set"
consts get_a :: "(volatile_seed \<Rightarrow> P \<Rightarrow> nat \<times> volatile_seed)"
term "obtains"

definition test_something :: "P \<Rightarrow> nat"
  where "test_something x = 
    (if chooses (get_a) x = chooses (get_a) x then
0 else 1)"
lemma idontwant : "test_something p = 0"
  apply(simp add:test_something_def)
  done

lemma "(let y = chooses x in y) = chooses x"
  by simp
*)

type_synonym concr_device_state = "(bool, bool, 8 word, 8 word, 32 word, 32 word, 32 word) Meson_timer_reg"
type_synonym concr_state = "(concr_device_state, bool) Meson_timer"

axiomatization
  where cast82_def:"cast82 x = x"
   and  cast83_def:"cast83 x = x"
   and  set_timer_e_def :"set_timer_e (T1.make n reg) =
      reg \<lparr> timer_e_hi\<^sub>f := 0, timer_e\<^sub>f := 0 \<rparr>
     "

definition concr_driver :: "(concr_state, VAddr, 64 word, 16 word, bool) driver"
  where
  "concr_driver = 
\<lparr> 
  get_time = meson_get_time,
  init = curry_T3 meson_init,
  stop_timer = meson_stop_timer,
  set_timeout = curry_T0 meson_set_timeout,
\<comment> \<open>we are going to multiply it by 1000 (\<approx> 1024 = 2^10) \<close>
  stateInv = (\<lambda>s.  timer_e_hi\<^sub>f (regs\<^sub>f s) < 2^(32-10))
\<rparr>
"

locale concr_is_refinement = 
  is_refinement concr_driver mor
  for mor :: "(concr_state, VAddr, 64 word, 16 word, bool) driver_abstr"

  

definition \<alpha>timeout_timebase :: "nat \<Rightarrow> timeout_timebase"
  where 
  "\<alpha>timeout_timebase n = 
   (if n = 0 then TIMEOUT_TIMEBASE_1_US   else
    if n = 1 then TIMEOUT_TIMEBASE_10_US  else
    if n = 2 then TIMEOUT_TIMEBASE_100_US else
    if n = 3 then TIMEOUT_TIMEBASE_1_MS   else
    undefined)
   "
   
definition \<alpha>timestamp_timebase :: "nat \<Rightarrow> timestamp_timebase"
  where 
  "\<alpha>timestamp_timebase n = 
   (if n = 0 then TIMESTAMP_TIMEBASE_SYSTEM   else
    if n = 1 then TIMESTAMP_TIMEBASE_1_US  else
    if n = 2 then TIMESTAMP_TIMEBASE_10_US else
    if n = 3 then TIMESTAMP_TIMEBASE_100_US   else
    if n = 4 then TIMESTAMP_TIMEBASE_100_US   else
    TIMESTAMP_TIMEBASE_1_MS)
   "

definition \<alpha>_timer_mode :: "bool \<Rightarrow> timer_mode"
  where "\<alpha>_timer_mode b = (if b then Periodic else NotPeriodic)"

definition \<alpha>_reg :: "concr_device_state \<Rightarrow> device_state" where
"\<alpha>_reg ds = 
    \<lparr> timer_a_mode = \<alpha>_timer_mode (timer_a_mode\<^sub>f ds) ,
     timer_a_en = timer_a_en\<^sub>f ds,
timer_a = unat (timer_a\<^sub>f ds),
timer_a_input_clk = \<alpha>timeout_timebase (unat (timer_a_input_clk\<^sub>f ds)),
timer_e_input_clk = \<alpha>timestamp_timebase (unat (timer_e_input_clk\<^sub>f ds)),
timer_e_low_hi = unat (word_cat (timer_e_hi\<^sub>f ds) (timer_e\<^sub>f ds) :: 64 word)

 \<rparr> "

definition \<alpha>_state :: "concr_state \<Rightarrow> abstr_state" where
"\<alpha>_state s = 
  \<lparr> 
    driverState = \<lparr> disable = disable\<^sub>f s \<rparr>,
    deviceState = \<alpha>_reg (regs\<^sub>f s)
  \<rparr>"

definition abstraction :: "(concr_state, VAddr, 64 word, 16 word, bool) driver_abstr"
  where "abstraction = 
  \<lparr>
   mor_state = \<alpha>_state,
   mor_reg = \<alpha>_reg o config_get_regs,
   mor_time = unat, 
   mor_timeout = unat,
   mor_timer_mode = \<alpha>_timer_mode 
  \<rparr>"

lemmas driver_defs = concr_driver_def abs_driver_def abstraction_def
lemmas simp_defs = driver_defs \<alpha>_state_def \<alpha>_reg_def \<alpha>timeout_timebase_def
 \<alpha>timestamp_timebase_def


thm unat_def uint_up_ucast is_up

lemma unat_ucast_up : 
 " LENGTH('a :: len0) \<le> LENGTH('b ::len0) \<Longrightarrow> 
unat (UCAST('a \<rightarrow> 'b) w) = unat w"
  by (simp add: unat_def uint_up_ucast is_up)


lemma helper1 : "
((UCAST(32 \<rightarrow> 64) x << 32) || UCAST(32 \<rightarrow> 64) y)
= word_cat x y"
  by word_bitwise

lemma helper2 : "
(h :: int) < 4194304 \<Longrightarrow> l < 2^32 \<Longrightarrow> 536870912000 * h + 125 * l < 2305843009213693952
"  
  
  apply(rule less_le_trans)
   apply(rule add_strict_mono)
    apply(erule mult_strict_left_mono)
    apply simp
   apply(erule mult_strict_left_mono)
   apply simp
  apply simp
  done


interpretation concr_implementation:
  concr_is_refinement abstraction
  apply unfold_locales
     apply (simp add:simp_defs meson_get_time_def ns_in_us_def)

     apply(case_tac s, rename_tac regs disable, case_tac regs)
     apply clarsimp
     apply(simp add:helper1)
     apply(simp add:unat_def)
     apply (subst uint_mult_lem[THEN HOL.iffD1])
      apply simp
      apply(simp add:word_cat_def )
      apply(subst word_ubin.eq_norm)
 
      apply simp
      apply(simp add:bintr_cat)
      apply(subst word_ubin.norm_norm(2)[THEN fun_cong, simplified comp_def, of "_ :: 32 word", simplified])
      apply(simp add:bin_cat_num)
      apply(subst word_ubin.norm_norm(2)[THEN fun_cong, simplified comp_def, of "_ :: 32 word", simplified])
      apply(simp add:word_less_alt)
      apply(erule helper2)


      apply(uint_arith, simp)
     apply simp


    apply (simp add:simp_defs meson_init_def meson_get_time_def ns_in_us_def
  set_timer_e_def)
     apply(case_tac s, rename_tac regs disable, case_tac regs)
    apply(simp add: take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t_def cast82_def cast83_def)
     (* hmm *)
    apply clarsimp
  apply(simp add:word_cat_def)

(* yeah! *)
     apply (simp add:simp_defs meson_stop_timer_def  ns_in_us_def take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t_def)

  
    
    apply(simp add:simp_defs  meson_set_timeout_def  take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t_def Let\<^sub>d\<^sub>s_def)
     apply(simp add:unat_ucast_up)

(* invariants *)
    apply(simp add:simp_defs meson_init_def take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t_def Let\<^sub>d\<^sub>s_def set_timer_e_def)
   apply(simp add:simp_defs  meson_stop_timer_def  ns_in_us_def take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t_def)
  apply(simp add:simp_defs  meson_set_timeout_def  take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t_def Let\<^sub>d\<^sub>s_def)
  
  by(simp add: HOL.Let_def )
  

end