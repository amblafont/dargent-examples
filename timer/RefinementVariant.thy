theory RefinementVariant
  imports Main "HOL-Word.Word" "Word_Lib.Word_Lib" "TimerSpec"
 "build_ignore_volatile_variant/Ignore_volatile_variant_dargentfull_Shallow_Desugar"
begin

fun curry_T1 :: "(('a, 'b, 'c) T1 \<Rightarrow> 'z) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'z)" where
  "curry_T1 f a b c = f (\<lparr> T1.p1\<^sub>f = a, p2\<^sub>f = b, p3\<^sub>f = c \<rparr>)"

fun curry_T0 :: "(('a, 'b) T0 \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c)" where
  "curry_T0 f a b = f (\<lparr> T0.p1\<^sub>f = a, p2\<^sub>f = b \<rparr>)"

type_synonym concr_device_state = "Meson_timer_reg\<^sub>T"
type_synonym concr_state = "Meson_timer\<^sub>T"

axiomatization
  where  reset_timer_e_def : "reset_timer_e reg =
      reg \<lparr> timer_e_hi\<^sub>f := 0, timer_e\<^sub>f := 0 \<rparr>
     "

definition concr_driver :: "(concr_state, VAddr, 64 word, 16 word, bool) driver"
  where
  "concr_driver = 
\<lparr> 
  get_time = meson_get_time,
  init = curry_T0 meson_init,
  stop_timer = meson_stop_timer,
  set_timeout = curry_T1 meson_set_timeout,
\<comment> \<open>we are going to multiply it by 1000 (\<approx> 1024 = 2^10) \<close>
  stateInv = (\<lambda>s. timer_e_hi\<^sub>f (regs\<^sub>f s) < 2^(32-10)
             \<and>  disable\<^sub>f s = Not (timer_a_en\<^sub>f (regs\<^sub>f s)) ),
  iniDeviceInv = (\<lambda>s r. (disable\<^sub>f s = True \<and> Not (timer_a_en\<^sub>f (config_get_regs r))))
\<rparr>
"


locale concr_is_refinement = 
  is_refinement concr_driver mor
  for mor :: "(concr_state, VAddr, 64 word, 16 word, bool) driver_abstr"

  

fun \<alpha>timeout_timebase :: "Timeout_timebase\<^sub>T \<Rightarrow> TimerSpec.timeout_timebase"
  where 
   "\<alpha>timeout_timebase (TIMEOUT_TIMEBASE_100_US _) = TimerSpec.TIMEOUT_TIMEBASE_1_US"
|  "\<alpha>timeout_timebase (TIMEOUT_TIMEBASE_10_US _)  = TimerSpec.TIMEOUT_TIMEBASE_10_US"
|  "\<alpha>timeout_timebase (TIMEOUT_TIMEBASE_1_MS _)   = TimerSpec.TIMEOUT_TIMEBASE_1_MS"
|  "\<alpha>timeout_timebase (TIMEOUT_TIMEBASE_1_US _)   = TimerSpec.TIMEOUT_TIMEBASE_1_US"
   
   
fun \<alpha>timestamp_timebase :: "Timestamp_timebase\<^sub>T \<Rightarrow> TimerSpec.timestamp_timebase"
  where 
   "\<alpha>timestamp_timebase (TIMESTAMP_TIMEBASE_100_US _) = TimerSpec.TIMESTAMP_TIMEBASE_100_US"
|  "\<alpha>timestamp_timebase (TIMESTAMP_TIMEBASE_10_US _)  = TimerSpec.TIMESTAMP_TIMEBASE_10_US"
|  "\<alpha>timestamp_timebase (TIMESTAMP_TIMEBASE_1_MS _)   = TimerSpec.TIMESTAMP_TIMEBASE_1_MS"
|  "\<alpha>timestamp_timebase (TIMESTAMP_TIMEBASE_1_US _)   = TimerSpec.TIMESTAMP_TIMEBASE_1_US"
|  "\<alpha>timestamp_timebase (TIMESTAMP_TIMEBASE_SYSTEM _) = TimerSpec.TIMESTAMP_TIMEBASE_SYSTEM"


definition \<alpha>_timer_mode :: "bool \<Rightarrow> timer_mode"
  where "\<alpha>_timer_mode b = (if b then Periodic else NotPeriodic)"

definition \<alpha>_reg :: "concr_device_state \<Rightarrow> device_state" where
"\<alpha>_reg ds = 
    \<lparr> timer_a_mode = \<alpha>_timer_mode (timer_a_mode\<^sub>f ds) ,
     timer_a_en = timer_a_en\<^sub>f ds,
timer_a = unat (timer_a\<^sub>f ds),
timer_a_input_clk = \<alpha>timeout_timebase (timer_a_input_clk\<^sub>f ds),
timer_e_input_clk = \<alpha>timestamp_timebase (timer_e_input_clk\<^sub>f ds),
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
lemmas simp_defs = driver_defs \<alpha>_state_def \<alpha>_reg_def (* \<alpha>timeout_timebase_def 
 \<alpha>timestamp_timebase_def *)



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
  reset_timer_e_def)
     apply(case_tac s, rename_tac regs disable, case_tac regs)
    apply(simp add: take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t_def)
     (* hmm *)
    apply clarsimp
  apply(simp add:word_cat_def)

(* yeah! *)
     apply (simp add:simp_defs meson_stop_timer_def  ns_in_us_def take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t_def)

  
    
    apply(simp add:simp_defs  meson_set_timeout_def  take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t_def Let\<^sub>d\<^sub>s_def)
     apply(simp add:unat_ucast_up)

(* invariants *)
    apply(simp add:simp_defs meson_init_def take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t_def Let\<^sub>d\<^sub>s_def reset_timer_e_def)
     apply(simp add:simp_defs  meson_stop_timer_def  ns_in_us_def take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t_def)

    apply(simp add:simp_defs meson_init_def take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t_def Let\<^sub>d\<^sub>s_def reset_timer_e_def)
   apply(simp add:simp_defs  meson_stop_timer_def  ns_in_us_def take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t_def)

  apply(simp add:simp_defs  meson_set_timeout_def  take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t_def Let\<^sub>d\<^sub>s_def)
  
  by(simp add: HOL.Let_def )
  

end