theory DriverSpec
  imports Main
begin

record ('s, 'reg, 'time, 'timeout, 'timer_mode) driver =
   get_time :: "'s \<Rightarrow> 'time" 
   init :: "'s \<Rightarrow> 'reg \<Rightarrow> 's"
   stop_timer :: "'s \<Rightarrow> 's"
   set_timeout :: "'s \<Rightarrow> 'timeout \<Rightarrow> 'timer_mode \<Rightarrow> 's"
   (* This is because the concrete get_time can trigger an overflow 
      and we want to avoid this
    *)
   stateInv :: "'s \<Rightarrow> bool"
   iniDeviceInv :: "'s \<Rightarrow> 'reg \<Rightarrow> bool"

locale dataInvariant =
  fixes dr ::  "('s1, 'r1, 't1, 'to1, 'tm1) driver"  
  assumes initDI : "iniDeviceInv dr s r \<Longrightarrow> stateInv dr (init dr s r)"
  assumes stop_timerDI :  "stateInv dr s \<Longrightarrow> stateInv dr (stop_timer dr s)"
  assumes set_timeoutDI : "stateInv dr s \<Longrightarrow> stateInv dr (set_timeout dr s to tm)"

  

record ('s1, 'r1, 't1, 'to1, 'tm1, 
        's2, 'r2, 't2, 'to2, 'tm2) 
  driver_morphism_rec =
  mor_state :: "'s1 \<Rightarrow> 's2" ("\<alpha>\<index>")
  mor_reg :: "'r1 \<Rightarrow> 'r2" ("\<alpha>reg\<index>")
  mor_time :: "'t1 \<Rightarrow> 't2" ("\<alpha>time\<index>")
  mor_timeout :: "'to1 \<Rightarrow> 'to2" ("\<alpha>timeout\<index>")
  mor_timer_mode :: "'tm1  \<Rightarrow> 'tm2" ("\<alpha>timermode\<index>")



locale driver_morphism_laws =  


  fixes dr1 ::  "('s1, 'r1, 't1, 'to1, 'tm1) driver"
  fixes dr2 :: "('s2, 'r2, 't2, 'to2, 'tm2) driver" 
  fixes mor :: "('s1, 'r1, 't1, 'to1, 'tm1, 
                 's2, 'r2, 't2, 'to2, 'tm2) driver_morphism_rec"   (structure) 
  assumes \<alpha>get_time : "\<And> s. stateInv dr1 s \<Longrightarrow> get_time dr2 (\<alpha> s) = \<alpha>time (get_time dr1 s)"
  assumes \<alpha>init : "init dr2 (\<alpha> s) (\<alpha>reg r) = \<alpha> (init dr1 s r)"
  assumes \<alpha>stop_timer : "stop_timer dr2 (\<alpha> s) = \<alpha> (stop_timer dr1 s)"
  assumes \<alpha>set_timeout : "   set_timeout dr2 (\<alpha> s) (\<alpha>timeout to) (\<alpha>timermode tm) = \<alpha> (set_timeout dr1 s to tm)"
  assumes \<alpha>stateInv : "stateInv dr1 s \<Longrightarrow> stateInv dr2 (\<alpha> s)"
  assumes \<alpha>iniDeviceInv : "iniDeviceInv dr1 s r \<Longrightarrow> iniDeviceInv dr2 (\<alpha> s) (\<alpha>reg r)"

(* abstract driver *)

definition "ns_in_us = (1000 :: nat)"

datatype timer_mode = Periodic | NotPeriodic

datatype timestamp_timebase =
  TIMESTAMP_TIMEBASE_SYSTEM
  | TIMESTAMP_TIMEBASE_1_US
  | TIMESTAMP_TIMEBASE_10_US
  | TIMESTAMP_TIMEBASE_100_US
  | TIMESTAMP_TIMEBASE_1_MS

datatype timeout_timebase =
   TIMEOUT_TIMEBASE_1_US
 | TIMEOUT_TIMEBASE_10_US
 | TIMEOUT_TIMEBASE_100_US
 | TIMEOUT_TIMEBASE_1_MS


record driver_state =
  disable :: bool

record device_state =
  timer_a_mode :: timer_mode
  timer_a_en :: bool
  timer_a :: nat
  timer_a_input_clk :: timeout_timebase
  timer_e_input_clk :: timestamp_timebase
  timer_e_low_hi :: nat


record abstr_state =
  driverState :: driver_state
  deviceState :: device_state

definition abs_driver :: "(abstr_state, device_state, nat, nat, timer_mode) driver"
  where
  "abs_driver = 
\<lparr> get_time = (\<lambda> s. (timer_e_low_hi (deviceState s))  * (ns_in_us :: nat)),

 init = (\<lambda> s r. s \<lparr> deviceState := r \<lparr>     
        timer_e_low_hi := 0
      , timer_a_input_clk := TIMEOUT_TIMEBASE_1_MS
      , timer_e_input_clk := TIMESTAMP_TIMEBASE_1_US
 \<rparr> \<rparr>),

 stop_timer = (\<lambda> s. \<lparr> 
     driverState = \<lparr> disable = True \<rparr>,
     deviceState = (deviceState s) \<lparr> timer_a_en := False \<rparr>
     \<rparr>
  ),

set_timeout = (\<lambda> s timeout periodic. 
  let deviceState' = (deviceState s) \<lparr>
      timer_a := timeout,
      timer_a_mode := periodic,
      timer_a_en := 
         if disable (driverState s) then
           True
         else
           timer_a_en (deviceState s)
      \<rparr>
    in
       \<lparr> driverState = \<lparr> disable = False \<rparr>,
        deviceState = deviceState' \<rparr>
   )
   , stateInv = (\<lambda>s. disable (driverState s) = Not (timer_a_en (deviceState s)))
   , iniDeviceInv = (\<lambda>s r. disable (driverState s) \<and> Not (timer_a_en r))

\<rparr>
"

interpretation dataInvariant abs_driver
  apply unfold_locales
  by(simp add:abs_driver_def)+


type_synonym ('s, 'r, 'time, 'timeout, 'timer_mode) driver_abstr = 
   "('s, 'r, 'time, 'timeout, 'timer_mode, 
     abstr_state, device_state, nat, nat, timer_mode) driver_morphism_rec"

locale is_refinement = 
  driver_morphism_laws dr abs_driver mor
+ dataInvariant dr
  for dr :: "('s, 'r, 'time, 'timeout, 'timer_mode) driver"
 and mor :: "('s, 'r, 'time, 'timeout, 'timer_mode) driver_abstr"

  
end
