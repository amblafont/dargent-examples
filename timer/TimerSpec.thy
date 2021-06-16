theory TimerSpec
  imports Main "HOL-Word.Word" "Word_Lib.Word_Lib" 
begin

record ('s, 'time, 'timeout) driver =
  (*  invariants 
   dataInv :: "'s \<Rightarrow> bool"
   brightnessInv :: "'b \<Rightarrow> bool"
   indexInv :: "'s \<Rightarrow> 'i \<Rightarrow> bool"    *)
  (*  interface *)
(* TODO: replace 'n with nat, or better, remove this field *)
   get_time :: "'s \<Rightarrow> 'time"
   init :: "'s \<Rightarrow> 's"
   stop_timer :: "'s \<Rightarrow> 's"
   set_timeout :: "'s \<Rightarrow> 'timeout \<Rightarrow> bool \<Rightarrow> 's"
   is_disabled :: "'s \<Rightarrow> bool"


record driver_state =
  is_disabled :: "bool"
(* difference with the original state *)
  brightness :: nat
  (* nleds :: nat *)

(* what is the point of having bool^8 instead of 8 word? *)
type_synonym device_colour = "8 word"

term unat
term uint
find_theorems uint
term word_of_int
term Abs_word
term word_of_nat
find_consts nat "_ word"
find_consts nat int


fun serialise_channel :: "nat \<Rightarrow> 8 word \<Rightarrow> device_colour" where
  "serialise_channel br r = 
     word_of_int (int ((br * unat r) div 256))"


record abstr_state =
  driverState :: driver_state
  deviceState :: "device_colour triple list"
  

definition abs_dataInv :: "abstr_state \<Rightarrow> bool"
  where "abs_dataInv s = 
      (length (leds (driverState s)) = length (deviceState s))" 

(* brightness is a 8 word *)
definition abs_driver :: "(abstr_state, nat, nat, 8 word, rgb) driver"
  where
  "abs_driver = 
  \<lparr> 
  
   dataInv = (\<lambda> s. (length (leds (driverState s)) = length (deviceState s))
   \<and> brightness (driverState s) \<le> (256 :: nat)
           ),
   brightnessInv = (\<lambda> b. True),
   indexInv = (\<lambda> s i. i < length (leds (driverState s))),
   get_nleds = (\<lambda> s. length (leds (driverState s))),
   setB = (\<lambda>s b . s\<lparr>driverState := (driverState s)
  \<comment> \<open>this definition is strange... \<close>
   \<lparr>brightness := if b = 0 then 0 else unat b + 1\<rparr> \<rparr>) ,
   setL = (\<lambda>s i c. s\<lparr>driverState := (driverState s)
               \<lparr>leds := (leds (driverState s))[i := c]\<rparr> \<rparr>),
   commit = (\<lambda> s . s\<lparr> deviceState := 
                map (\<lambda> (w1, w2, w3) .
                      (serialise_channel (brightness (driverState s)) w1,
                       serialise_channel (brightness (driverState s)) w2,
                       serialise_channel (brightness (driverState s)) w3)
                      )
                (leds (driverState s)) \<rparr>)
\<rparr>"
(*    
*)
locale driver_invariants =
  fixes dr :: "('s, 'i, 'n, 'b, 'c) driver"
  assumes
    setBInv : "dataInv dr s \<Longrightarrow> brightnessInv dr b \<Longrightarrow>
               dataInv dr (setB dr s b)"
  assumes
    setLInv : "dataInv dr s \<Longrightarrow> indexInv dr s i
                   \<Longrightarrow> dataInv dr (setL dr s i c)"
  assumes commitInv : 
      "dataInv dr s \<Longrightarrow> dataInv dr (commit dr s)"

interpretation abstr_implementation:
  driver_invariants abs_driver
  apply unfold_locales
  apply ( simp add:abs_driver_def)

record ('s1, 'i1, 'n1, 'b1, 'c1, 's2, 'i2, 'n2, 'b2, 'c2) 
  driver_morphism_rec =
  mor_state :: "'s1 \<Rightarrow> 's2" ("\<alpha>\<index>")
  mor_index :: "'i1 \<Rightarrow> 'i2" ("\<alpha>index\<index>")
  mor_brightness :: "'b1 \<Rightarrow> 'b2" (* abstract brightness *) ("\<alpha>brightness\<index>")
  mor_length :: "'n1  \<Rightarrow> 'n2" ("\<alpha>length\<index>")
  mor_colour :: "'c1 \<Rightarrow> 'c2" ("\<alpha>colour\<index>")

type_synonym ('s, 'i, 'n, 'b, 'c) driver_abstr = 
   "('s, 'i, 'n, 'b, 'c, 
     abstr_state, nat, nat, 8 word, rgb) driver_morphism_rec"

(*
  fixes \<alpha> :: "'s1 \<Rightarrow> 's2"

fixes \<alpha>index :: "'i1 \<Rightarrow> 'i2"
fixes \<alpha>brightness :: "'b1 \<Rightarrow> 'b2" (* abstract brightness *)
fixes \<alpha>length :: "'n1  \<Rightarrow> 'n2"
fixes \<alpha>colour :: "'c1 \<Rightarrow> 'c2"*)

(*
locale driver_morphism =
fixes \<alpha> :: "'s1 \<Rightarrow> 's2"
fixes \<alpha>index :: "'i1 \<Rightarrow> 'i2"
fixes \<alpha>brightness :: "'b1 \<Rightarrow> 'b2" (* abstract brightness *)
fixes \<alpha>length :: "'n1  \<Rightarrow> 'n2"
fixes \<alpha>colour :: "'c1 \<Rightarrow> 'c2"
*)

locale driver_morphism_laws =  


  fixes dr1 ::  "('s1, 'i1, 'n1, 'b1, 'c1) driver"
  fixes dr2 :: "('s2, 'i2, 'n2, 'b2, 'c2) driver" 
 fixes mor :: "('s1, 'i1, 'n1, 'b1, 'c1, 's2, 'i2, 'n2, 'b2, 'c2) 
   driver_morphism_rec"   (structure) 

  
(* assumes driver_morphism: "driver_morphism \<alpha> \<alpha>index \<alpha>brightness \<alpha>length \<alpha>colour" *)

assumes \<alpha>Inv : "dataInv dr1 s \<Longrightarrow> dataInv dr2 (\<alpha> s)"

assumes \<alpha>indexInv : "dataInv dr1 s \<Longrightarrow> indexInv dr1 s i 
               \<Longrightarrow> indexInv dr2 (\<alpha> s) (\<alpha>index i)"

assumes \<alpha>get_nleds : "dataInv dr1 s \<Longrightarrow> get_nleds dr2 (\<alpha> s) = \<alpha>length (get_nleds dr1 s)"
assumes \<alpha>setB : "dataInv dr1 s \<Longrightarrow> brightnessInv dr1 b \<Longrightarrow>
   setB dr2 (\<alpha> s) (\<alpha>brightness b) = \<alpha> (setB dr1 s b)"
assumes \<alpha>setL : "dataInv dr1 s \<Longrightarrow> indexInv dr1 s i \<Longrightarrow>
   setL dr2 (\<alpha> s) (\<alpha>index i) (\<alpha>colour c) = 
       \<alpha> (setL dr1 s i c)"
assumes \<alpha>commit : "dataInv dr1 s \<Longrightarrow>
   commit dr2 (\<alpha> s) = \<alpha> (commit dr1 s)"



locale is_refinement = 
  driver_morphism_laws _ abs_driver mor
  for mor :: "('s, 'i, 'n, 'b, 'c) driver_abstr"

(*

(* don't we want a kind of surjectivity as well? 
Otherwise, I can just define a driver implementation whose invariant is 
always wrong. Then, it will be a valid refinement... 

This category is no longer locally presentable, but still accessible.
*)
locale driver_mor_epi =
  driver_morphism dr1 dr2 \<alpha> \<alpha>index \<alpha>brightness \<alpha>length \<alpha>colour
  for dr1 ::  "('s1, 'i1, 'n1, 'b1, 'c1) driver"
   and dr2 ::  "('s2, 'i2, 'n2, 'b2, 'c2) driver"
   and  \<alpha> \<alpha>index \<alpha>brightness \<alpha>length \<alpha>colour +
 fixes \<alpha>_section :: "'s2 \<Rightarrow> 's1"
 fixes \<alpha>index_section :: "'i2 \<Rightarrow> 'i1"
 fixes \<alpha>brightness_section :: "'b2 \<Rightarrow> 'b1" (* abstract brightness *)
(* fixes \<alpha>length_section :: "'n2  \<Rightarrow> 'n1" 
if dr2 = abs_driver, then this can be deduced.
*)
 fixes \<alpha>colour_section :: "'c2 \<Rightarrow> 'c1"

assumes \<alpha>_sectionInv :  "dataInv dr2 s \<Longrightarrow> dataInv dr1 (\<alpha>_section s)"
assumes \<alpha>index_sectionInv : "dataInv dr2 s \<Longrightarrow> indexInv dr2 s i \<Longrightarrow>
         indexInv dr1 (\<alpha>_section s) (\<alpha>index_section i)"

assumes \<alpha>_section_eq :  "dataInv dr2 s \<Longrightarrow> \<alpha> ( \<alpha>_section s) = s"
assumes \<alpha>index_section_eq : "dataInv dr2 s \<Longrightarrow> indexInv dr2 s i \<Longrightarrow>
   \<alpha>index (\<alpha>index_section i) = i " 
assumes \<alpha>brightness_section : "\<alpha>brightness \<circ> \<alpha>brightness_section = id"
(*
assumes \<alpha>length_section : "\<alpha>length \<circ> \<alpha>length_section = id"
*)
assumes \<alpha>colour_section : "\<alpha>colour \<circ> \<alpha>colour_section = id"

(* Note: I should define invariants for brightness (< 255) and color *)
definition is_refinement_epi :: 
  "('s, 'i, 'n, 'b, 'c) driver \<Rightarrow>
    ('s \<Rightarrow> _) \<Rightarrow> ('i \<Rightarrow> _) \<Rightarrow> ('b \<Rightarrow> _) \<Rightarrow> ('n \<Rightarrow> _) \<Rightarrow> ('c \<Rightarrow> _) \<Rightarrow>
   _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow>
 bool"
  where "is_refinement_epi dr 
  \<alpha> \<alpha>index \<alpha>brightness \<alpha>length \<alpha>colour
  \<alpha>_section \<alpha>index_section \<alpha>brightness_section \<alpha>colour_section
 = 
(driver_mor_epi dr abs_driver \<alpha> \<alpha>index \<alpha>brightness \<alpha>length \<alpha>colour
  \<alpha>_section \<alpha>index_section \<alpha>brightness_section \<alpha>colour_section)"

*)


subsection \<open>Concrete Refinement\<close>

subsubsection \<open>Helpers\<close>

fun extract_Error :: "('a, 'a) Error \<Rightarrow> 'a" where
  "extract_Error (Ok a) = a"
| "extract_Error (Err a) = a"

fun curry_T1 :: "(('a, 'b) T1 \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c)" where
  "curry_T1 f a b = f (\<lparr> T1.p1\<^sub>f = a, p2\<^sub>f = b \<rparr>)"

fun uncurry_T1 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> (('a, 'b) T1 \<Rightarrow> 'c)" where
  "uncurry_T1 f (\<lparr> T1.p1\<^sub>f = a, p2\<^sub>f = b \<rparr>) = f a b"

fun curry_T0 :: "(('a, 'b, 'c, 'd, 'e) T0 \<Rightarrow> 'z) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'z)" where
  "curry_T0 f a b c d e = f (\<lparr> T0.p1\<^sub>f = a, p2\<^sub>f = b, p3\<^sub>f = c, p4\<^sub>f = d, p5\<^sub>f = e \<rparr>)"

fun uncurry_T0 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'z) \<Rightarrow> (('a, 'b, 'c, 'd, 'e) T0 \<Rightarrow> 'z)" where
  "uncurry_T0 f (\<lparr> T0.p1\<^sub>f = a, p2\<^sub>f = b, p3\<^sub>f = c, p4\<^sub>f = d, p5\<^sub>f = e \<rparr>) = f a b c d e"


subsubsection \<open>Concrete driver\<close>

fun ws_set_led' :: "Wsp\<^sub>T \<Rightarrow> 32 word \<Rightarrow> (8 word \<times> 8 word \<times> 8 word) \<Rightarrow> Wsp\<^sub>T" where
  "ws_set_led' s i (r,g,b) = curry_T0 (ws_set_led) s i r g b"



definition wsp_length_correctness_condition :: "Wsp\<^sub>T \<Rightarrow> bool" where
  "wsp_length_correctness_condition (r :: Wsp\<^sub>T) \<equiv>
    length (led_data\<^sub>f r) = length (led_state\<^sub>f r)
    \<and> length (led_state\<^sub>f r) < 0xFFFFFFFF"


definition concr_driver :: "(Wsp\<^sub>T, 32 word, nat, 32 word, 8 word triple) driver"
  where
  "concr_driver = 
  \<lparr> 
  
   dataInv = wsp_length_correctness_condition,
   brightnessInv = (\<lambda> b. unat b < 256),
   indexInv = (\<lambda> s i. unat i < length (led_data\<^sub>f s)),
\<comment> \<open>difference with the original implementation: not 8\<close>
   get_nleds = (\<lambda> s.  ( length (led_data\<^sub>f s))),
   setB = curry_T1 (extract_Error \<circ> ws_set_brightness) ,
   setL = ws_set_led' ,
   commit = ws_commit 
\<rparr>"

locale concr_is_refinement = 
  is_refinement concr_driver mor
  for mor :: "(Wsp\<^sub>T, 32 word, nat, 32 word, 8 word triple) driver_abstr"




subsection \<open>Abstraction Definitions\<close>


type_synonym LEDArray = "Rgb\<^sub>T list"
type_synonym led = "8 word triple"
type_synonym LEDData = "RgbX\<^sub>T list"

definition extract_led_arr_val :: "LEDArray \<Rightarrow> led list" where
  "extract_led_arr_val xs = map (\<lambda>grb. (g\<^sub>f grb, r\<^sub>f grb, b\<^sub>f grb)) xs"

lemma extract_led_arr_val_length[simp]:
  shows "length (extract_led_arr_val xs) = length xs"
  by (simp add: extract_led_arr_val_def)

lemma extract_led_arr_val_nth:
  assumes "i < length xs"
  shows "extract_led_arr_val xs ! i = (g\<^sub>f (xs ! i), r\<^sub>f (xs ! i), b\<^sub>f (xs ! i))"
  using assms
  by (simp add: extract_led_arr_val_def)

(* inverse of expand_channel *)
definition split_led_encoding :: "32 word \<Rightarrow> 8 word" where
  "split_led_encoding w = 
    (let encode = (\<lambda>w. (if w = (0x88 :: 8 word) then (0 :: 8 word)
                        else if w = (0x8c :: 8 word) then 1
                        else if w = (0xc8 :: 8 word) then 2
                        else if w = (0xcc :: 8 word) then 3
                        else undefined))
     in    (encode (ucast ((w >> 24) && 0xFF)) << 6)
       ||  (encode (ucast ((w >> 16) && 0xFF)) << 4)
       ||  (encode (ucast ((w >> 8) && 0xFF)) << 2)
       ||  (encode (ucast (w && 0xFF)))
)"
lemma saveme : 
    "split_led_encoding (expand_channel x) 
   =  SCAST(32 \<rightarrow> 8) x
    "
  sorry


 definition extract_led_data_val :: "LEDData \<Rightarrow> device_colour triple list" where
  "extract_led_data_val as = map (\<lambda>a. (split_led_encoding (gx\<^sub>f a), split_led_encoding (rx\<^sub>f a), split_led_encoding (bx\<^sub>f a))) as"
 
 lemma extract_led_data_val_length[simp]:
  "length (extract_led_data_val xs) = length xs"
  by (simp add: extract_led_data_val_def) 

 lemma extract_led_data_val_nth:
  assumes "i < length xs"
  shows "extract_led_data_val xs ! i = (split_led_encoding (gx\<^sub>f (xs ! i)), split_led_encoding (rx\<^sub>f (xs ! i)), split_led_encoding (bx\<^sub>f (xs ! i)))"
  using assms
  by (simp add: extract_led_data_val_def) 


subsection \<open>Concrete Abstraction Functions\<close>

definition \<alpha>Wsp\<^sub>T :: "Wsp\<^sub>T \<Rightarrow> abstr_state" where
  "\<alpha>Wsp\<^sub>T r = 
   \<lparr> driverState = \<lparr> leds = extract_led_arr_val (led_state\<^sub>f r),
     brightness = ucast (brightness\<^sub>f r) \<rparr>, 
     deviceState = extract_led_data_val (led_data\<^sub>f r) \<rparr>"

definition abstraction :: "(Wsp\<^sub>T, 32 word, nat, 32 word, 8 word triple) driver_abstr"
  where "abstraction = 
  \<lparr>
   mor_state = \<alpha>Wsp\<^sub>T,
   mor_index = unat,
   mor_brightness = ucast, 
   mor_length = id,
   mor_colour = id 
  \<rparr>"

(*
definition serialise_led :: "nat \<Rightarrow> led \<Rightarrow> device_colour triple" where
  "serialise_led br led = (serialise_channel br (\<alpha>g led), serialise_channel br (\<alpha>r led), serialise_channel br (\<alpha>b led))"


definition leds_to_device_state :: "nat \<Rightarrow> led list \<Rightarrow> device_state" where
  "leds_to_device_state br led_list \<equiv> map (serialise_led br) led_list"
*)

lemmas driver_defs = concr_driver_def abs_driver_def abstraction_def
lemmas simp_defs = driver_defs
   wsp_length_correctness_condition_def \<alpha>Wsp\<^sub>T_def

lemmas cogent_defs = 
Let_def  take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t_def Let\<^sub>d\<^sub>s_def T1.defs 

lemma map2_fst_trivial:
  assumes "length xs = length ys"
  shows "fst (array_map2 (\<lambda>x y. (f x, g x y)) xs ys) = map f xs"
  using assms
  by (induct rule: list_induct2) (clarsimp split: prod.splits)+

lemma map2_snd_trivial:
  assumes "length xs = length ys"
  shows "snd (array_map2 (\<lambda>x y. (f x, g x y)) xs ys) = map2 g xs ys"
  using assms
  by (induct rule: list_induct2) (clarsimp split: prod.splits)+

lemma map2_snd_trivial':
  assumes "length xs = length ys"
  shows "snd (array_map2 (\<lambda>x y. (f x, g x)) xs ys) = map g xs"
  using assms
  by (induct rule: list_induct2) (clarsimp split: prod.splits)+


(*
definition unzip :: "('a \<times> 'b) list \<Rightarrow> 'a list \<times> 'b list"
  where "unzip l = (map fst l, map snd l)"
lemma array_map2_spec :
  assumes "length l1 = length l2"
  shows
  "array_map2 f l1 l2 =
   unzip ( map2 f l1 l2)"
  using assms
  apply (induct rule: list_induct2) 
   apply (simp add:unzip_def)
  apply (simp add:unzip_def)  
  using case_prod_beta by blast

*)

lemma elim_rgb : "ds \<lparr> gx\<^sub>f := g,
                    rx\<^sub>f := r,
                    bx\<^sub>f := b\<rparr> = 
                  \<lparr> gx\<^sub>f = g,
                    rx\<^sub>f = r,
                    bx\<^sub>f = b\<rparr>
"
  by simp

lemma chiant : "unat (n ) < 2^LENGTH('a :: len) \<Longrightarrow>
 n = ucast (of_nat (unat n) :: 'a word)"
  apply(simp add:ucast_def unat_def)
  apply(simp add: word_ubin.eq_norm word_of_int bintrunc_mod2p )
  done

lemma chiant2 : "unat (n ) < 2^LENGTH('a :: len) \<Longrightarrow>
\<exists> p.  n = ucast (p :: 'a word)"
  apply (drule chiant)
  by blast


lemma commit_refinement':
  assumes "wsp_length_correctness_condition s"
  shows "\<alpha>Wsp\<^sub>T (ws_commit s) = commit abs_driver (\<alpha>Wsp\<^sub>T s)"
(*
 \<lparr> driverState = driverState (\<alpha>Wsp\<^sub>T s),
   deviceState = leds_to_device_state (brightness (driverState (\<alpha>Wsp\<^sub>T s))) (leds (driverState (\<alpha>Wsp\<^sub>T s))) \<rparr>"
*)
  using assms
  apply (simp add:simp_defs)
  
  
  
  apply(simp add:ws_commit_def cogent_defs expand_def)
  apply(intro conjI)+
  apply(simp add:map2_fst_trivial) 
(*   apply(simp add:array_map2_spec unzip_def) *)
  
  apply(simp add:elim_rgb map2_snd_trivial')
  
  (*apply (simp add:array_map2_spec unzip_def) *)
  apply(simp add:extract_led_arr_val_def)
  apply (simp add:extract_led_data_val_def)
  term "(checked_div (brightness\<^sub>f s * UCAST(8 \<rightarrow> 32) (g\<^sub>f x)) 0x100)"
  by(simp add:saveme)

interpretation concr_implementation:
  concr_is_refinement abstraction
  apply unfold_locales
  (* preservation of state invariant *)
       apply (simp add:simp_defs)
      apply (simp add:simp_defs)
     apply (simp add:simp_defs)
(* brightness *)
   apply(simp add:simp_defs)  
apply (
      simp add: \<alpha>Wsp\<^sub>T_def ws_set_brightness_def take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t_def unat_eq_zero word_less_nat_alt
      unat_plus_if' wsp_length_correctness_condition_def)
    apply(intro impI conjI)+
  
     apply(simp add:ucast_def)
     apply(simp only:Word.word.uint_inject[of _ 0, symmetric])
     apply(simp add: unat_def word_ubin.eq_norm word_of_int bintrunc_mod2p )
    apply(simp add:ucast_def)
    apply(simp only:Word.word.uint_inject[ symmetric])
    apply(simp add: unat_def word_ubin.eq_norm word_of_int bintrunc_mod2p )


  find_theorems uint name:inj
  thm word_ubin.eq_norm word_of_int
  find_theorems word_of_int
  find_theorems uint ucast
  
  find_theorems uint
  find_theorems is_up
  find_theorems ucast uint
  find_theorems ucast
  term of_bl
  
     apply (word_bitwise)
  
  find_theorems ucast 
(* set_led *)
  apply(simp add:simp_defs)  
 apply (force split: prod.splits simp add: 

 T1.defs ws_set_led_def \<alpha>Wsp\<^sub>T_def take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t_def
      Let_def Rgb.defs list_eq_iff_nth_eq nth_list_update extract_led_arr_val_def
      wsp_length_correctness_condition_def)

(* commit *)
  by(simp add: driver_defs commit_refinement')
  
end