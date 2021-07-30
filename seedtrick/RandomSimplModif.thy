theory RandomSimplModif
imports  "AutoCorres.AutoCorres"
begin
(* ******

AutoCorres embedding/specification 

******** *)

(* 
// returns true if it worked
// returns false if it didn't (because of failure, for example, the output device)
struct ret_write { 
  tag : u8;
  fail: u8;
  errormsg : char[];
}

ret_write write(int u8);

at the autocorres level, how do you axiomatize write?

char rand() provided the kernel


*)

record ac_Seed = 
   dummy :: nat



(* AutoCorres specification of the C function 
  char ac_rand ();
*)
definition
  ac_rand :: "('state, nat) nondet_monad"
where
 "ac_rand \<equiv> select UNIV        

"

definition ac_main_orig :: "('state,  nat) nondet_monad"
  where "ac_main_orig  = 
  do v1 <- ac_rand  ;
     v2 <- ac_rand  ;
     return (v1 + v2)
od"

lemma "\<And> st. (1, st) \<in> fst (ac_main_orig st)"
  apply(simp add:ac_main_orig_def ac_rand_def)
  apply(monad_eq)
  by presburger
  

(* shallow spec rand ? *)
definition rand :: "nat set"
  where "rand = UNIV"

definition main_spec :: "nat set"
  where "main_spec = { z. \<exists> x y. x \<in> rand \<and> y \<in> rand \<and> z = x + y }"


(* 
relation between ac_rand and rand
*)
definition refines :: "('state, 'a) nondet_monad \<Rightarrow> 'a set \<Rightarrow> bool "
  where "refines c a = ((\<forall> s s' r. (r, s') \<in> fst (c s) \<longrightarrow> r \<in> a \<and> s = s') \<and> (\<forall> s. \<not> snd (c s)))"
lemma "refines ac_rand rand"
  apply(simp add:refines_def ac_rand_def rand_def)
  apply monad_eq
  done
lemma "refines ac_main_orig main_spec"
  apply(simp add:refines_def ac_main_orig_def rand_def ac_rand_def main_spec_def)
  apply monad_eq
  done

(*
lemma "\<And> st. (1, st) \<in> fst (ac_main_orig st)"
*)
(*

sh_SeedValue ac_rand_with_seed(sh_Seed * s) {
   sh_SeedValue r = 
      // what else?
      { .seed = s, 
        .value = ac_rand() };
   return r;
}

*)
definition ac_rand_with_seed :: "'a ptr \<Rightarrow> ('state, 'a ptr \<times> nat) nondet_monad "
  where "ac_rand_with_seed s = 
do r <- ac_rand;            
  return (s, r)
od"
(*
definition rand_seed_spec :: "'a \<Rightarrow> ('a \<times> nat) \<Rightarrow> bool"
  where "rand_seed_spec seed = (seed, )"*)

consts abs_upd_val :: "'au \<Rightarrow> 'av  \<Rightarrow> bool"
type_synonym ('a, 'b) vabsfuns = "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool"
type_synonym ('a, 'b)
consts valRel (*::  "('s \<Rightarrow> 'i \<Rightarrow> 'o \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 's \<Rightarrow> bool" *)

fun valRel_fun :: "_ \<Rightarrow> (('s1 \<Rightarrow> 's2) \<Rightarrow> 'i \<Rightarrow> 'o \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('s1 \<Rightarrow> 's2) \<Rightarrow> bool" where
  "valRel_fun valRel \<xi> f f' =
  (\<forall>(x :: _) x' v'. valRel \<xi> x x' \<longrightarrow> \<xi> f' x' v' \<longrightarrow> valRel \<xi> (f x) v')"
(*
fun valRel_fun :: "('a \<Rightarrow> 's1 \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 's2 \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('s1 \<Rightarrow> 's2) \<Rightarrow> bool" where
  "valRel_fun r1 r2 \<xi> f f' =
  (\<forall>(x :: _) x' v'. valRel \<xi> x x' \<longrightarrow> \<xi> f' x' v' \<longrightarrow> valRel \<xi> (f x) v')"
*)
(*
definition rand_seed_spec :: "'a \<Rightarrow> ('a \<times> nat) set"
  where "rand_seed_spec seed = {(s, r). r \<in> UNIV \<and> s = seed }" 
*)
consts sh_rand_with_seed :: "'b \<Rightarrow> 'b \<times> nat "


(* TODO: specify *)
consts val_rel_seed :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
(*   where "rel_seed ac_seed s = undefined" *)

type_synonym 'a heap = "'a ptr \<Rightarrow> 'a"
term heap
definition corres :: "
   ('a ptr \<Rightarrow> ('a heap, 'a ptr \<times> nat) nondet_monad)
\<Rightarrow> ('b \<Rightarrow> 'b \<times> nat)
\<Rightarrow> bool"
  where "corres f' f = 
(\<forall> s' s (\<sigma> :: 'a heap). 
val_rel_seed (\<sigma> s') s \<longrightarrow>
\<not> snd (f' s' \<sigma>) \<longrightarrow>
(\<forall> s'f sf 
   r' r  
   \<sigma>'. 
   ((s'f, r'), \<sigma>') \<in> fst (f' s' \<sigma>)
\<longrightarrow> (sf, r) = f s
\<longrightarrow> r' = r \<and> val_rel_seed (\<sigma>' s'f) sf
))   
"

consts val_rel :: "('a ptr \<Rightarrow> ('state, 'a ptr \<times> nat) nondet_monad ) \<Rightarrow> "

lemma "refines (ac_rand_with_seed s) (rand_seed_spec s)"
  apply(simp add:refines_def ac_rand_def ac_rand_with_seed_def  rand_seed_spec_def)
  apply monad_eq
  done
lemma "refines ac_main_orig main_spec"
  apply(simp add:refines_def ac_main_orig_def rand_def ac_rand_def main_spec_def)
  apply monad_eq
  done

lemma ac_rand_with_seed_spec :
   "\<And> ptr_seed state. ac_rand_with_seed ptr_seed state = 
      ({((ptr_seedf, x), statef) . ptr_seedf = ptr_seed \<and> statef = state},
             False)"  
  apply(simp add:ac_rand_with_seed_def ac_rand_def)
  by monad_eq

(*

ac_seed_main : sh_Seed -> sh_SeedValue
ac_seed_main seed = 
  let r { seed } = ac_rand_with_seed seed in
  let r2 { seed }  = ac_rand_with_seed seed in
   #{ seed = seed,
      value = r.value + r2.value
   }

*)

definition ac_seed_main :: "ac_Seed ptr \<Rightarrow> ('state, ac_Seed ptr \<times> nat) nondet_monad"
  where "ac_seed_main s = 
  do (s1, v1) <- ac_rand_with_seed s ;
     (s2, v2) <- ac_rand_with_seed s1 ;
     return (s2, v1 + v2)
od
"

definition main_seed_spec :: "'a \<Rightarrow> ('a \<times> nat) set"
  where "main_seed_spec seed = { (s, z). s = seed \<and> (\<exists> x y. x \<in> rand \<and> y \<in> rand \<and> z = x + y) }"

lemma "refines (ac_seed_main s) (main_seed_spec s)"
  apply(simp add:refines_def ac_rand_def ac_rand_with_seed_def rand_def ac_seed_main_def main_seed_spec_def)
  apply monad_eq
  done

definition \<xi>_main_seed :: "'a \<Rightarrow> ('a \<times> nat) \<Rightarrow> bool "
  where "\<xi>_main_seed seed seed_value = (seed_value \<in> main_seed_spec seed)"



(* TODO: give a spec *)
consts sh_rand_with_seed :: "'a \<Rightarrow> 'a \<times> nat "
(*  where "sh_rand_with_seed s = undefined"  *)

definition sh_main :: "'a \<Rightarrow> 'a \<times> nat"
  where "sh_main s = 
    (let (s1, v1) = sh_rand_with_seed s in
     let (s2, v2) = sh_rand_with_seed s1 in
      (s2, v1 + v2))
"

lemma "refines (ac_seed_main s) (main_seed_spec s)"
  apply(simp add:refines_def ac_rand_def ac_rand_with_seed_def rand_def ac_seed_main_def main_seed_spec_def)
  apply monad_eq
  done


(* ******************

Shallow embedding 

******************* *)

(* TODO: give a spec *)
typedecl sh_Seed

(* TODO: give a spec *)
consts sh_rand_with_seed :: "sh_Seed \<Rightarrow> sh_Seed \<times> nat "
(*  where "sh_rand_with_seed s = undefined"  *)

definition sh_main :: "sh_Seed \<Rightarrow> sh_Seed \<times> nat"
  where "sh_main s = 
    (let (s1, v1) = sh_rand_with_seed s in
     let (s2, v2) = sh_rand_with_seed s1 in
      (s2, v1 + v2))
"


(* **************

How do we prove refinement between the autocorres and
the shallow embedding ?

************* *)

(* 

We first need a relation between sh_Seed and ac_Seed values

*)

(* TODO: specify *)
consts rel_seed :: "ac_Seed \<Rightarrow> sh_Seed \<Rightarrow> bool"
(*   where "rel_seed ac_seed s = undefined" *)

type_synonym ac_state = "ac_Seed ptr \<Rightarrow> ac_Seed"

definition corres :: "
   (ac_Seed ptr \<Rightarrow> (ac_state, ac_Seed ptr \<times> nat) nondet_monad)
\<Rightarrow> (sh_Seed \<Rightarrow> sh_Seed \<times> nat)
\<Rightarrow> bool"
  where "corres f' f = 
(\<forall> s' s (ac_state :: ac_state). 
rel_seed (ac_state s') s \<longrightarrow>
\<not> snd (f' s' ac_state) \<longrightarrow>
(\<forall> s'f sf 
   r' r  
   ac_statef. 
   ((s'f, r'), ac_statef) \<in> fst (f' s' ac_state)
\<longrightarrow> (sf, r) = f s
\<longrightarrow> r' = r \<and> rel_seed (ac_statef s'f) sf
))   
"
 

lemma refine_rand_with_seed : "(corres ac_rand_with_seed sh_rand_with_seed)"
  oops

(* Actually, I can show that it is impossible ! *)
lemma no_refine_rand_with_seed   :
  assumes corr: "corres ac_rand_with_seed sh_rand_with_seed"
  fixes ac_seed s
  assumes seed_rel : "rel_seed ac_seed s"
  shows "False"
proof -
  let ?ac_state = "\<lambda>_. ac_seed"
  let ?s' = "Ptr 0"
  have "
((\<And> s'f sf 
   r' r  
   ac_statef. 
   ((s'f, r'), ac_statef) \<in> fst (ac_rand_with_seed ?s' ?ac_state)
\<Longrightarrow> (sf, r) = sh_rand_with_seed s
\<Longrightarrow> r' = r \<and> rel_seed (ac_statef s'f) sf))"
  using corr seed_rel
  apply(simp add:corres_def  ac_rand_with_seed_spec)
  by fastforce
  then have "\<And> (r' :: nat). snd (sh_rand_with_seed s) = r'"
    apply(simp add: ac_rand_with_seed_spec)
    by (metis prod.collapse)
  then show "False"    
    by presburger
    
lemma refine_main : "corres ac_seed_main sh_main"
  oops



