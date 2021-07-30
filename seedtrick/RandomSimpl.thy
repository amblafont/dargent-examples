theory RandomSimpl
imports  "AutoCorres.AutoCorres"
begin
(* ******

AutoCorres embedding/specification 

******** *)


record ac_Seed = 
   dummy :: nat



(* AutoCorres specification of the C function 
  char ac_rand ();
*)
definition
  ac_rand :: "('state, nat) nondet_monad"
where
 "ac_rand \<equiv> do x <- select UNIV;
         return x
od
"

(*

sh_SeedValue ac_rand_with_seed(sh_Seed * s) {
   sh_SeedValue r = 
      // what else?
      { .seed = s, 
        .value = ac_rand() };
   return r;
}

*)
definition ac_rand_with_seed :: "ac_Seed ptr \<Rightarrow> ('state, ac_Seed ptr \<times> nat) nondet_monad "
  where "ac_rand_with_seed s = 
do r <- ac_rand;            
  return (s, r)
od"

lemma ac_rand_with_seed_spec :
   "\<And> ptr_seed state. ac_rand_with_seed ptr_seed state = 
      ({((ptr_seedf, x), statef) . ptr_seedf = ptr_seed \<and> statef = state},
             False)"  
  apply(simp add:ac_rand_with_seed_def ac_rand_def)
  by monad_eq

(*

ac_main : sh_Seed -> sh_SeedValue
ac_main seed = 
  let r { seed } = ac_rand_with_seed seed in
  let r2 { seed }  = ac_rand_with_seed seed in
   #{ seed = seed,
      value = r.value + r2.value
   }

*)

definition ac_main :: "ac_Seed ptr \<Rightarrow> ('state, ac_Seed ptr \<times> nat) nondet_monad"
  where "ac_main s = 
  do (s1, v1) <- ac_rand_with_seed s ;
     (s2, v2) <- ac_rand_with_seed s1 ;
     return (s2, v1 + v2)
od
"


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
consts val_rel_seed :: "ac_Seed \<Rightarrow> sh_Seed \<Rightarrow> bool"
(*   where "rel_seed ac_seed sh_seed = undefined" *)

type_synonym heap = "ac_Seed ptr \<Rightarrow> ac_Seed"

definition corres :: "
   (ac_Seed ptr \<Rightarrow> (heap, ac_Seed ptr \<times> nat) nondet_monad)
\<Rightarrow> (sh_Seed \<Rightarrow> sh_Seed \<times> nat)
\<Rightarrow> bool"
  where "corres f' f = 
(\<forall> s' s (\<sigma> :: heap). 
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
 

lemma refine_rand_with_seed : "(corres ac_rand_with_seed sh_rand_with_seed)"
  oops

(* Actually, I can show that it is impossible ! *)
lemma no_refine_rand_with_seed   :
  assumes corr: "corres ac_rand_with_seed sh_rand_with_seed"
  fixes ac_seed sh_seed
  assumes seed_rel : "val_rel_seed ac_seed sh_seed"
  shows "False"
proof -
  let ?heap = "\<lambda>_. ac_seed"
  let ?ac_ptr_seed = "Ptr 0"
  have "
((\<And> ac_ptr_seedf sh_seedf 
   ac_ret sh_ret  
   heapf. 
   ((ac_ptr_seedf, ac_ret), heapf) \<in> fst (ac_rand_with_seed ?ac_ptr_seed ?heap)
\<Longrightarrow> (sh_seedf, sh_ret) = sh_rand_with_seed sh_seed
\<Longrightarrow> ac_ret = sh_ret \<and> val_rel_seed (heapf ac_ptr_seedf) sh_seedf))"
  using corr seed_rel
  apply(simp add:corres_def  ac_rand_with_seed_spec)
  by fastforce
  then have "\<And> (ac_ret :: nat). snd (sh_rand_with_seed sh_seed) = ac_ret"
    apply(simp add: ac_rand_with_seed_spec)
    by (metis prod.collapse)
  then show "False"    
    by presburger
    
lemma refine_main : "corres ac_main sh_main"
  oops



