(*
This file is generated by Cogent

*)

theory Ex1_dargentisa_Shallow_Desugar
imports "Ex1_dargentisa_ShallowShared"
begin

definition
  main :: " Ex\<^sub>T \<Rightarrow>  Ex\<^sub>T"
where
  "main ds\<^sub>0 \<equiv> HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>0 Ex.field0\<^sub>f) (\<lambda>(field0,ds\<^sub>1). HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>1 Ex.field1\<^sub>f) (\<lambda>(field1,ds\<^sub>2). HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>2 Ex.field2\<^sub>f) (\<lambda>(field2,r). Ex.field2\<^sub>f_update (\<lambda>_. field2) (Ex.field1\<^sub>f_update (\<lambda>_. field1) (Ex.field0\<^sub>f_update (\<lambda>_. field0) r)))))"

end