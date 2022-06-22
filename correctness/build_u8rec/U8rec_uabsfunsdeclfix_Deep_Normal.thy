(*
This file is generated by Cogent

*)

theory U8rec_uabsfunsdeclfix_Deep_Normal
imports "Cogent.Cogent"
begin

definition
  abbreviatedType1 :: " Cogent.type"
where
  "abbreviatedType1 \<equiv> TRecord [(''a'', (TPrim (Num U8), Present))] (Boxed Writable undefined)"

lemmas abbreviated_type_defs =
  abbreviatedType1_def

definition
  main_type :: " Cogent.kind list \<times>  Cogent.type \<times>  Cogent.type"
where
  "main_type \<equiv> ([], (abbreviatedType1, abbreviatedType1))"

definition
  main :: "string Cogent.expr"
where
  "main \<equiv> Let (Var 0) (Var 0)"

ML \<open>
val Cogent_functions = ["main"]
val Cogent_abstract_functions = []
\<close>

end