(*
This file is generated by Cogent

*)

theory Ex1_dargentisa_Deep_Normal
imports "Cogent.Cogent"
begin

definition
  abbreviatedType1 :: " Cogent.type"
where
  "abbreviatedType1 \<equiv> TRecord [(''field0'', (TSum [(''Con0'', (TPrim Bool, Unchecked)), (''Con1'', (TPrim Bool, Unchecked))], Present)), (''field1'', (TRecord [(''field0'', (TRecord [(''field0'', (TRecord [(''field0'', (TPrim Bool, Present))] Unboxed, Present)), (''field1'', (TRecord [(''field0'', (TPrim Bool, Present)), (''field1'', (TPrim Bool, Present)), (''field2'', (TPrim Bool, Present))] Unboxed, Present)), (''field2'', (TPrim Bool, Present))] Unboxed, Present)), (''field1'', (TRecord [(''field0'', (TRecord [(''field0'', (TRecord [(''field0'', (TRecord [(''field0'', (TPrim Bool, Present))] Unboxed, Present))] Unboxed, Present)), (''field1'', (TPrim Bool, Present))] Unboxed, Present)), (''field1'', (TPrim Bool, Present))] Unboxed, Present)), (''field2'', (TPrim Bool, Present)), (''field3'', (TPrim Bool, Present)), (''field4'', (TRecord [(''field0'', (TPrim Bool, Present))] Unboxed, Present)), (''field5'', (TPrim Bool, Present)), (''field6'', (TPrim Bool, Present))] Unboxed, Present)), (''field2'', (TPrim Bool, Present))] (Boxed Writable undefined)"

definition
  abbreviatedType2 :: " Cogent.type"
where
  "abbreviatedType2 \<equiv> TRecord [(''field0'', (TRecord [(''field0'', (TRecord [(''field0'', (TPrim Bool, Present))] Unboxed, Present)), (''field1'', (TRecord [(''field0'', (TPrim Bool, Present)), (''field1'', (TPrim Bool, Present)), (''field2'', (TPrim Bool, Present))] Unboxed, Present)), (''field2'', (TPrim Bool, Present))] Unboxed, Present)), (''field1'', (TRecord [(''field0'', (TRecord [(''field0'', (TRecord [(''field0'', (TRecord [(''field0'', (TPrim Bool, Present))] Unboxed, Present))] Unboxed, Present)), (''field1'', (TPrim Bool, Present))] Unboxed, Present)), (''field1'', (TPrim Bool, Present))] Unboxed, Present)), (''field2'', (TPrim Bool, Present)), (''field3'', (TPrim Bool, Present)), (''field4'', (TRecord [(''field0'', (TPrim Bool, Present))] Unboxed, Present)), (''field5'', (TPrim Bool, Present)), (''field6'', (TPrim Bool, Present))] Unboxed"

definition
  abbreviatedType3 :: " Cogent.type"
where
  "abbreviatedType3 \<equiv> TRecord [(''field0'', (TPrim Bool, Present))] Unboxed"

definition
  abbreviatedType4 :: " Cogent.type"
where
  "abbreviatedType4 \<equiv> TRecord [(''field0'', (TRecord [(''field0'', (TRecord [(''field0'', (abbreviatedType3, Present))] Unboxed, Present)), (''field1'', (TPrim Bool, Present))] Unboxed, Present)), (''field1'', (TPrim Bool, Present))] Unboxed"

definition
  abbreviatedType5 :: " Cogent.type"
where
  "abbreviatedType5 \<equiv> TRecord [(''field0'', (TRecord [(''field0'', (abbreviatedType3, Present))] Unboxed, Present)), (''field1'', (TPrim Bool, Present))] Unboxed"

definition
  abbreviatedType6 :: " Cogent.type"
where
  "abbreviatedType6 \<equiv> TRecord [(''field0'', (abbreviatedType3, Present))] Unboxed"

definition
  abbreviatedType7 :: " Cogent.type"
where
  "abbreviatedType7 \<equiv> TRecord [(''field0'', (abbreviatedType3, Present)), (''field1'', (TRecord [(''field0'', (TPrim Bool, Present)), (''field1'', (TPrim Bool, Present)), (''field2'', (TPrim Bool, Present))] Unboxed, Present)), (''field2'', (TPrim Bool, Present))] Unboxed"

definition
  abbreviatedType8 :: " Cogent.type"
where
  "abbreviatedType8 \<equiv> TRecord [(''field0'', (TPrim Bool, Present)), (''field1'', (TPrim Bool, Present)), (''field2'', (TPrim Bool, Present))] Unboxed"

definition
  abbreviatedType9 :: " Cogent.type"
where
  "abbreviatedType9 \<equiv> TSum [(''Con0'', (TPrim Bool, Unchecked)), (''Con1'', (TPrim Bool, Unchecked))]"

definition
  abbreviatedType10 :: " Cogent.type"
where
  "abbreviatedType10 \<equiv> TRecord [(''field0'', (abbreviatedType9, Present)), (''field1'', (TRecord [(''field0'', (TRecord [(''field0'', (abbreviatedType3, Present)), (''field1'', (abbreviatedType8, Present)), (''field2'', (TPrim Bool, Present))] Unboxed, Present)), (''field1'', (TRecord [(''field0'', (TRecord [(''field0'', (abbreviatedType6, Present)), (''field1'', (TPrim Bool, Present))] Unboxed, Present)), (''field1'', (TPrim Bool, Present))] Unboxed, Present)), (''field2'', (TPrim Bool, Present)), (''field3'', (TPrim Bool, Present)), (''field4'', (abbreviatedType3, Present)), (''field5'', (TPrim Bool, Present)), (''field6'', (TPrim Bool, Present))] Unboxed, Present)), (''field2'', (TPrim Bool, Present))] (Boxed Writable undefined)"

definition
  abbreviatedType11 :: " Cogent.type"
where
  "abbreviatedType11 \<equiv> TRecord [(''field0'', (TRecord [(''field0'', (abbreviatedType3, Present)), (''field1'', (abbreviatedType8, Present)), (''field2'', (TPrim Bool, Present))] Unboxed, Present)), (''field1'', (TRecord [(''field0'', (TRecord [(''field0'', (abbreviatedType6, Present)), (''field1'', (TPrim Bool, Present))] Unboxed, Present)), (''field1'', (TPrim Bool, Present))] Unboxed, Present)), (''field2'', (TPrim Bool, Present)), (''field3'', (TPrim Bool, Present)), (''field4'', (abbreviatedType3, Present)), (''field5'', (TPrim Bool, Present)), (''field6'', (TPrim Bool, Present))] Unboxed"

definition
  abbreviatedType12 :: " Cogent.type"
where
  "abbreviatedType12 \<equiv> TRecord [(''field0'', (TRecord [(''field0'', (abbreviatedType6, Present)), (''field1'', (TPrim Bool, Present))] Unboxed, Present)), (''field1'', (TPrim Bool, Present))] Unboxed"

definition
  abbreviatedType13 :: " Cogent.type"
where
  "abbreviatedType13 \<equiv> TRecord [(''field0'', (abbreviatedType6, Present)), (''field1'', (TPrim Bool, Present))] Unboxed"

definition
  abbreviatedType14 :: " Cogent.type"
where
  "abbreviatedType14 \<equiv> TRecord [(''field0'', (abbreviatedType3, Present)), (''field1'', (abbreviatedType8, Present)), (''field2'', (TPrim Bool, Present))] Unboxed"

lemmas abbreviated_type_defs =
  abbreviatedType9_def
  abbreviatedType6_def
  abbreviatedType14_def
  abbreviatedType7_def
  abbreviatedType13_def
  abbreviatedType10_def
  abbreviatedType3_def
  abbreviatedType8_def
  abbreviatedType1_def
  abbreviatedType5_def
  abbreviatedType11_def
  abbreviatedType12_def
  abbreviatedType4_def
  abbreviatedType2_def

definition
  main_type :: " Cogent.kind list \<times>  Cogent.type \<times>  Cogent.type"
where
  "main_type \<equiv> ([], (TRecord [(''field0'', (abbreviatedType9, Present)), (''field1'', (TRecord [(''field0'', (abbreviatedType14, Present)), (''field1'', (TRecord [(''field0'', (abbreviatedType13, Present)), (''field1'', (TPrim Bool, Present))] Unboxed, Present)), (''field2'', (TPrim Bool, Present)), (''field3'', (TPrim Bool, Present)), (''field4'', (abbreviatedType3, Present)), (''field5'', (TPrim Bool, Present)), (''field6'', (TPrim Bool, Present))] Unboxed, Present)), (''field2'', (TPrim Bool, Present))] (Boxed Writable undefined), TRecord [(''field0'', (abbreviatedType9, Present)), (''field1'', (TRecord [(''field0'', (abbreviatedType14, Present)), (''field1'', (TRecord [(''field0'', (abbreviatedType13, Present)), (''field1'', (TPrim Bool, Present))] Unboxed, Present)), (''field2'', (TPrim Bool, Present)), (''field3'', (TPrim Bool, Present)), (''field4'', (abbreviatedType3, Present)), (''field5'', (TPrim Bool, Present)), (''field6'', (TPrim Bool, Present))] Unboxed, Present)), (''field2'', (TPrim Bool, Present))] (Boxed Writable undefined)))"

definition
  main :: "string Cogent.expr"
where
  "main \<equiv> Take (Var 0) 0 (Take (Var 1) 1 (Take (Var 1) 2 (Let (Put (Var 1) 0 (Var 4)) (Let (Put (Var 0) 1 (Var 3)) (Put (Var 0) 2 (Var 2))))))"

ML \<open>
val Cogent_functions = ["main"]
val Cogent_abstract_functions = []
\<close>

end
