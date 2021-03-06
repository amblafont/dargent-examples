(*
This file is generated by Cogent

*)

theory Ex1_dargentisa_ShallowShared_Tuples
imports "Cogent.Util"
"CogentShallow.ShallowUtil"
begin

record ('a, 'b) T0 =
  field0\<^sub>f :: "'a"
  field1\<^sub>f :: "'b"

record 'a T1 =
  field0\<^sub>f :: "'a"

record ('a, 'b, 'c, 'd, 'e, 'f, 'g) T2 =
  field0\<^sub>f :: "'a"
  field1\<^sub>f :: "'b"
  field2\<^sub>f :: "'c"
  field3\<^sub>f :: "'d"
  field4\<^sub>f :: "'e"
  field5\<^sub>f :: "'f"
  field6\<^sub>f :: "'g"

datatype ('a, 'b) T3 =
  Con0 "'a"|
  Con1 "'b"

record ('a, 'b, 'c) Ex =
  field0\<^sub>f :: "'a"
  field1\<^sub>f :: "'b"
  field2\<^sub>f :: "'c"

type_synonym  Ex\<^sub>T = "((bool, bool) T3, ((bool T1, (bool, bool, bool) Ex, bool) Ex, ((bool T1 T1, bool) T0, bool) T0, bool, bool, bool T1, bool, bool) T2, bool) Ex"

end
