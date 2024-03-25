theory SepAlgInstancesExperimental
  imports "../SepAlgInstances"
begin


section \<open> Locked resources \<close>

(* This doesn't work. *)

(* TODO: this might be better as a datatype. *)
type_synonym 'a locked = \<open>munit + 'a\<close>

abbreviation(input) \<open>Locked \<equiv> Inl \<one> :: 'a locked\<close>
abbreviation(input) \<open>Unlocked x \<equiv> Inr x :: 'a locked\<close>

lemma disjoint_locked_simps[simp]:
  \<open>\<And>b. Locked ## b \<longleftrightarrow> False\<close>
  \<open>\<And>a. a ## Locked \<longleftrightarrow> False\<close>
  \<open>\<And>a b. Unlocked a ## Unlocked b \<longleftrightarrow> a ## b\<close>
    apply (case_tac b; simp)
   apply (case_tac a; simp)
  apply simp
  done

type_synonym 'a resources = \<open>nat \<rightharpoonup> 'a locked\<close>




end