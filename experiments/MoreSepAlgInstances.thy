theory MoreSepAlgInstances
  imports "../SepAlgInstances"
begin

class bounded_distrib_lattice = distrib_lattice + bounded_lattice

context boolean_algebra
begin
subclass bounded_distrib_lattice
  by standard
end


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


section \<open> lock permissions #2 \<close>

text \<open>
  Krebber's (TODO cite) `lockable' permission structure.
\<close>

typedef ('a::bounded_distrib_lattice) lock_perm = \<open>UNIV :: 'a set\<close>
  by blast

definition \<open>Top \<equiv> Abs_lock_perm \<bottom>\<close>
definition \<open>Bot \<equiv> Abs_lock_perm \<top>\<close>

declare Abs_lock_perm_inject[simplified, simp]
declare Abs_lock_perm_inverse[simplified, simp]
declare Rep_lock_perm_inverse[simplified, simp]

lemmas Rep_lock_perm_inject2 = Rep_lock_perm_inject[simplified]

lemma Abs_lock_perm_helpers:
  \<open>(a = Abs_lock_perm x) \<longleftrightarrow> x = Rep_lock_perm a\<close>
  \<open>(Abs_lock_perm x = a) \<longleftrightarrow> x = Rep_lock_perm a\<close>
  using Abs_lock_perm_inverse Rep_lock_perm_inject2
  by force+

setup_lifting type_definition_lock_perm

instantiation lock_perm :: (bounded_distrib_lattice) perm_alg
begin

lift_definition less_eq_lock_perm :: \<open>'a lock_perm \<Rightarrow> 'a lock_perm \<Rightarrow> bool\<close> is
  \<open>\<lambda>a b. a = b \<or> (\<exists>c. a \<squnion> c = \<top> \<and> b = a \<sqinter> c)\<close> .

lift_definition less_lock_perm :: \<open>'a lock_perm \<Rightarrow> 'a lock_perm \<Rightarrow> bool\<close> is
  \<open>\<lambda>a b. a \<noteq> b \<and> (\<exists>c. a \<squnion> c = \<top> \<and> b = a \<sqinter> c)\<close> .

lift_definition disjoint_lock_perm :: \<open>'a lock_perm \<Rightarrow> 'a lock_perm \<Rightarrow> bool\<close> is
  \<open>\<lambda>a b. a \<squnion> b = \<top>\<close> .


lemma disjoint_lock_perm_simps[simp]:
  \<open>Top ## b \<longleftrightarrow> b = Bot\<close>
  \<open>a ## Top \<longleftrightarrow> a = Bot\<close>
  \<open>Top ## Top \<longleftrightarrow> (\<bottom>::'a) = \<top>\<close>
  by (force simp add: disjoint_lock_perm.rep_eq Top_def Bot_def Abs_lock_perm_helpers)+

lift_definition plus_lock_perm :: \<open>'a lock_perm \<Rightarrow> 'a lock_perm \<Rightarrow> 'a lock_perm\<close> is \<open>(\<sqinter>)\<close> .

lemma plus_lock_perm_simps[simp]:
  \<open>Top + Bot = Top\<close>
  \<open>Bot + Top = Top\<close>
  \<open>Bot + Bot = Bot\<close>
  unfolding Bot_def Top_def
  by (transfer, force)+

instance
  apply standard
       apply (transfer, metis inf.assoc)
      apply (transfer, metis inf.commute)
     apply (transfer, metis sup.commute)
    apply (transfer, simp add: sup_inf_distrib1; fail)
   apply (transfer, simp add: inf_sup_aci(5) sup_inf_distrib1; fail)
  subgoal sorry
  done

end

end