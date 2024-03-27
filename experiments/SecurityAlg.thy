theory SecurityAlg
  imports SepAlgInstances
begin

definition tuple_lift :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'a \<Rightarrow> bool)\<close> (\<open>\<T>\<close>) where
  \<open>\<T> p \<equiv> \<lambda>(x,y). p x \<and> p y\<close>

lemma tuple_lift_conj[simp]: \<open>\<T> (p \<sqinter> q) = \<T> p \<sqinter> \<T> q\<close>
  by (force simp add: tuple_lift_def fun_eq_iff)

lemma tuple_lift_disj_weak:
  \<open>\<T> p \<le> \<T> (p \<squnion> q)\<close>
  \<open>\<T> q \<le> \<T> (p \<squnion> q)\<close>
  by (force simp add: tuple_lift_def fun_eq_iff)+

lemma tuple_lift_top[simp]: \<open>\<T> \<top> = \<top>\<close>
  by (force simp add: tuple_lift_def fun_eq_iff)

lemma tuple_lift_bot[simp]: \<open>\<T> \<bottom> = \<bottom>\<close>
  by (force simp add: tuple_lift_def fun_eq_iff)

lemma tuple_lift_sepconj[simp]: \<open>\<T> (p \<^emph> q) = \<T> p \<^emph> \<T> q\<close>
  by (force simp add: tuple_lift_def fun_eq_iff sepconj_def)


section \<open> SecRel \<close>

type_synonym 'a sec_st = \<open>'a \<times> 'a\<close>

type_synonym ('l, 'a) sec_rel = \<open>'l \<Rightarrow> 'a sec_st \<Rightarrow> bool\<close>

definition level_eval
  :: \<open>('a \<Rightarrow> 'v) \<Rightarrow> ('a \<Rightarrow> 'l::order) \<Rightarrow> ('l \<Rightarrow> 'a \<times> 'a \<Rightarrow> bool)\<close>
  (\<open>_ \<triangleleft> _\<close> [55,55] 55)
  where
  \<open>e \<triangleleft> el \<equiv> \<lambda>l (low, high).
    el low = el high \<and>
    (el low \<le> l \<longrightarrow> e high = e low)\<close>

definition level_points_to
  :: \<open>(('p \<rightharpoonup> 'v) \<Rightarrow> 'p) \<Rightarrow> (('p \<rightharpoonup> 'v) \<Rightarrow> 'l::order) \<Rightarrow> (('p \<rightharpoonup> 'v) \<Rightarrow> 'v) \<Rightarrow> ('l, 'p \<rightharpoonup> 'v) sec_rel\<close>
  (\<open>_ \<^bold>\<mapsto>\<^bsub>_\<^esub> _\<close> [55,0,55] 55)
  where
  \<open>ep \<^bold>\<mapsto>\<^bsub>el\<^esub> ev \<equiv> \<lambda>l (low::('p \<rightharpoonup> 'v), high::('p \<rightharpoonup> 'v)).
    (ep low \<^bold>\<mapsto> ev low) low \<and>
    (ep high \<^bold>\<mapsto> ev high) high \<and>
    (ep \<triangleleft> el) l (low, high) \<and>
    (ev \<triangleleft> el) l (low, high)\<close>

end