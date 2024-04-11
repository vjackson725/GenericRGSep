theory SecurityAlg
  imports "../SepAlgInstances"
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
  :: \<open>('a \<Rightarrow> 'v) \<Rightarrow> ('a \<Rightarrow> 'l::order) \<Rightarrow> ('l,'a) sec_rel\<close>
  (\<open>_ \<triangleleft> _\<close> [55,55] 55)
  where
  \<open>e \<triangleleft> l' \<equiv> \<lambda>l (s, s').
    l' s \<le> l \<longrightarrow> l' s' \<le> l \<longrightarrow> e s = e s'\<close>

definition sec_points_to
  :: \<open>'a \<Rightarrow> 'b \<Rightarrow> ('l, 'a \<rightharpoonup> 'b) sec_rel\<close>
  (infix \<open>\<^bold>\<mapsto>\<^sub>s\<close> 90)
  where
  \<open>p \<^bold>\<mapsto>\<^sub>s v \<equiv> \<lambda>l. \<T> (p \<^bold>\<mapsto> v)\<close>

end