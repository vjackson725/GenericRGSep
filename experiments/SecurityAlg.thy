theory SecurityAlg
  imports "../RGLogic"
begin

datatype level = Low | High

instantiation level :: order
begin

definition \<open>less_eq_level a b \<equiv> a = Low \<or> a = High \<and> b = High\<close>

lemma less_eq_level_simps[simp]:
  \<open>a \<le> High\<close>
  \<open>Low \<le> b\<close>
  \<open>High \<le> b \<longleftrightarrow> b = High\<close>
  \<open>a \<le> Low \<longleftrightarrow> a = Low\<close>
  unfolding less_eq_level_def
  using level.exhaust by blast+

definition \<open>less_level a b \<equiv> a = Low \<and> b = High\<close>

lemma less_level_simps[simp]:
  \<open>a < High \<longleftrightarrow> a = Low\<close>
  \<open>Low < b \<longleftrightarrow> b = High\<close>
  \<open>High < b \<longleftrightarrow> False\<close>
  \<open>a < Low \<longleftrightarrow> False\<close>
  unfolding less_level_def
  using level.exhaust by blast+

instance
  apply standard
     apply (case_tac x; case_tac y; force simp add: less_eq_level_def less_level_def)
    apply (case_tac x; force simp add: less_eq_level_def less_level_def)
   apply (force simp add: less_eq_level_def)
  apply (force simp add: less_eq_level_def)
  done

end

instance level :: linorder
  by standard (metis less_eq_level_def level.exhaust)

instantiation level :: order_top
begin
definition \<open>top_level \<equiv> High\<close>
instance by standard (simp add: less_eq_level_def top_level_def, metis level.exhaust)
end

instantiation level :: order_bot
begin
definition \<open>bot_level \<equiv> Low\<close>
instance by standard (simp add: less_eq_level_def bot_level_def)
end

instantiation level :: semilattice_inf
begin

definition \<open>inf_level a b \<equiv> case a of Low \<Rightarrow> Low | High \<Rightarrow> b\<close>

lemma inf_level_simps[simp]:
  \<open>High \<sqinter> b = b\<close>
  \<open>a \<sqinter> High = a\<close>
  \<open>Low \<sqinter> b = Low\<close>
  \<open>a \<sqinter> Low = Low\<close>
  by (simp add: inf_level_def split: level.splits)+

instance by standard (case_tac x; case_tac y; force)+

end

instantiation level :: semilattice_sup
begin

definition \<open>sup_level a b \<equiv> case a of High \<Rightarrow> High | Low \<Rightarrow> b\<close>

lemma sup_level_simps[simp]:
  \<open>High \<squnion> b = High\<close>
  \<open>a \<squnion> High = High\<close>
  \<open>Low \<squnion> b = b\<close>
  \<open>a \<squnion> Low = a\<close>
  by (simp add: sup_level_def split: level.splits)+

instance by standard (case_tac x; case_tac y; force)+

end

instance level :: lattice by standard

instance level :: distrib_lattice
  by standard (case_tac x; simp)

instantiation level :: boolean_algebra
begin

definition \<open>uminus_level a \<equiv> case a of Low \<Rightarrow> High | High \<Rightarrow> Low\<close>
definition \<open>minus_level (a::level) b \<equiv> a \<sqinter> - b\<close>

instance
  by standard
    (simp add: uminus_level_def bot_level_def top_level_def minus_level_def split: level.splits)+

end  



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

type_synonym 'a sec_rel = \<open>'a sec_st \<Rightarrow> bool\<close>

definition level_eval
  :: \<open>('a \<Rightarrow> 'v) \<Rightarrow> ('a \<Rightarrow> 'l::order) \<Rightarrow> ('l \<Rightarrow> 'a sec_rel)\<close>
  (\<open>_ \<triangleleft> _\<close> [55,55] 55)
  where
  \<open>e \<triangleleft> l' \<equiv> \<lambda>l (s, s').
    l' s \<le> l \<longrightarrow> l' s' \<le> l \<longrightarrow> e s = e s'\<close>

definition sec_points_to
  :: \<open>'a \<Rightarrow> 'b \<Rightarrow> ('a \<rightharpoonup> 'b) sec_rel\<close>
  (infix \<open>\<^bold>\<mapsto>\<^sub>s\<close> 90)
  where
  \<open>p \<^bold>\<mapsto>\<^sub>s v \<equiv> \<T> (p \<^bold>\<mapsto> v)\<close>

(* Low(e,e') in the paper.
    The paper produces \<open>emp\<close> when it's successful; we cannot, as our local store and heap are mixed.
    Thus, we must say \<open>lowe e e' \<and> ...\<close>
*)
definition lowe
  :: \<open>('st::perm_alg \<Rightarrow> 'v) \<Rightarrow> ('st \<Rightarrow> 'v) \<Rightarrow> 'st sec_rel\<close>
  where
  \<open>lowe e e' \<equiv> \<lambda>(sl, sh). (if e sl = e' sl then \<top> else \<bottom>)\<close>

lemma eq_rel_Times_eq_conv[simp]: \<open>((=) \<times>\<^sub>R (=)) = (=)\<close>
  unfolding rel_Times_def
  by blast

lemma post_state_un_eq[simp]:
  \<open>post_state (\<lambda>a b. p a b \<or> q a b) = post_state p \<squnion> post_state q\<close>
  by (force simp add: post_state_def fun_eq_iff)

lemma pre_state_un_eq[simp]:
  \<open>pre_state (\<lambda>a b. p a b \<or> q a b) = pre_state p \<squnion> pre_state q\<close>
  by (force simp add: pre_state_def fun_eq_iff)

lemma
  \<open>(=), (=) \<turnstile> { \<L> ((p \<triangleleft> l) l') } Assert (\<L> (p \<times>\<^sub>P \<top>)) { \<top> }\<close>
  unfolding Assert_def
  by (rule rgsat_atom) (force simp add: sp_def)+

end