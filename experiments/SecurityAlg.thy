theory SecurityAlg
  imports "../RGLogic"
begin

section \<open> Low/High Levels \<close>

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

section \<open> Location heaps \<close>

lemma dom_comp[simp]: \<open>dom (g \<circ>\<^sub>m f) = {a. \<exists>b. f a = Some b \<and> b \<in> dom g}\<close>
  by (force simp add: map_comp_def dom_def split: option.splits)

text \<open>
  For security applications, we need not just the data to be splittable, but also
  the \<^emph>\<open>locations\<close> of the heap. Being able to observe a location's existence can give
  security-relevant information, even without access to its data.
    Thus, we split the information that a location exists and a location's data into
  separate resources.
\<close>

typedef ('a,'b) locheap (infixr \<open>\<rightharpoonup>\<^sub>l\<close> 0) =
  \<open>{(L::'a set, h :: 'a \<rightharpoonup> 'b). dom h \<le> L}\<close>
  by blast

setup_lifting type_definition_locheap

setup \<open>Sign.mandatory_path "locheap"\<close>

lift_definition empty :: \<open>'a \<rightharpoonup>\<^sub>l 'b\<close> is \<open>({}, Map.empty)\<close>
  by force

lift_definition comp :: "('b \<rightharpoonup>\<^sub>l 'c) \<Rightarrow> ('a \<rightharpoonup>\<^sub>l 'b) \<Rightarrow> ('a \<rightharpoonup>\<^sub>l 'c)" (infixl "\<circ>\<^sub>l" 55) is
  \<open>\<lambda>(B::'b set, g::'b \<rightharpoonup> 'c) (A::'a set, f::'a \<rightharpoonup> 'b). ({a. \<exists>b. f a = Some b \<and> b \<in> dom g}, g \<circ>\<^sub>m f)\<close>
  by (simp split: prod.splits)

lift_definition restrict :: "('a \<rightharpoonup>\<^sub>l 'b) \<Rightarrow> 'a set \<Rightarrow> ('a \<rightharpoonup>\<^sub>l 'b)" (infixl \<open>|`\<^sub>l\<close> 110) is
  \<open>\<lambda>(A, m) B. (A \<inter> B, m |` B)\<close>
  by (auto split: prod.splits)

lift_definition dom :: "('a \<rightharpoonup>\<^sub>l 'b) \<Rightarrow> 'a set" is fst .
lift_definition precise_dom :: "('a \<rightharpoonup>\<^sub>l 'b) \<Rightarrow> 'a set" is \<open>dom \<circ> snd\<close> .

lift_definition less_eq :: \<open>('a \<rightharpoonup>\<^sub>l 'b) \<Rightarrow> ('a \<rightharpoonup>\<^sub>l 'b) \<Rightarrow> bool\<close> (infix \<open>\<subseteq>\<^sub>l\<close> 50) is
  \<open>\<lambda>(A,a) (B,b). A \<subseteq> B \<and> a \<subseteq>\<^sub>m b\<close> .

lemma less_eq_trans[trans]:
  \<open>a \<subseteq>\<^sub>l b \<Longrightarrow> b \<subseteq>\<^sub>l c \<Longrightarrow> a \<subseteq>\<^sub>l c\<close>
  by (transfer, force simp add: map_le_def dom_def split: prod.splits)

lemma less_eq_refl[iff]:
  \<open>a \<subseteq>\<^sub>l a\<close>
  by (transfer, simp split: prod.splits)

lemma less_eq_antisym:
  \<open>a \<subseteq>\<^sub>l b \<Longrightarrow> b \<subseteq>\<^sub>l a \<Longrightarrow> a = b\<close>
  by (transfer,
      clarsimp simp add: map_le_def dom_def fun_eq_iff split: prod.splits,
      metis not_Some_eq)

setup \<open>Sign.parent_path\<close>

instantiation locheap :: (type, type) plus
begin
lift_definition plus_locheap :: \<open>('a \<rightharpoonup>\<^sub>l 'b) \<Rightarrow> ('a \<rightharpoonup>\<^sub>l 'b) \<Rightarrow> 'a \<rightharpoonup>\<^sub>l 'b\<close> is
  \<open>\<lambda>(D1, m1) (D2, m2). (D1 \<union> D2, m1 ++ m2)\<close>
  by force
instance by standard
end

instantiation locheap :: (type, perm_alg) perm_alg
begin

lift_definition disjoint_locheap :: \<open>('a \<rightharpoonup>\<^sub>l 'b) \<Rightarrow> ('a \<rightharpoonup>\<^sub>l 'b) \<Rightarrow> bool\<close> is
  \<open>\<lambda>(D1, m1) (D2, m2). D1 \<inter> D2 = {}\<close> .

instance
  apply standard
       apply (transfer, force)
      apply (transfer, simp split: prod.splits)
      apply (metis inf_mono inf_sup_aci(5) map_add_comm order_bot_class.bot.extremum_uniqueI)
     apply (transfer, force)
    apply (transfer, fastforce)
   apply (transfer, fastforce)
  apply (transfer, clarsimp split: prod.splits)
  apply (metis Un_Int_assoc_eq Un_Int_eq(1) Un_Int_eq(3) empty_iff map_add_subsumed2 map_le_def sup_bot_left)
  done

end

instantiation locheap :: (type, perm_alg) multiunit_sep_alg
begin
lift_definition unitof_locheap :: \<open>('a \<rightharpoonup>\<^sub>l 'b) \<Rightarrow> ('a \<rightharpoonup>\<^sub>l 'b)\<close> is
  \<open>\<lambda>_. ({}, Map.empty)\<close>
  by (simp split: prod.splits)
instance by standard (transfer, force)+
end

instantiation locheap :: (type, perm_alg) sep_alg
begin

lift_definition zero_locheap :: \<open>('a \<rightharpoonup>\<^sub>l 'b)\<close> is
  \<open>({}, Map.empty)\<close>
  by (simp split: prod.splits)

lift_definition bot_locheap :: \<open>('a \<rightharpoonup>\<^sub>l 'b)\<close> is
  \<open>({}, Map.empty)\<close>
  by (simp split: prod.splits)

instance
  apply standard
   apply (simp add: less_eq_sepadd_def', transfer, force)
  apply (transfer, force)
  done

end


section \<open> Security Logic \<close>

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