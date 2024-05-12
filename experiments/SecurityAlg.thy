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

subsection \<open> (weak/permissive) leq \<close>

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

subsection \<open> strong leq \<close>

lift_definition strong_less_eq :: \<open>('a \<rightharpoonup>\<^sub>l 'b) \<Rightarrow> ('a \<rightharpoonup>\<^sub>l 'b) \<Rightarrow> bool\<close> (infix \<open>\<sqsubseteq>\<^sub>l\<close> 50) is
  \<open>\<lambda>(A,a) (B,b). A = B \<and> a \<subseteq>\<^sub>m b\<close> .

lemma strong_less_eq_trans[trans]:
  \<open>a \<sqsubseteq>\<^sub>l b \<Longrightarrow> b \<sqsubseteq>\<^sub>l c \<Longrightarrow> a \<sqsubseteq>\<^sub>l c\<close>
  by (transfer, force simp add: map_le_def dom_def split: prod.splits)

lemma strong_less_eq_refl[iff]:
  \<open>a \<sqsubseteq>\<^sub>l a\<close>
  by (transfer, simp split: prod.splits)

lemma strong_less_eq_antisym:
  \<open>a \<sqsubseteq>\<^sub>l b \<Longrightarrow> b \<sqsubseteq>\<^sub>l a \<Longrightarrow> a = b\<close>
  by (transfer,
      clarsimp simp add: map_le_def dom_def fun_eq_iff split: prod.splits,
      metis not_Some_eq)

lemma strong_less_eq_impl_less_eq[dest]:
  \<open>a \<sqsubseteq>\<^sub>l b \<Longrightarrow> a \<subseteq>\<^sub>l b\<close>
  by (transfer, simp split: prod.splits)

subsection \<open> Locheap completion \<close>

lift_definition embed :: \<open>('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup>\<^sub>l 'b)\<close> is
  \<open>\<lambda>h. (dom h, h)\<close>
  by simp

abbreviation completion :: \<open>('a \<rightharpoonup>\<^sub>l 'b) \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> bool\<close> (infix \<open>\<sqsubseteq>\<^sub>c\<close> 50) where
  \<open>lh \<sqsubseteq>\<^sub>c h \<equiv> lh \<sqsubseteq>\<^sub>l locheap.embed h\<close>

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
    The paper produces \<open>emp\<close> when it's successful; we cannot, as we have a unitary resource model.
    Thus, we must say \<open>lowe e e' \<and> ...\<close>.
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
  \<open>(=), (=) \<turnstile> { \<L> ((p \<triangleleft> l) l') } Guard (\<L> (\<T> p)) { \<L> (\<T> p) }\<close>
  unfolding Guard_def
  apply (rule rgsat_atom)
      apply (force simp add: sp_def)
     apply (force simp add: sp_def)
    apply (clarsimp simp add: sp_def)
  oops

(* FIXME: We convert pp into  partial equivalence relation, which might not be what we want to do. *)
definition lift_T_to_H :: \<open>('a \<times> 'a \<Rightarrow> bool) \<Rightarrow> (('a \<Rightarrow> bool) \<Rightarrow> bool)\<close> where
  \<open>lift_T_to_H pp \<equiv> \<lambda>p. \<forall>x y. p x \<longrightarrow> tranclp (curry pp \<squnion> (curry pp)\<inverse>\<inverse>) x y \<longrightarrow> p y\<close>

lemma \<open>r x y \<or> r y x \<Longrightarrow> tranclp (symclp r) x x\<close>
  by (metis symclpI1 symclpI2 tranclp.simps)


type_synonym 'a prog = \<open>'a \<Rightarrow> 'a set set\<close>

definition less_eq_smyth :: \<open>('a::order) set \<Rightarrow> 'a set \<Rightarrow> bool\<close> (infix \<open>\<le>\<^sub>S\<close> 50) where
  \<open>A \<le>\<^sub>S B \<equiv> \<forall>b\<in>B. \<exists>a\<in>A. a \<le> b\<close>

lemma smyth_supcl_greater[intro]:
  fixes A B :: \<open>('a::complete_lattice) set\<close>
  shows \<open>A \<le>\<^sub>S supcl A\<close>
  by (clarsimp simp add: supcl_def less_eq_smyth_def)
    (meson Sup_upper order.trans all_not_in_conv subset_iff)

lemma smyth_supcl_lesser[intro]:
  fixes A B :: \<open>('a::complete_lattice) set\<close>
  shows \<open>supcl A \<le>\<^sub>S A\<close>
  by (clarsimp simp add: supcl_def less_eq_smyth_def)
    (metis Sup_upper ccpo_Sup_singleton empty_iff insert_subset singletonI sup.order_iff
      sup_bot.right_neutral)

lemma smyth_supcl_closedR:
  fixes A B :: \<open>('a::complete_lattice) set\<close>
  shows \<open>A \<le>\<^sub>S B \<Longrightarrow> A \<le>\<^sub>S supcl B\<close>
  by (clarsimp simp add: supcl_def less_eq_smyth_def)
    (meson Sup_upper order.trans all_not_in_conv subset_iff)

lemma smyth_supcl_closedL:
  fixes A B :: \<open>('a::complete_lattice) set\<close>
  shows \<open>supcl A \<le>\<^sub>S B \<Longrightarrow> A \<le>\<^sub>S B\<close>
  by (clarsimp simp add: supcl_def less_eq_smyth_def)
    (metis Sup_upper order.trans all_not_in_conv subset_iff)

definition less_eq_hoare :: \<open>('a::order) set \<Rightarrow> 'a set \<Rightarrow> bool\<close> (infix \<open>\<le>\<^sub>H\<close> 50) where
  \<open>A \<le>\<^sub>H B \<equiv> \<forall>a\<in>A. \<exists>b\<in>B. a \<le> b\<close>

abbreviation less_eq_plotkin :: \<open>('a::order) set \<Rightarrow> 'a set \<Rightarrow> bool\<close> (infix \<open>\<le>\<^sub>P\<close> 50) where
  \<open>A \<le>\<^sub>P B \<equiv> A \<le>\<^sub>S B \<and> A \<le>\<^sub>H B\<close>

abbreviation refinement :: \<open>'a prog \<Rightarrow> 'a prog \<Rightarrow> bool\<close> (infix \<open>\<sqsubseteq>\<close> 50) where
  \<open>S \<sqsubseteq> I \<equiv> \<forall>x. S x \<le>\<^sub>S I x\<close>

lemma union_closure:
  \<open>\<forall>x. \<forall>h HI. HI \<in> I' x \<longrightarrow> (\<exists>\<HH>. \<HH> \<noteq> {} \<and> HI = \<Union>\<HH> \<and> (\<forall>H\<in>\<HH>. H \<in> I x)) \<Longrightarrow>
    \<forall>x. I x \<subseteq> I' x \<Longrightarrow>
    I \<sqsubseteq> I' \<and> I' \<sqsubseteq> I\<close>
  apply (clarsimp simp add: less_eq_smyth_def Ball_def split: prod.splits)
  apply (intro conjI impI allI)
   apply blast
  apply fast
  done

lemma union_closure2:
  \<open>I \<sqsubseteq> supcl \<circ> I \<and> supcl \<circ> I \<sqsubseteq> I\<close>
  by (clarsimp simp add: Ball_def smyth_supcl_greater smyth_supcl_lesser split: prod.splits)

lemma
  fixes PP :: \<open>('a \<times> 'a set) set\<close>
  assumes refl_cl: \<open>\<And>h H. (h, H) \<in> PP \<Longrightarrow> h \<in> H\<close>
  assumes sym_cl: \<open>\<And>h h' H. (h, H) \<in> PP \<Longrightarrow> h' \<in> H \<Longrightarrow> (h', H) \<in> PP\<close>
  shows \<open>PP = {(h,H)|h H u. (u,H) \<in> PP \<and> h \<in> H}\<close>
  apply (simp add: set_eq_iff)
  using refl_cl sym_cl by blast

definition \<open>healthy p \<equiv> (\<forall>x y. p (x,y) \<longrightarrow> p (x,x)) \<and> (\<forall>x y. p (x,y) \<longrightarrow> p (y,x))\<close>

lemma \<open>healthy ((e \<triangleleft> l') l)\<close>
  by (simp add: healthy_def level_eval_def)

definition level_eval_H
  :: \<open>('a \<Rightarrow> 'v) \<Rightarrow> ('a \<Rightarrow> 'l::order) \<Rightarrow> ('l \<Rightarrow> 'a set set)\<close> (\<open>_ \<triangleleft>\<^sub>\<H> _\<close> [55,55] 55)
  where
  \<open>e \<triangleleft>\<^sub>\<H> l' \<equiv> \<lambda>l. ({A. \<exists>s. A = {s'. l' s \<le> l \<longrightarrow> l' s' \<le> l \<longrightarrow> e s = e s'}})\<close>

definition \<open>uncertainty p s \<equiv> {s'. p (s,s')}\<close>

lemma hyperset_level_eval_eq:
  \<open>{uncertainty ((e \<triangleleft> l') l) s|s. True} =
      {A. \<exists>s. A = {s'. l' s \<le> l \<longrightarrow> l' s' \<le> l \<longrightarrow> e s = e s'}}\<close>
  by transfer
    (clarsimp simp add: level_eval_def level_eval_H_def uncertainty_def)

lemma \<open>((e \<triangleleft>\<^sub>\<H> l') l) \<le>\<^sub>S {uncertainty ((e \<triangleleft> l') l) s|s. True}\<close>
(*
  by transfer
    (force simp add: level_eval_def level_eval_H_def uncertainty_def)
*)
  sorry

lemma \<open>{uncertainty ((e \<triangleleft> l') l) s|s. True} \<le>\<^sub>S ((e \<triangleleft>\<^sub>\<H> l') l)\<close>
(*
  by transfer
    (force simp add: level_eval_def level_eval_H_def uncertainty_def)
*)
  sorry

abbreviation \<open>equiv_class_by f \<equiv> \<lambda>x. {y. f x = f y}\<close>

abbreviation \<open>equiv_classes_by f \<equiv> range (equiv_class_by f)\<close>


abbreviation inf_Times :: \<open>('a::inf) set \<Rightarrow> 'a set \<Rightarrow> 'a set\<close> (infixr \<open>\<times>\<sqinter>\<times>\<close> 90) where
  \<open>A \<times>\<sqinter>\<times> B \<equiv> case_prod (\<sqinter>) ` (A \<times> B)\<close>

abbreviation sup_Times :: \<open>('a::sup) set \<Rightarrow> 'a set \<Rightarrow> 'a set\<close> (infixr \<open>\<times>\<squnion>\<times>\<close> 85) where
  \<open>A \<times>\<squnion>\<times> B \<equiv> case_prod (\<squnion>) ` (A \<times> B)\<close>

abbreviation implies_Times :: \<open>('a::boolean_algebra) set \<Rightarrow> 'a set \<Rightarrow> 'a set\<close> (infixr \<open>\<times>\<leadsto>\<times>\<close> 80) where
  \<open>A \<times>\<leadsto>\<times> B \<equiv> case_prod (\<leadsto>) ` (A \<times> B)\<close>

definition
  \<open>equiv_rel_to_equiv_classes r \<equiv>
    {A. (\<exists>x y. (x,y) \<in> r \<and> x \<in> A \<and> y \<in> A) \<and>
          (\<forall>x y. x \<in> A \<longrightarrow> (x,y) \<in> r \<longrightarrow> y \<in> A)}\<close>

lemma
  fixes l' :: \<open>'s \<Rightarrow> 'l::ord\<close>
  fixes e :: \<open>'s \<Rightarrow> 'v\<close>
  shows \<open>{y. \<exists>x. l' x \<le> l \<and> y = {s'. l' s' \<le> l \<longrightarrow> e x = e s'}} = Z\<close>
proof -
  have \<open>
    {y. \<exists>x. l' x \<le> l \<and> y = {s'. l' s' \<le> l \<longrightarrow> e x = e s'}} =
    {y. \<exists>x. l' x \<le> l \<and> y = ({s'. \<not> l' s' \<le> l} \<union>
                              (equiv_class_by e x \<inter> {s'. l' s' \<le> l}))}
  \<close>
    by (simp add: Un_def)
  have \<open>... =
    ((\<union>) {s'. \<not> l' s' \<le> l} \<circ> equiv_class_by e) ` {s. l' s \<le> l}
  \<close>
    by (clarsimp simp add: set_eq_iff image_def)
  show ?thesis
    sorry
qed

lemma equiv_class_image_eq:
  \<open>equiv_class_by e ` A =
    (Set.filter ((\<noteq>) {} \<circ> (\<inter>) A) (equiv_classes_by e))\<close>
  by (force simp add: image_def Set.filter_def)

definition
  \<open>scott_continuous f A \<equiv> f (\<Squnion> A) = \<Squnion> (f ` A)\<close>

lemma Un_contains_eq:
  fixes A :: \<open>'a set\<close>
  shows \<open>A \<in> \<AA> \<Longrightarrow> \<Union> ((\<union>) A ` \<AA>) = \<Union> \<AA>\<close>
  by (drule mk_disjoint_insert, clarsimp)

lemma Sup_contains_eq:
  fixes a :: \<open>'a :: complete_boolean_algebra\<close>
  shows \<open>a \<in> A \<Longrightarrow> \<Squnion> ((\<squnion>) a ` A) = \<Squnion> A\<close>
  apply (drule mk_disjoint_insert)
  apply clarsimp
  apply (simp add: Sup_insert[symmetric] image_def del: Sup_insert)
  oops

lemma un_Un_eq_Un_un_every:
  fixes a :: \<open>'a set\<close>
  shows \<open>A \<noteq> {} \<Longrightarrow> a \<squnion> \<Squnion> A = \<Squnion> ((\<squnion>) a ` A)\<close>
  by blast

lemma sup_Sup_eq_Sup_sup_every:
  fixes a :: \<open>'a :: complete_boolean_algebra\<close>
  shows \<open>A \<noteq> {} \<Longrightarrow> a \<squnion> \<Squnion> A = \<Squnion> ((\<squnion>) a ` A)\<close>
  oops

lemma
  fixes a :: \<open>'a set\<close>
  shows \<open>supcl ((\<squnion>) a ` B) = (\<squnion>) a ` supcl B\<close>
  apply (rule antisym)
   apply (clarsimp simp add: supcl_def image_def subset_iff
      Ball_def[symmetric] Bex_def)
   apply (drule bchoice)
   apply (clarsimp simp add: Ball_def subset_iff[symmetric])
   apply (subgoal_tac \<open>A' \<subseteq> f -` B\<close>)
    prefer 2
    apply blast
  sorry

lemma
  \<open>supcl ({A. \<exists>s. A = {s'. l' s \<le> l \<longrightarrow> l' s' \<le> l \<longrightarrow> e s = e s'}}) =
    insert UNIV (
      supcl (((\<union>) {s'. \<not> l' s' \<le> l} \<circ> equiv_class_by e) ` {s. l' s \<le> l})
    )\<close> (is \<open>?lhs = _\<close>)
proof -
  have helper: \<open>\<And>\<AA>. UNIV \<in> supcl \<AA> \<longleftrightarrow> (\<forall>x. \<exists>A'\<in>\<AA>. x \<in> A')\<close>
    apply (simp add: supcl_def)
    apply (metis Sup_subset_mono UNIV_eq_I Union_iff emptyE iso_tuple_UNIV_I order_refl top.extremum_unique)
    done

  have helper2:
    \<open>\<forall>x. \<exists>A'\<in>equiv_classes_by e. x \<in> A'\<close>
    by auto

  have \<open>?lhs = {\<Union>A'|A'. A' \<noteq> {} \<and> A' \<subseteq> (\<lambda>s. {s'. l' s \<le> l \<longrightarrow> l' s' \<le> l \<longrightarrow> e s = e s'}) ` UNIV}\<close>
    by (simp add: supcl_def Union_eq Bex_def, fast)
  also have \<open>... = {\<Union> A' |A'. A' \<noteq> {} \<and> A' \<subseteq> (\<lambda>s. {s'. \<not> l' s \<le> l} \<union> {s'. \<not> l' s' \<le> l} \<union> {s'. e s = e s'}) ` UNIV}\<close>
    by (simp add: Un_def del: Collect_const)
  also have \<open>... = {\<Union> A' |A'. A' \<noteq> {} \<and> A' \<subseteq> (if \<forall>x. l' x \<le> l then {} else {UNIV}) \<union> (\<lambda>x. {s'. \<not> l' s' \<le> l} \<union> {s'. e x = e s'}) ` {x. l' x \<le> l}}\<close>
    by (simp add: if_distrib[where f=\<open>\<lambda>x. x \<union> _\<close>] image_constant_conv)
  also have \<open>... =
      {\<Union> A' |A'. A' \<noteq> {} \<and> (\<forall>x. l' x \<le> l) \<and> A' \<subseteq> range (\<lambda>x. {s'. l' s' \<le> l \<longrightarrow> e x = e s'})} \<union>
      {\<Union> A' |A'. A' \<noteq> {} \<and> (\<exists>x. \<not> l' x \<le> l) \<and> A' \<subseteq> insert UNIV ((\<lambda>x. {s'. l' s' \<le> l \<longrightarrow> e x = e s'}) ` {x. l' x \<le> l})}\<close>
    by (simp add: Collect_disj_eq[symmetric], blast)
  also have \<open>... =
    (if \<forall>x. l' x \<le> l
     then {\<Union> A' |A'. A' \<noteq> {} \<and> A' \<subseteq> range (\<lambda>x. {s'. l' s' \<le> l \<longrightarrow> e x = e s'})}
     else insert UNIV
            {\<Union> A' |A'. A' \<noteq> {} \<and> UNIV \<notin> A' \<and> A' \<subseteq> (\<lambda>x. {s'. l' s' \<le> l \<longrightarrow> e x = e s'}) ` {x. l' x \<le> l}})\<close>
    by (simp add: subset_insert_iff if_distrib[where f=\<open>(\<and>) _\<close>] if_bool_eq_disj
        conj_disj_distribL ex_disj_distrib Collect_disj_eq, blast)
  also have \<open>... =
    (if \<forall>x. l' x \<le> l
     then supcl (equiv_classes_by e)
     else insert UNIV
            (supcl ((\<lambda>x. {s'. l' s' \<le> l \<longrightarrow> e x = e s'}) ` {x. l' x \<le> l})))\<close>
    by (auto simp add: supcl_def)
  also have \<open>... =
    (if \<forall>x. l' x \<le> l
      then supcl (((\<union>) {s'. \<not> l' s' \<le> l} \<circ> equiv_class_by e) ` {s. l' s \<le> l})
      else insert UNIV (supcl
        (((\<union>) {s'. \<not> l' s' \<le> l} \<circ> equiv_class_by e) ` {s. l' s \<le> l})
      ))\<close>
    by (simp add: Un_def)
  also have \<open>... =
    insert UNIV
      (supcl (((\<union>) {s'. \<not> l' s' \<le> l} \<circ> equiv_class_by e) ` {s. l' s \<le> l}))\<close>
    using iffD2[OF helper, of \<open>((\<union>) {s'. \<not> l' s' \<le> l} \<circ> equiv_class_by e) ` {s. l' s \<le> l}\<close>]
    by force
  also have \<open>... =
    insert UNIV
      (supcl
        ((\<union>) {s'. \<not> l' s' \<le> l} `
          (Set.filter
            ((\<noteq>) {} \<circ> (\<inter>) (Collect ((\<ge>) l \<circ> l')))
            (equiv_classes_by e))))\<close>

    apply (rule arg_cong[of _ _ \<open>insert UNIV\<close>])
    apply (simp add: supcl_def image_def)
    sorry


  show ?thesis
    sorry
qed

(*
definition sec_points_to
  :: \<open>'a \<Rightarrow> 'b \<Rightarrow> ('a \<rightharpoonup> 'b) sec_rel\<close>
  (infix \<open>\<^bold>\<mapsto>\<^sub>s\<close> 90)
  where
  \<open>p \<^bold>\<mapsto>\<^sub>s v \<equiv> \<T> (p \<^bold>\<mapsto> v)\<close>

(* Low(e,e') in the paper.
    The paper produces \<open>emp\<close> when it's successful; we cannot, as we have a unitary resource model.
    Thus, we must say \<open>lowe e e' \<and> ...\<close>.
*)

definition lowe
  :: \<open>('st::perm_alg \<Rightarrow> 'v) \<Rightarrow> ('st \<Rightarrow> 'v) \<Rightarrow> 'st sec_rel\<close>
  where
  \<open>lowe e e' \<equiv> \<lambda>(sl, sh). (if e sl = e' sl then \<top> else \<bottom>)\<close>
*)

lemma
  \<open>r = (\<lambda>(s,h) (s',h'). \<phi> s \<and> \<phi> s' \<and> h = h' \<and> h = 0) \<Longrightarrow>
     tight_reflp r \<and> transp r \<and> symp r\<close>
  by (clarsimp simp add: prepost_state_def' reflp_on_def transp_def
      symp_def)

lemma
  \<open>r = (\<lambda>s s'. l' s \<le> l \<longrightarrow> l' s' \<le> l \<longrightarrow> e s = e s') \<Longrightarrow>
      reflp r \<and> symp r\<close>
  by (clarsimp simp add: reflp_def symp_def)

lemma
  \<open>r = (\<lambda>s s'. l' s \<le> l \<longrightarrow> l' s' \<le> l \<longrightarrow> e s = e s') \<Longrightarrow>
     transp r\<close>
  apply (clarsimp simp add: transp_def)
  oops

lemma
  \<open>r = (\<lambda>(s,h) (s',h'). (ep s \<^bold>\<mapsto> ev s) h \<and> (ep s' \<^bold>\<mapsto> ev s') h') \<Longrightarrow>
      tight_reflp r \<and> transp r \<and> symp r\<close>
  by (clarsimp simp add: prepost_state_def' reflp_on_def transp_def symp_def
      points_to_def split: prod.splits)

lemma
  \<open>reflp (curry p) \<Longrightarrow> reflp (curry q) \<Longrightarrow> reflp (curry (p \<leadsto> q))\<close>
  by (clarsimp simp add: prepost_state_def' reflp_on_def
      reflp_def symp_def split: prod.splits)

(* nope *)
lemma
  \<open>tight_reflp (curry p) \<Longrightarrow> tight_reflp (curry q) \<Longrightarrow>
    tight_reflp (curry (p \<leadsto> q))\<close>
  nitpick
  oops

lemma
  \<open>tight_reflp (curry p) \<Longrightarrow> tight_reflp (curry q) \<Longrightarrow>
    tight_reflp (curry (p \<sqinter> q))\<close>
  by (clarsimp simp add: reflp_on_def prepost_state_def')
    blast

lemma
  \<open>tight_reflp (curry p) \<Longrightarrow> tight_reflp (curry q) \<Longrightarrow>
    tight_reflp (curry (p \<squnion> q))\<close>
  by (clarsimp simp add: reflp_on_def prepost_state_def')
    blast

lemma
  \<open>tight_reflp (curry p) \<Longrightarrow> tight_reflp (curry q) \<Longrightarrow>
    tight_reflp (curry (p \<^emph> q))\<close>
  apply (clarsimp simp add: reflp_on_def prepost_state_def' sepconj_def)
  apply (intro conjI impI allI)
   apply fast
  apply metis
  done

lemma
  \<open>symp (curry p) \<Longrightarrow> symp (curry q) \<Longrightarrow> symp (curry (p \<^emph> q))\<close>
  by (clarsimp simp add: symp_def sepconj_def)
    blast

lemma
  \<open>symp (curry p) \<Longrightarrow> symp (curry q) \<Longrightarrow> symp (curry (p \<squnion> q))\<close>
  by (clarsimp simp add: symp_def sepconj_def)

lemma
  \<open>symp (curry p) \<Longrightarrow> symp (curry q) \<Longrightarrow> symp (curry (p \<sqinter> q))\<close>
  by (clarsimp simp add: symp_def sepconj_def)

lemma
  \<open>symp (curry p) \<Longrightarrow> symp (curry q) \<Longrightarrow> symp (curry (p \<leadsto> q))\<close>
  by (clarsimp simp add: symp_def sepconj_def)

lemma
  \<open>symp (curry p) \<Longrightarrow> symp (curry (- p))\<close>
  by (clarsimp simp add: symp_def sepconj_def)

end