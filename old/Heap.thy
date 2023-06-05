theory Heap
  imports Stabilisation
begin

section \<open>Finite Heaps\<close>

typedef ('p,'v) heap = \<open>{h::'p \<rightharpoonup> 'v. finite (dom h)}\<close>
  by (rule exI[where x=Map.empty], force)

setup_lifting type_definition_heap

lemma eq_Rep_heap_iff:
  \<open>a = Rep_heap a' \<longleftrightarrow> a' = Abs_heap a \<and> finite (dom a)\<close>
  \<open>Rep_heap a' = a \<longleftrightarrow> a' = Abs_heap a \<and> finite (dom a)\<close>
  by (metis Abs_heap_inverse Rep_heap Rep_heap_inverse mem_Collect_eq)+

lemma eq_Abs_heap_iff:
  \<open>finite (dom a) \<Longrightarrow> a' = Abs_heap a \<longleftrightarrow> a = Rep_heap a'\<close>
  \<open>finite (dom a) \<Longrightarrow> Abs_heap a = a' \<longleftrightarrow> a = Rep_heap a'\<close>
  by (force simp add: eq_Rep_heap_iff)+

lemma finite_dom_Rep_heap[simp]:
  \<open>finite (dom (Rep_heap a))\<close>
  using eq_Rep_heap_iff by auto

instantiation heap :: (type,type) cancel_seplogic
begin

lift_definition disjoint_heap :: \<open>('a,'b) heap \<Rightarrow> ('a,'b) heap \<Rightarrow> bool\<close> is
  \<open>\<lambda>a b. dom a \<inter> dom b = {}\<close> .

lift_definition plus_heap :: \<open>('a,'b) heap \<Rightarrow> ('a,'b) heap \<Rightarrow> ('a,'b) heap\<close> is \<open>(++)\<close>
  by simp

lift_definition zero_heap :: \<open>('a,'b) heap\<close> is \<open>Map.empty\<close>
  by simp

lift_definition bot_heap :: \<open>('a,'b) heap\<close> is \<open>Map.empty\<close>
  by simp

lift_definition less_eq_heap :: \<open>('a,'b) heap \<Rightarrow> ('a,'b) heap \<Rightarrow> bool\<close> is
  \<open>(\<subseteq>\<^sub>m)\<close> .

definition less_heap :: \<open>('a,'b) heap \<Rightarrow> ('a,'b) heap \<Rightarrow> bool\<close> where
  \<open>less_heap a b \<equiv> a \<le> b \<and> \<not>(b \<le> a)\<close>

lift_definition minus_heap :: \<open>('a,'b) heap \<Rightarrow> ('a,'b) heap \<Rightarrow> ('a,'b) heap\<close> is
  \<open>\<lambda>a b. a |` (- dom b)\<close> by simp


instance
  apply standard
                   apply (simp add: less_heap_def; fail)
                  apply (simp add: less_eq_heap_def; fail)
                 apply (force intro: map_le_trans simp add: less_eq_heap_def)
                apply (force dest: map_le_antisym simp add: less_eq_heap_def Rep_heap_inject)
               apply (simp add: less_eq_heap_def bot_heap_def Abs_heap_inverse; fail)
              apply (force simp add: disjoint_heap_def)
             apply (simp add: disjoint_heap_def zero_heap_def Abs_heap_inverse; fail)
            apply (simp add: disjoint_heap_def plus_heap_def Abs_heap_inverse Int_Un_distrib
      sup_commute; fail)
           apply (simp add: disjoint_heap_def plus_heap_def Abs_heap_inverse Int_Un_distrib
      Int_commute; fail)
          apply (simp add: disjoint_heap_def plus_heap_def less_eq_heap_def eq_Abs_heap_iff
      le_map_le_iff_sepadd, metis dom_map_add eq_Rep_heap_iff finite_Un; fail)
         apply (simp add: disjoint_heap_def plus_heap_def Abs_heap_inverse; fail)
        apply (fastforce dest: map_add_comm simp add: disjoint_heap_def plus_heap_def)
       apply (simp add: plus_heap_def zero_heap_def Abs_heap_inverse Rep_heap_inverse; fail)
      apply (simp add: plus_heap_def minus_heap_def disjoint_heap_def
      Abs_heap_inverse Rep_heap_inverse
      disjoint_dom_map_add_restrict_distrib Int_commute dom_disjoint_restrict_eq; fail)
     apply (simp add: plus_heap_def minus_heap_def disjoint_heap_def
      Abs_heap_inverse Int_commute; fail)
    apply (simp add: plus_heap_def minus_heap_def disjoint_heap_def Abs_heap_inverse; fail)

   apply (simp add: plus_heap_def minus_heap_def disjoint_heap_def
      Abs_heap_inverse eq_Abs_heap_iff map_restrict_un_eq)
   apply (metis dom_subset_restrict_eq inf_sup_ord(2) map_restrict_un_eq sup_commute sup_neg_inf)

  apply (simp add: minus_heap_def plus_heap_def disjoint_heap_def eq_Abs_heap_iff Abs_heap_inverse,
      metis Compl_Int dom_disjoint_restrict_eq inf_bot_right map_restrict_un_eq; fail)
  done

end


lift_definition dom_heap :: \<open>('a,'b) heap \<Rightarrow> 'a set\<close> is \<open>dom\<close> .

lift_definition restrict_heap :: \<open>('a,'b) heap \<Rightarrow> 'a set \<Rightarrow> ('a,'b) heap\<close>
  (infixl \<open>|`\<^sub>h\<close> 110) is \<open>(|`)\<close>
  by simp

lemma restrict_heap_un_eq: \<open>h |`\<^sub>h (A \<union> B) = h |`\<^sub>h A + h |`\<^sub>h B\<close>
  by (simp add: restrict_heap_def plus_heap_def Abs_heap_inverse map_restrict_un_eq)

lemma restrict_heap_add_eq[simp]:
  \<open>(a + b) |`\<^sub>h A = a |`\<^sub>h A + b |`\<^sub>h A\<close>
  by (simp add: disjoint_heap_def restrict_heap_def plus_heap_def Abs_heap_inverse
      Abs_heap_inject, simp add: map_add_def restrict_map_def fun_eq_iff)

lemma dom_restrict_heap_eq[simp]: \<open>dom_heap (h |`\<^sub>h A) = dom_heap h \<inter> A\<close>
  by (simp add: dom_heap.rep_eq restrict_heap.rep_eq)

lemma dom_plus_heap_eq[simp]: \<open>dom_heap (h1 + h2) = dom_heap h1 \<union> dom_heap h2\<close>
  by (simp add: dom_heap.rep_eq plus_heap.rep_eq sup_commute)

lemma restrict_heap_ge_dom_eq[simp]: \<open>dom_heap h \<subseteq> A \<Longrightarrow> h |`\<^sub>h A = h\<close>
  by (simp add: dom_heap.rep_eq restrict_heap_def eq_Abs_heap_iff,
      metis inf.absorb_iff1 map_le_refl map_le_restrict_eq restrict_restrict)

lemma restrict_disjoint_dom[simp]:
  \<open>a ## b \<Longrightarrow> a |`\<^sub>h dom_heap b = 0\<close>
  \<open>a ## b \<Longrightarrow> b |`\<^sub>h dom_heap a = 0\<close>
  by (simp add: dom_heap_def restrict_heap_def disjoint_heap_def zero_heap_def Abs_heap_inject,
      force simp add: restrict_map_def fun_eq_iff domIff)+

lemma heap_restrict_Compl_disjoint[simp]:
  \<open>a |`\<^sub>h A ## a |`\<^sub>h (- A)\<close>
  by (simp add: restrict_heap_def disjoint_heap_def Abs_heap_inverse)

lemma heap_restrict_Compl_plus_eq[simp]:
  \<open>a |`\<^sub>h A + a |`\<^sub>h (- A) = a\<close>
  by (simp add: restrict_heap_def disjoint_heap_def plus_heap_def
      Abs_heap_inverse Rep_heap_inverse map_restrict_un_eq[symmetric] dom_subset_restrict_eq)

lemma restrict_Coml_dom_eq[simp]:
  \<open>a |`\<^sub>h (- dom_heap a) = 0\<close>
  by (metis heap_restrict_Compl_disjoint heap_restrict_Compl_plus_eq order_refl
      restrict_heap_ge_dom_eq sepadd_cancel_right_right)

lemma restrict_Compl_disjoint_heap[simp]:
  \<open>a ## b \<Longrightarrow> a |`\<^sub>h (- dom_heap b) = a\<close>
  \<open>a ## b \<Longrightarrow> b |`\<^sub>h (- dom_heap a) = b\<close>
  by (simp add: disjoint_eq_subset_Compl disjoint_heap.rep_eq dom_heap.rep_eq compl_le_swap1)+

subsection \<open>Heap Stabilisation\<close>

lemma rely_additivity_impl_rely_consistent_subheap:
  fixes a b :: \<open>('a,'v) heap\<close>
  assumes rely_additivity_of_update:
    \<open>\<And>a1 a2 b. a1 ## a2 \<Longrightarrow> R\<^sup>*\<^sup>* (a1 + a2) b \<Longrightarrow> \<exists>b1 b2. b1 ## b2 \<and> b = b1 + b2 \<and> R\<^sup>*\<^sup>* a1 b1 \<and> R\<^sup>*\<^sup>* a2 b2\<close>
  shows
    \<open>R\<^sup>*\<^sup>* a b \<Longrightarrow> \<exists>B. R\<^sup>*\<^sup>* (a |`\<^sub>h A) (b |`\<^sub>h B) \<and> R\<^sup>*\<^sup>* (a |`\<^sub>h (- A)) (b |`\<^sub>h (- B))\<close>
  using rely_additivity_of_update[of \<open>a |`\<^sub>h A\<close> \<open>a |`\<^sub>h (- A)\<close> b]
  by (clarsimp, rule_tac x=\<open>dom_heap b1\<close> in exI, simp)

lemma rely_consistent_Compl_subheaps_impl_rely_additivity:
  fixes a b :: \<open>('a,'v) heap\<close>
  assumes rely_consistent_subheap:
    \<open>\<And>a b A. R\<^sup>*\<^sup>* a b \<Longrightarrow> \<exists>B. R\<^sup>*\<^sup>* (a |`\<^sub>h A) (b |`\<^sub>h B) \<and> R\<^sup>*\<^sup>* (a |`\<^sub>h (- A)) (b |`\<^sub>h (- B))\<close>
  shows
    \<open>a1 ## a2 \<Longrightarrow> R\<^sup>*\<^sup>* (a1 + a2) b \<Longrightarrow> \<exists>b1 b2. b1 ## b2 \<and> b = b1 + b2 \<and> R\<^sup>*\<^sup>* a1 b1 \<and> R\<^sup>*\<^sup>* a2 b2\<close>
  using rely_consistent_subheap[of \<open>a1 + a2\<close> b \<open>dom_heap a1\<close>]
  using set_eq_subset by fastforce


lemma rely_additivity_impl_rely_consistent_subheap2:
  fixes a b :: \<open>('a,'v) heap\<close>
  assumes rely_additivity_of_update:
    \<open>\<And>a1 a2 b. a1 ## a2 \<Longrightarrow> R\<^sup>*\<^sup>* (a1 + a2) b \<Longrightarrow> \<exists>b1 b2. b1 ## b2 \<and> b = b1 + b2 \<and> R\<^sup>*\<^sup>* a1 b1 \<and> R\<^sup>*\<^sup>* a2 b2\<close>
  shows
    \<open>R\<^sup>*\<^sup>* a b \<Longrightarrow> \<exists>bx. bx \<le> b \<and> R\<^sup>*\<^sup>* (a |`\<^sub>h A) bx \<and> R\<^sup>*\<^sup>* (a |`\<^sub>h (- A)) (b |`\<^sub>h (- dom_heap bx))\<close>
  using rely_additivity_of_update[of \<open>a |`\<^sub>h A\<close> \<open>a |`\<^sub>h (- A)\<close> b]
  by (fastforce intro!: le_plus)

lemma rely_consistent_Compl_subheaps_impl_rely_additivity2:
  fixes a b :: \<open>('a,'v) heap\<close>
  assumes rely_consistent_subheap:
    \<open>\<And>a b A. R\<^sup>*\<^sup>* a b \<Longrightarrow> \<exists>bx. bx \<le> b \<and> R\<^sup>*\<^sup>* (a |`\<^sub>h A) bx \<and> R\<^sup>*\<^sup>* (a |`\<^sub>h (- A)) (b |`\<^sub>h (- dom_heap bx))\<close>
  shows
    \<open>a1 ## a2 \<Longrightarrow> R\<^sup>*\<^sup>* (a1 + a2) b \<Longrightarrow> \<exists>b1 b2. b1 ## b2 \<and> b = b1 + b2 \<and> R\<^sup>*\<^sup>* a1 b1 \<and> R\<^sup>*\<^sup>* a2 b2\<close>
  using rely_consistent_subheap[of \<open>a1 + a2\<close> b \<open>dom_heap a1\<close>]
  by (force simp add: le_iff_sepadd)


lemma swstable_sepconj_semidistrib_heap:
  fixes P Q :: \<open>('a,'b) heap \<Rightarrow> bool\<close>
  assumes rely_consistent_Compl_subheaps:
    \<open>\<And>a b A. R\<^sup>*\<^sup>* a b \<Longrightarrow> \<exists>B. R\<^sup>*\<^sup>* (a |`\<^sub>h A) (b |`\<^sub>h B) \<and> R\<^sup>*\<^sup>* (a |`\<^sub>h (- A)) (b |`\<^sub>h (- B))\<close>
  shows \<open>\<lfloor> P \<rfloor>\<^bsub>R\<^esub> \<^emph> \<lfloor> Q \<rfloor>\<^bsub>R\<^esub> \<le> \<lfloor> P \<^emph> Q \<rfloor>\<^bsub>R\<^esub>\<close>
  using assms
  by (force intro!: swstable_sepconj_semidistrib rely_consistent_Compl_subheaps_impl_rely_additivity)

lemma wsstable_sepconj_semidistrib_heap:
  fixes P Q :: \<open>('a,'b) heap \<Rightarrow> bool\<close>
  assumes rely_consistent_Compl_subheaps:
    \<open>\<And>a b A. R\<^sup>*\<^sup>* a b \<Longrightarrow> \<exists>B. R\<^sup>*\<^sup>* (a |`\<^sub>h A) (b |`\<^sub>h B) \<and> R\<^sup>*\<^sup>* (a |`\<^sub>h (- A)) (b |`\<^sub>h (- B))\<close>
  shows \<open>\<lceil> P \<^emph> Q \<rceil>\<^bsub>R\<^esub> \<le> \<lceil> P \<rceil>\<^bsub>R\<^esub> \<^emph> \<lceil> Q \<rceil>\<^bsub>R\<^esub>\<close>
  using assms
  by (force intro!: wsstable_sepconj_semidistrib rely_consistent_Compl_subheaps_impl_rely_additivity)

end