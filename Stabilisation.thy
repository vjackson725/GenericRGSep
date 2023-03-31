theory Stabilisation
  imports SepLogic HOL.Rat
begin

section \<open>Helper Lemmas\<close>

lemma conj_imp_distribR:
  \<open>(p \<longrightarrow> q) \<and> r \<longleftrightarrow> (\<not> p \<and> r) \<or> (q \<and> r)\<close>
  by force

lemma conj_imp_distribL:
  \<open>p \<and> (q \<longrightarrow> r) \<longleftrightarrow> (p \<and> \<not> q) \<or> (p \<and> r)\<close>
  by force

lemma all_simps2[simp]:
  \<open>(\<forall>x y. P y \<longrightarrow> Q x y) = (\<forall>y. P y \<longrightarrow> (\<forall>x. Q x y))\<close>
  by force

lemma le_map_le_iff_sepadd:
  \<open>(a \<subseteq>\<^sub>m b) = (\<exists>c. dom a \<inter> dom c = {} \<and> b = a ++ c)\<close>
  by (metis dom_restrict inf_compl_bot_right map_add_comm map_le_map_add map_le_split)

lemma disjoint_dom_map_add_restrict_distrib:
  \<open>dom a \<inter> dom b = {} \<Longrightarrow> (a ++ b) |` A = a |` A ++ b |` A\<close>
  by (simp add: fun_eq_iff restrict_map_def map_add_def)

lemma antidom_restrict_eq[simp]:
  \<open>a |` (- dom a) = Map.empty\<close>
  by (force simp add: restrict_map_def subset_iff domIff)

lemma dom_subset_restrict_eq:
  \<open>dom a \<subseteq> A \<Longrightarrow>  a |` A = a\<close>
  by (force simp add: restrict_map_def subset_iff domIff)

lemmas dom_disjoint_restrict_eq =
  dom_subset_restrict_eq[OF iffD1[OF disjoint_eq_subset_Compl]]

lemma transp_subrel_compp_smaller:
  \<open>transp S \<Longrightarrow> R \<le> S \<Longrightarrow> S OO R \<le> S\<close>
  \<open>transp S \<Longrightarrow> R \<le> S \<Longrightarrow> R OO S \<le> S\<close>
  by (meson order.refl order.trans relcompp_mono transp_relcompp_less_eq)+

lemma rel_le_rtranscp_relcompp_absorb:
  \<open>R \<le> S \<Longrightarrow> S\<^sup>*\<^sup>* OO R\<^sup>*\<^sup>* = S\<^sup>*\<^sup>*\<close>
  \<open>R \<le> S \<Longrightarrow> R\<^sup>*\<^sup>* OO S\<^sup>*\<^sup>* = S\<^sup>*\<^sup>*\<close>
   apply -
   apply (rule antisym)
    apply (metis rtranclp_mono transp_rtranclp transp_subrel_compp_smaller(1))
   apply force
  apply (rule antisym)
   apply (simp add: rtranclp_mono transp_subrel_compp_smaller(2))
  apply force
  done

lemma not_Some_prod_eq[iff]: \<open>(\<forall>a b. x \<noteq> Some (a,b)) \<longleftrightarrow> x = None\<close>
  by (metis option.exhaust option.simps(3) surj_pair)

lemmas rev_finite_subset_Collect =
  rev_finite_subset[of \<open>Collect P\<close> \<open>Collect Q\<close> for P Q, OF _ iffD2[OF Collect_mono_iff]]


section \<open>Stabilisation\<close>

(* strongest weaker stable predicate *)
definition swstable_pred
  :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close>
  ("\<lfloor> _ \<rfloor>\<^bsub>_\<^esub>" [0,0] 90)
  where
  \<open>\<lfloor> P \<rfloor>\<^bsub>R\<^esub> \<equiv> \<lambda>s. \<forall>s'. R\<^sup>*\<^sup>* s s' \<longrightarrow> P s'\<close>

(* weakest stronger stable predicate *)
definition wsstable_pred
  :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close>
  ("\<lceil> _ \<rceil>\<^bsub>_\<^esub>" [0,0] 90)
  where
  \<open>\<lceil> P \<rceil>\<^bsub>R\<^esub> \<equiv> \<lambda>s'. \<exists>s. R\<^sup>*\<^sup>* s s' \<and> P s\<close>

subsection \<open>basic logical properties\<close>

lemma swstable_weaker: \<open>\<lfloor> P \<rfloor>\<^bsub>R\<^esub> \<le> P\<close>
  by (force simp add: swstable_pred_def)

lemma wsstable_stronger: \<open>P \<le> \<lceil> P \<rceil>\<^bsub>R\<^esub>\<close>
  by (force simp add: wsstable_pred_def)

subsection \<open>(semi)distributivity properties\<close>

lemma swstable_conj_distrib: \<open>\<lfloor> P \<sqinter> Q \<rfloor>\<^bsub>R\<^esub> = \<lfloor> P \<rfloor>\<^bsub>R\<^esub> \<sqinter> \<lfloor> Q \<rfloor>\<^bsub>R\<^esub>\<close>
  by (force simp add: swstable_pred_def)

lemma swstable_disj_semidistrib: \<open>\<lfloor> P \<rfloor>\<^bsub>R\<^esub> \<squnion> \<lfloor> Q \<rfloor>\<^bsub>R\<^esub> \<le> \<lfloor> P \<squnion> Q \<rfloor>\<^bsub>R\<^esub>\<close>
  by (force simp add: swstable_pred_def)

lemma wsstable_disj_distrib: \<open>\<lceil> P \<squnion> Q \<rceil>\<^bsub>R\<^esub> = \<lceil> P \<rceil>\<^bsub>R\<^esub> \<squnion> \<lceil> Q \<rceil>\<^bsub>R\<^esub>\<close>
  by (force simp add: wsstable_pred_def)

lemma wsstable_conj_semidistrib: \<open>\<lceil> P \<sqinter> Q \<rceil>\<^bsub>R\<^esub> \<le> \<lceil> P \<rceil>\<^bsub>R\<^esub> \<sqinter> \<lceil> Q \<rceil>\<^bsub>R\<^esub>\<close>
  by (force simp add: wsstable_pred_def)

subsection \<open>Rely Monotonicity\<close>

lemma swstable_rely_antimono: \<open>R \<le> S \<Longrightarrow> \<lfloor> P \<rfloor>\<^bsub>S\<^esub> \<le> \<lfloor> P \<rfloor>\<^bsub>R\<^esub>\<close>
  using mono_rtranclp
  by (force simp add: swstable_pred_def le_fun_def)

lemma wsstable_rely_mono: \<open>R \<le> S \<Longrightarrow> \<lceil> P \<rceil>\<^bsub>R\<^esub> \<le> \<lceil> P \<rceil>\<^bsub>S\<^esub>\<close>
  using mono_rtranclp
  by (force simp add: wsstable_pred_def le_fun_def)

subsection \<open>nested stabilisation\<close>

lemma wsstable_absorb[simp]:
  assumes \<open>R\<^sup>*\<^sup>* = Ra\<^sup>*\<^sup>* OO Rb\<^sup>*\<^sup>*\<close>
  shows \<open>\<lceil> \<lceil> P \<rceil>\<^bsub>Ra\<^esub> \<rceil>\<^bsub>Rb\<^esub> = \<lceil> P \<rceil>\<^bsub>R\<^esub>\<close>
  by (force simp add: assms wsstable_pred_def relcompp_apply fun_eq_iff)

lemma wsstable_absorb1[simp]: \<open>R \<le> R' \<Longrightarrow> \<lceil> \<lceil> P \<rceil>\<^bsub>R\<^esub> \<rceil>\<^bsub>R'\<^esub> = \<lceil> P \<rceil>\<^bsub>R'\<^esub>\<close>
  by (simp add: rel_le_rtranscp_relcompp_absorb)

lemma wsstable_absorb2[simp]: \<open>R \<le> R' \<Longrightarrow> \<lceil> \<lceil> P \<rceil>\<^bsub>R'\<^esub> \<rceil>\<^bsub>R\<^esub> = \<lceil> P \<rceil>\<^bsub>R'\<^esub>\<close>
  by (simp add: rel_le_rtranscp_relcompp_absorb)

lemma swstable_absorb[simp]:
  \<open>R\<^sup>*\<^sup>* = Rb\<^sup>*\<^sup>* OO Ra\<^sup>*\<^sup>* \<Longrightarrow> \<lfloor> \<lfloor> P \<rfloor>\<^bsub>Ra\<^esub> \<rfloor>\<^bsub>Rb\<^esub> = \<lfloor> P \<rfloor>\<^bsub>R\<^esub>\<close>
  by (force simp add: swstable_pred_def relcompp_apply imp_ex imp_conjL fun_eq_iff)

lemma swstable_absorb1[simp]: \<open>R \<le> R' \<Longrightarrow> \<lfloor> \<lfloor> P \<rfloor>\<^bsub>R\<^esub> \<rfloor>\<^bsub>R'\<^esub> = \<lfloor> P \<rfloor>\<^bsub>R'\<^esub>\<close>
  by (simp add: rel_le_rtranscp_relcompp_absorb)

lemma swstable_absorb2[simp]: \<open>R \<le> R' \<Longrightarrow> \<lfloor> \<lfloor> P \<rfloor>\<^bsub>R'\<^esub> \<rfloor>\<^bsub>R\<^esub> = \<lfloor> P \<rfloor>\<^bsub>R'\<^esub>\<close>
  by (simp add: rel_le_rtranscp_relcompp_absorb)


lemma wsstable_swstable_absorb[simp]: \<open>R \<le> R' \<Longrightarrow> \<lceil> \<lfloor> P \<rfloor>\<^bsub>R'\<^esub> \<rceil>\<^bsub>R\<^esub> = \<lfloor> P \<rfloor>\<^bsub>R'\<^esub>\<close>
  unfolding wsstable_pred_def swstable_pred_def
  by (metis (opaque_lifting) predicate2D rtranclp.rtrancl_refl rtranclp_trans rtranclp_mono)

lemma swstable_wsstable_absorb[simp]: \<open>R \<le> R' \<Longrightarrow> \<lfloor> \<lceil> P \<rceil>\<^bsub>R'\<^esub> \<rfloor>\<^bsub>R\<^esub> = \<lceil> P \<rceil>\<^bsub>R'\<^esub>\<close>
  unfolding wsstable_pred_def swstable_pred_def
  by (metis (opaque_lifting) predicate2D rtranclp.rtrancl_refl rtranclp_trans rtranclp_mono)


context seplogic
begin

(*
assumes rely_substate_result_consistent:
  \<open>\<And>a b b'. R\<^sup>*\<^sup>* a b \<Longrightarrow> R\<^sup>*\<^sup>* a b' \<Longrightarrow> b' \<le> b \<Longrightarrow> b' = b\<close>

lemma
  assumes rely_same_dom: \<open>\<And>a b. R\<^sup>*\<^sup>* a b \<Longrightarrow> sepdomeq a b\<close>
  assumes rely_additivity_of_update:
    \<open>\<And>a1 a2 b. a1 ## a2 \<Longrightarrow> R\<^sup>*\<^sup>* (a1 + a2) b \<Longrightarrow> \<exists>b1 b2. R\<^sup>*\<^sup>* a1 b1 \<and> R\<^sup>*\<^sup>* a2 b2 \<and> b = b1 + b2 \<and> b1 ## b2\<close>
  shows
    \<open>\<And>a b a' b'. R\<^sup>*\<^sup>* a b \<Longrightarrow> a' \<le> a \<Longrightarrow> \<exists>b'\<le> b. R\<^sup>*\<^sup>* a' b' \<and> sepdomeq a' b'\<close>
  by (simp add: le_iff_sepadd, blast dest: rely_additivity_of_update intro: rely_same_dom)
*)

lemma swstable_sepconj_semidistrib:
  fixes P Q :: \<open>'a \<Rightarrow> bool\<close>
  assumes rely_additivity_of_update:
    \<open>\<And>a1 a2 b. a1 ## a2 \<Longrightarrow> R\<^sup>*\<^sup>* (a1 + a2) b \<Longrightarrow>
        \<exists>b1 b2. b1 ## b2 \<and> b = b1 + b2 \<and> R\<^sup>*\<^sup>* a1 b1 \<and> R\<^sup>*\<^sup>* a2 b2\<close>
  shows \<open>(\<lfloor> P \<rfloor>\<^bsub>R\<^esub> \<^emph> \<lfloor> Q \<rfloor>\<^bsub>R\<^esub>) s \<Longrightarrow> (\<lfloor> P \<^emph> Q \<rfloor>\<^bsub>R\<^esub>) s\<close>
  using rely_additivity_of_update
  by (simp add: swstable_pred_def sepconj_def le_fun_def, metis)

lemma wsstable_sepconj_semidistrib:
  fixes P Q :: \<open>'a \<Rightarrow> bool\<close>
  assumes rely_additivity_of_update:
    \<open>\<And>a1 a2 b. a1 ## a2 \<Longrightarrow> R\<^sup>*\<^sup>* (a1 + a2) b \<Longrightarrow> \<exists>b1 b2. b1 ## b2 \<and> b = b1 + b2 \<and> R\<^sup>*\<^sup>* a1 b1 \<and> R\<^sup>*\<^sup>* a2 b2\<close>
  shows \<open>\<lceil> P \<^emph> Q \<rceil>\<^bsub>R\<^esub> \<le> \<lceil> P \<rceil>\<^bsub>R\<^esub> \<^emph> \<lceil> Q \<rceil>\<^bsub>R\<^esub>\<close>
  using rely_additivity_of_update
  by (simp add: wsstable_pred_def sepconj_def le_fun_def, metis)

end


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
           apply (simp add: disjoint_heap_def plus_heap_def Abs_heap_inverse
      Int_Un_distrib sup_commute; fail)
  subgoal sorry
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


lemma heap_separating_trichotomy:
  fixes a b :: \<open>('a,'v) heap\<close>
  shows \<open>sepdomsubseteq a b \<or> sepdomsubseteq b a \<or> a ## b\<close>
  apply (simp add: sepdomsubseteq_def)
  nitpick
  oops

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


lemma swstable_sepconj_semidistrib:
  fixes P Q :: \<open>('a,'b) heap \<Rightarrow> bool\<close>
  assumes rely_consistent_Compl_subheaps:
    \<open>\<And>a b A. R\<^sup>*\<^sup>* a b \<Longrightarrow> \<exists>B. R\<^sup>*\<^sup>* (a |`\<^sub>h A) (b |`\<^sub>h B) \<and> R\<^sup>*\<^sup>* (a |`\<^sub>h (- A)) (b |`\<^sub>h (- B))\<close>
  shows \<open>\<lfloor> P \<rfloor>\<^bsub>R\<^esub> \<^emph> \<lfloor> Q \<rfloor>\<^bsub>R\<^esub> \<le> \<lfloor> P \<^emph> Q \<rfloor>\<^bsub>R\<^esub>\<close>
  using assms
  by (force intro!: swstable_sepconj_semidistrib rely_consistent_Compl_subheaps_impl_rely_additivity)

lemma wsstable_sepconj_semidistrib:
  fixes P Q :: \<open>('a,'b) heap \<Rightarrow> bool\<close>
  assumes rely_consistent_Compl_subheaps:
    \<open>\<And>a b A. R\<^sup>*\<^sup>* a b \<Longrightarrow> \<exists>B. R\<^sup>*\<^sup>* (a |`\<^sub>h A) (b |`\<^sub>h B) \<and> R\<^sup>*\<^sup>* (a |`\<^sub>h (- A)) (b |`\<^sub>h (- B))\<close>
  shows \<open>\<lceil> P \<^emph> Q \<rceil>\<^bsub>R\<^esub> \<le> \<lceil> P \<rceil>\<^bsub>R\<^esub> \<^emph> \<lceil> Q \<rceil>\<^bsub>R\<^esub>\<close>
  using assms
  by (force intro!: wsstable_sepconj_semidistrib rely_consistent_Compl_subheaps_impl_rely_additivity)



section \<open>(Weak) Permission Heaps\<close>

typedef ('p,'v) pheap =
  \<open>{h::'p \<rightharpoonup> rat \<times> 'v.
    finite (dom h) \<and> (\<forall>p c v. h p = Some (c,v) \<longrightarrow> 0 \<le> c \<and> c \<le> 1)}\<close>
  by (rule exI[where x=Map.empty], force)

print_theorems

setup_lifting type_definition_pheap

lemma eq_Rep_pheap_iff:
  \<open>a = Rep_pheap a' \<longleftrightarrow> a' = Abs_pheap a \<and> finite (dom a) \<and> (\<forall>p c v. a p = Some (c,v) \<longrightarrow> 0 \<le> c \<and> c \<le> 1)\<close>
  \<open>Rep_pheap a' = a \<longleftrightarrow> a' = Abs_pheap a \<and> finite (dom a) \<and> (\<forall>p c v. a p = Some (c,v) \<longrightarrow> 0 \<le> c \<and> c \<le> 1)\<close>
  by (case_tac a' rule: Abs_pheap_cases, force simp add: Abs_pheap_inverse Abs_pheap_inject)+

lemma eq_Abs_pheap_iff:
  assumes
    \<open>finite (dom a)\<close>
    \<open>\<forall>p c v. a p = Some (c,v) \<longrightarrow> 0 \<le> c \<and> c \<le> 1\<close>
  shows
    \<open>a' = Abs_pheap a \<longleftrightarrow> a = Rep_pheap a'\<close>
    \<open>Abs_pheap a = a' \<longleftrightarrow> a = Rep_pheap a'\<close>
  by (force simp add: assms eq_Rep_pheap_iff)+

definition plus_perm :: \<open>(rat \<times> 'a) option \<Rightarrow> (rat \<times> 'a) option \<Rightarrow> (rat \<times> 'a) option\<close>
  (infixl \<open>\<oplus>\<^sub>p\<close> 65) where
  \<open>plus_perm a b \<equiv> case b of
                    Some (c2, v2) \<Rightarrow>
                      (case a of Some (c1, v1) \<Rightarrow> Some (min (c1+c2) 1, v1) | None \<Rightarrow> Some (c2, v2))
                    | None \<Rightarrow> a\<close>

lemma finite_dom_add[simp]:
  \<open>finite (dom (\<lambda>x. a x \<oplus>\<^sub>p b x)) \<longleftrightarrow> finite (dom a) \<and> finite (dom b)\<close>
  by (simp add: dom_def plus_perm_def imp_conv_disj del: imp_conv_disj[symmetric]
      split: option.splits, blast)

lemma plus_perm_None[simp]:
  \<open>a \<oplus>\<^sub>p None = a\<close>
  \<open>None \<oplus>\<^sub>p b = b\<close>
  by (simp add: plus_perm_def split: option.splits)+


definition minus_perm :: \<open>(rat \<times> 'a) option \<Rightarrow> (rat \<times> 'a) option \<Rightarrow> (rat \<times> 'a) option\<close>
  (infixl \<open>\<ominus>\<^sub>p\<close> 65) where
  \<open>minus_perm a b \<equiv> case a of
                      Some (c1, v1) \<Rightarrow>
                        (case b of
                          Some (c2, v2) \<Rightarrow> if v1 = v2 then None else Some (max (c2 - c1) 0, v1)
                        | None \<Rightarrow> Some (c1, v1))
                    | None \<Rightarrow> None\<close>

lemma finite_dom_minus[intro]:
  \<open>finite (dom a) \<Longrightarrow> finite (dom (\<lambda>x. a x \<ominus>\<^sub>p b x))\<close>
  by (simp add: dom_def minus_perm_def Collect_conj_eq split: option.splits)

lemma minus_perm_None[simp]:
  \<open>a \<ominus>\<^sub>p None = a\<close>
  \<open>None \<ominus>\<^sub>p b = None\<close>
  by (simp add: minus_perm_def split: option.splits)+

lemma minus_perm_SomeR_eq_Some:
  \<open>a \<ominus>\<^sub>p Some (c2, v2) = Some (c, v) \<longleftrightarrow>
      (\<exists>c1. a = Some (c1, v) \<and> c = max (c2 - c1) 0 \<and> v \<noteq> v2)\<close>
  by (force simp add: minus_perm_def max_def split: option.splits)

lemma minus_perm_eq_None[simp]:
  \<open>a \<ominus>\<^sub>p b = None \<longleftrightarrow>
    (a = None \<or> (\<exists>c1 v. a = Some (c1, v) \<and> (\<exists>c2. b = Some (c2, v))))\<close>
  by (simp add: minus_perm_def max_def split: option.splits)


lift_definition app_pheap :: \<open>('a,'b) pheap \<Rightarrow> 'a \<Rightarrow> (rat \<times> 'b) option\<close> (infix \<open>\<bullet>\<close> 990) is
  \<open>\<lambda>m x. m x\<close> .

lemma pheap_ext:
  fixes a b :: \<open>('a,'b) pheap\<close>
  shows \<open>(\<And>x. a \<bullet> x = b \<bullet> x) \<Longrightarrow> a = b\<close>
  by (force intro: iffD1[OF Rep_pheap_inject] simp add: app_pheap_def)

lemma pheap_eq_iff:
  fixes a b :: \<open>('a,'b) pheap\<close>
  shows \<open>a = b \<longleftrightarrow> (\<forall>x. a \<bullet> x = b \<bullet> x)\<close>
  using pheap_ext by blast

lemma Abs_app_pheap:
  \<open>finite (dom m) \<Longrightarrow> (\<And>p c v. m p = Some (c, v) \<Longrightarrow> 0 \<le> c \<and> c \<le> 1) \<Longrightarrow> (Abs_pheap m) \<bullet> x = m x\<close>
  using Abs_pheap_inverse
  by (fastforce simp add: app_pheap_def)

lemma Abs_pheap_inverse_app[simp]:
  \<open>Abs_pheap (Rep_pheap h) \<bullet> x = h \<bullet> x\<close>
  by (simp add: app_pheap_def Rep_pheap_inverse)

lemma Rep_pheap_bounded_permD:
  \<open>Rep_pheap h x = Some (c, v) \<Longrightarrow> 0 \<le> c\<close>
  \<open>Rep_pheap h x = Some (c, v) \<Longrightarrow> c \<le> 1\<close>
  by (metis eq_Rep_pheap_iff(1))+


lift_definition dom_pheap :: \<open>('a,'b) pheap \<Rightarrow> 'a set\<close> is \<open>dom\<close> .

lemma finite_dom_Rep_pheap[simp]:
  \<open>finite (dom (Rep_pheap a))\<close>
  using eq_Rep_pheap_iff by auto

lemma finite_dom_pheap[simp]:
  \<open>finite (dom_pheap a)\<close>
  by (simp add: dom_pheap.rep_eq)

lemma Rep_pheap_Some_prod_set_eq:
  \<open>{x. \<exists>a1 a2. Rep_pheap h x = Some (a1, a2)} = dom_pheap h\<close>
  by (simp add: dom_pheap_def dom_def)

lemma Abs_pheap_lookup:
  \<open>finite (dom m) \<Longrightarrow> \<forall>p c v. m p = Some (c, v) \<longrightarrow> 0 \<le> c \<and> c \<le> 1 \<Longrightarrow>
    Rep_pheap (Abs_pheap m) x = m x\<close>
  by (metis eq_Abs_pheap_iff(2))


lift_definition perm_dom_pheap :: \<open>('a,'b) pheap \<Rightarrow> 'a set\<close>
  is \<open>\<lambda>m. {x|x c v. m x = Some (c, v) \<and> c > 0}\<close> .

lemma finite_perm_dom_pheap[simp]:
  \<open>finite (perm_dom_pheap a)\<close>
  by (rule rev_finite_subset[of \<open>dom_pheap a\<close>];
      force simp add: perm_dom_pheap_def dom_pheap_def subset_iff)

instantiation pheap :: (type,type) disjoint
begin

lift_definition disjoint_pheap :: \<open>('a,'b) pheap \<Rightarrow> ('a,'b) pheap \<Rightarrow> bool\<close> is
  \<open>\<lambda>a b. \<forall>x c1 c2 v1 v2. a x = Some (c1, v1) \<longrightarrow> b x = Some (c2, v2) \<longrightarrow> c1 + c2 \<le> 1 \<and> v1 = v2\<close> .

instance by standard

end

instantiation pheap :: (type, type) plus
begin

lift_definition plus_pheap :: \<open>('a,'b) pheap \<Rightarrow> ('a,'b) pheap \<Rightarrow> ('a,'b) pheap\<close> is
  \<open>\<lambda>ma mb. \<lambda>x. ma x \<oplus>\<^sub>p mb x\<close>
  apply (rename_tac ma mb)
  apply (simp add: dom_def plus_perm_def split: option.splits)
  apply (rule conjI)
   apply (rule_tac B=\<open>dom ma \<union> dom mb\<close> in rev_finite_subset; force simp add: dom_def)
  apply (force intro: add_nonneg_nonneg)
  done

lemma Rep_add_in_bounds:
  assumes \<open>Rep_pheap a p \<oplus>\<^sub>p Rep_pheap b p = Some (c, v)\<close>
  shows \<open>c \<le> 1\<close> \<open>0 \<le> c\<close>
  using assms
  by (simp add: dom_def plus_pheap_def plus_perm_def
      Rep_pheap_bounded_permD eq_commute[of \<open>min _ _\<close>] split: option.splits prod.splits)+

instance by standard

end

instantiation pheap :: (type, type) minus
begin

lift_definition minus_pheap :: \<open>('a,'b) pheap \<Rightarrow> ('a,'b) pheap \<Rightarrow> ('a,'b) pheap\<close> is
  \<open>\<lambda>ma mb. \<lambda>x. ma x \<ominus>\<^sub>p mb x\<close>
  by (force simp add: dom_def minus_perm_def split: option.splits)

instance by standard

lemma Rep_minus_in_bounds:
  assumes \<open>Rep_pheap a p \<ominus>\<^sub>p Rep_pheap b p = Some (c, v)\<close>
  shows \<open>c \<le> 1\<close> \<open>0 \<le> c\<close>
  using assms
  by (clarsimp simp add: dom_def minus_pheap_def minus_perm_def Rep_pheap_bounded_permD
      add_increasing2 diff_le_eq split: option.splits prod.splits if_splits)+

end


lemma app_plus_pheap[simp]:
  \<open>(a + b) \<bullet> x = a \<bullet> x \<oplus>\<^sub>p b \<bullet> x\<close>
  apply (simp add: disjoint_pheap_def plus_pheap_def app_pheap_def)
  apply (subst Abs_pheap_inverse; force simp add: Rep_add_in_bounds)
  done

lemma minus_plus_pheap[simp]:
  \<open>(a - b) \<bullet> x = a \<bullet> x \<ominus>\<^sub>p b \<bullet> x\<close>
  apply (simp add: disjoint_pheap_def minus_pheap_def app_pheap_def)
  apply (subst Abs_pheap_inverse; force simp add: Rep_minus_in_bounds)
  done

instantiation pheap :: (type,type) cancel_seplogic
begin

lift_definition zero_pheap :: \<open>('a,'b) pheap\<close> is \<open>Map.empty\<close>
  by simp

lift_definition bot_pheap :: \<open>('a,'b) pheap\<close> is \<open>Map.empty\<close>
  by simp

lift_definition less_eq_pheap :: \<open>('a,'b) pheap \<Rightarrow> ('a,'b) pheap \<Rightarrow> bool\<close> is
  \<open>\<lambda>ma mb. \<forall>x ca v. ma x = Some (ca, v) \<longrightarrow> (\<exists>cb\<ge>ca. mb x = Some (cb, v))\<close> .

definition less_pheap :: \<open>('a,'b) pheap \<Rightarrow> ('a,'b) pheap \<Rightarrow> bool\<close> where
  \<open>less_pheap a b \<equiv> a \<le> b \<and> \<not>(b \<le> a)\<close>


lemma perm_eq_plus_minus_iff:
  \<open>b = a \<oplus>\<^sub>p (b \<ominus>\<^sub>p a) \<longleftrightarrow> a = None \<or> a = b\<close>
  by (force simp add: plus_perm_def minus_perm_def split: option.splits)

lemma le_iff_minus:
  fixes a b :: \<open>('a,'b) pheap\<close>
  shows \<open>(a \<le> b) = (a ## (b - a) \<and> b = a + (b - a))\<close>
  apply (rule iffI)
  apply (simp add: less_eq_pheap_def disjoint_pheap_def minus_pheap_def plus_pheap_def)
   apply (subst Abs_pheap_inverse, force simp add: Rep_minus_in_bounds)
   apply (subst Abs_pheap_inverse, force simp add: Rep_minus_in_bounds)
   apply (subst eq_Abs_pheap_iff)
     apply force
    apply (metis Rep_add_in_bounds minus_pheap.rep_eq)
   apply (clarsimp simp add: fun_eq_iff plus_perm_def minus_perm_SomeR_eq_Some split: option.splits)
  apply (rule conjI)
    apply (force simp add: max_def Rep_pheap_bounded_permD)
   apply clarsimp
   apply safe
     apply (metis not_Some_prod_eq)
    apply simp
    defer
    apply force
   apply (simp add: pheap_eq_iff perm_eq_plus_minus_iff)
  apply (clarsimp simp add: app_pheap_def less_eq_pheap_def)
  apply (metis not_None_eq order_refl)
  oops

instance
  apply standard
                   apply (simp add: less_pheap_def; fail)
                  apply (simp add: less_eq_pheap_def; fail)
                 apply (force intro: map_le_trans simp add: less_eq_pheap_def)

                apply (clarsimp dest: map_le_antisym simp add: less_eq_pheap_def Rep_pheap_inject)
                apply (rule iffD1[OF Rep_pheap_inject], rule ext)
                apply (rename_tac ma mb x)
                apply (drule_tac x=x in spec, drule_tac x=x in spec)
                apply (case_tac \<open>Rep_pheap ma x\<close>; force)

               apply (simp add: less_eq_pheap_def bot_pheap_def Abs_pheap_inverse; fail)
              apply (force simp add: disjoint_pheap_def)
             apply (force simp add: disjoint_pheap_def zero_pheap_def Abs_pheap_inverse)
(* disjoint_add_leftL *)
            apply (simp add: disjoint_pheap_def plus_pheap_def)
            apply (subst (asm) Abs_pheap_inverse, clarsimp)
             apply (rule conjI)
              apply (rule_tac B=\<open>dom_pheap b \<union> dom_pheap c\<close> in rev_finite_subset, force)
              apply (force simp add: dom_pheap_def split: option.splits)
             apply (clarsimp split: option.splits,
      force dest: Rep_pheap_bounded_permD intro!: add_nonneg_nonneg)
            apply clarsimp
            apply (case_tac \<open>Rep_pheap c x\<close>)
             apply (force split: option.splits)
            apply clarsimp
            apply (drule spec2, drule spec, drule mp, blast)
            apply (drule spec2, drule spec, drule mp, blast)
            apply clarsimp
            apply (meson Rep_pheap_bounded_permD(1) add_left_mono le_add_same_cancel1 order_trans)
(* disjoint_add_left_commute *)
           apply (simp add: disjoint_pheap_def plus_pheap_def)
           apply (subst (asm) Abs_pheap_inverse, clarsimp)
            apply (rule conjI)
             apply (rule_tac B=\<open>dom_pheap a \<union> dom_pheap c\<close> in rev_finite_subset, force)
             apply (force simp add: dom_pheap_def split: option.splits)
            apply (clarsimp split: option.splits,
      force dest: Rep_pheap_bounded_permD intro!: add_nonneg_nonneg)
           apply (subst Abs_pheap_inverse, clarsimp)
            apply (rule conjI)
             apply (rule_tac B=\<open>dom_pheap a \<union> dom_pheap b \<union> dom_pheap c\<close> in rev_finite_subset, force)
             apply (force simp add: dom_pheap_def split: option.splits)
            apply (force dest: Rep_pheap_bounded_permD split: prod.splits option.splits if_splits)
           apply clarsimp
           apply (case_tac \<open>Rep_pheap b x\<close>; case_tac \<open>Rep_pheap c x\<close>)
              apply force
             apply force
            apply force
           apply (clarsimp split: if_splits)
            apply (drule spec2, drule spec, drule mp, blast)
           apply (drule spec2, drule spec, drule mp, blast)
           apply force

          apply (simp add: pheap_eq_iff)

          apply (simp add: less_eq_pheap_def plus_pheap_def disjoint_pheap_def split: option.splits)
          apply (rule iffI)
           apply (subst eq_Abs_pheap_iff)
             apply (rule_tac B=\<open>dom_pheap a \<union> dom_pheap c\<close> in rev_finite_subset;
      force simp add: dom_pheap_def)
            apply (simp split: option.splits,
      force dest: Rep_pheap_bounded_permD intro!: add_nonneg_nonneg)

           apply (rule_tac x=\<open>b - a\<close> in exI)
           apply (clarsimp simp add: fun_eq_iff minus_pheap_def split: option.splits)
  apply (simp add: Abs_pheap_inverse)

  oops
         apply (simp add: disjoint_pheap_def plus_pheap_def Abs_pheap_inverse; fail)
        apply (fastforce dest: map_add_comm simp add: disjoint_pheap_def plus_pheap_def)
           apply (simp add: plus_pheap_def zero_pheap_def Abs_pheap_inverse Rep_pheap_inverse; fail)
      apply (simp add: plus_pheap_def minus_pheap_def disjoint_pheap_def
      Abs_pheap_inverse Rep_pheap_inverse
      disjoint_dom_map_add_restrict_distrib Int_commute dom_disjoint_restrict_eq; fail)
     apply (simp add: plus_pheap_def minus_pheap_def disjoint_pheap_def
      Abs_pheap_inverse Int_commute; fail)
    apply (simp add: plus_pheap_def minus_pheap_def disjoint_pheap_def Abs_pheap_inverse; fail)

   apply (simp add: plus_pheap_def minus_pheap_def disjoint_pheap_def
      Abs_pheap_inverse eq_Abs_pheap_iff map_restrict_un_eq)
   apply (metis dom_subset_restrict_eq inf_sup_ord(2) map_restrict_un_eq sup_commute sup_neg_inf)

  apply (simp add: minus_pheap_def plus_pheap_def disjoint_pheap_def eq_Abs_pheap_iff Abs_pheap_inverse,
      metis Compl_Int dom_disjoint_restrict_eq inf_bot_right map_restrict_un_eq; fail)
  done

end


lift_definition restrict_pheap :: \<open>('a,'b) pheap \<Rightarrow> 'a set \<Rightarrow> ('a,'b) pheap\<close>
  (infixl \<open>|`\<^sub>h\<close> 110) is \<open>(|`)\<close>
  by simp

lemma restrict_pheap_un_eq: \<open>h |`\<^sub>h (A \<union> B) = h |`\<^sub>h A + h |`\<^sub>h B\<close>
  by (simp add: restrict_pheap_def plus_pheap_def Abs_pheap_inverse map_restrict_un_eq)

lemma restrict_pheap_add_eq[simp]:
  \<open>(a + b) |`\<^sub>h A = a |`\<^sub>h A + b |`\<^sub>h A\<close>
  by (simp add: disjoint_pheap_def restrict_pheap_def plus_pheap_def Abs_pheap_inverse
      Abs_pheap_inject, simp add: map_add_def restrict_map_def fun_eq_iff)

lemma dom_restrict_pheap_eq[simp]: \<open>dom_pheap (h |`\<^sub>h A) = dom_pheap h \<inter> A\<close>
  by (simp add: dom_pheap.rep_eq restrict_pheap.rep_eq)

lemma dom_plus_pheap_eq[simp]: \<open>dom_pheap (h1 + h2) = dom_pheap h1 \<union> dom_pheap h2\<close>
  by (simp add: dom_pheap.rep_eq plus_pheap.rep_eq sup_commute)

lemma restrict_pheap_ge_dom_eq[simp]: \<open>dom_pheap h \<subseteq> A \<Longrightarrow> h |`\<^sub>h A = h\<close>
  by (simp add: dom_pheap.rep_eq restrict_pheap_def eq_Abs_pheap_iff,
      metis inf.absorb_iff1 map_le_refl map_le_restrict_eq restrict_restrict)

lemma restrict_disjoint_dom[simp]:
  \<open>a ## b \<Longrightarrow> a |`\<^sub>h dom_pheap b = 0\<close>
  \<open>a ## b \<Longrightarrow> b |`\<^sub>h dom_pheap a = 0\<close>
  by (simp add: dom_pheap_def restrict_pheap_def disjoint_pheap_def zero_pheap_def Abs_pheap_inject,
      force simp add: restrict_map_def fun_eq_iff domIff)+

lemma pheap_restrict_Compl_disjoint[simp]:
  \<open>a |`\<^sub>h A ## a |`\<^sub>h (- A)\<close>
  by (simp add: restrict_pheap_def disjoint_pheap_def Abs_pheap_inverse)

lemma pheap_restrict_Compl_plus_eq[simp]:
  \<open>a |`\<^sub>h A + a |`\<^sub>h (- A) = a\<close>
  by (simp add: restrict_pheap_def disjoint_pheap_def plus_pheap_def
      Abs_pheap_inverse Rep_pheap_inverse map_restrict_un_eq[symmetric] dom_subset_restrict_eq)

lemma restrict_Coml_dom_eq[simp]:
  \<open>a |`\<^sub>h (- dom_pheap a) = 0\<close>
  by (metis pheap_restrict_Compl_disjoint pheap_restrict_Compl_plus_eq order_refl
      restrict_pheap_ge_dom_eq sepadd_cancel_right_right)

lemma restrict_Compl_disjoint_pheap[simp]:
  \<open>a ## b \<Longrightarrow> a |`\<^sub>h (- dom_pheap b) = a\<close>
  \<open>a ## b \<Longrightarrow> b |`\<^sub>h (- dom_pheap a) = b\<close>
  by (simp add: disjoint_eq_subset_Compl disjoint_pheap.rep_eq dom_pheap.rep_eq compl_le_swap1)+


lemma pheap_separating_trichotomy:
  fixes a b :: \<open>('a,'v) pheap\<close>
  shows \<open>sepdomsubseteq a b \<or> sepdomsubseteq b a \<or> a ## b\<close>
  apply (simp add: sepdomsubseteq_def)
  nitpick

  oops
end