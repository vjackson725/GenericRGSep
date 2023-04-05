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

(* We can prove the existence of a map satisfying a relation by showing
    the relation is nice and that there exists a value for every input.
*)
lemma finite_map_choice_iff:
  shows \<open>(\<exists>f. finite (dom f) \<and> (\<forall>x. P x (f x))) \<longleftrightarrow>
          (finite {x. (\<exists>y. P x (Some y)) \<and> \<not> P x None} \<and> (\<forall>x. \<exists>y. P x y))\<close>
  apply -
  apply (rule iffI)
  subgoal (* 1 \<Longrightarrow> 2 *)
    apply (clarsimp simp add: dom_def)
    apply (subgoal_tac \<open>(\<forall>x. f x = None \<longrightarrow> P x None) \<and> (\<forall>x y. f x = Some y \<longrightarrow> P x (Some y))\<close>)
     prefer 2
     apply metis
    apply (rule conjI)
     apply (rule rev_finite_subset, assumption)
     apply blast
    apply force
    done
  subgoal (* 2 \<Longrightarrow> 1 *)
    apply (clarsimp simp add: dom_def)
    apply (clarsimp simp add: choice_iff)
    apply (rule_tac x=\<open>\<lambda>x. if \<exists>y. P x (Some y) \<and> \<not> P x None then f x else None\<close> in exI)
    apply (rule conjI)
     apply clarsimp
     apply (simp add: rev_finite_subset_Collect)
    apply (simp, metis option.exhaust_sel)
    done
  done


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
  morphisms app_pheap Abs_pheap
  by (rule exI[where x=Map.empty], force)

syntax app_pheap :: \<open>('a,'b) pheap \<Rightarrow> 'a \<Rightarrow> (rat \<times> 'b) option\<close> (infix \<open>\<bullet>\<close> 990)

setup_lifting type_definition_pheap

lemma eq_app_pheap_iff:
  \<open>a = app_pheap a' \<longleftrightarrow> a' = Abs_pheap a \<and> finite (dom a) \<and> (\<forall>p c v. a p = Some (c,v) \<longrightarrow> 0 \<le> c \<and> c \<le> 1)\<close>
  \<open>app_pheap a' = a \<longleftrightarrow> a' = Abs_pheap a \<and> finite (dom a) \<and> (\<forall>p c v. a p = Some (c,v) \<longrightarrow> 0 \<le> c \<and> c \<le> 1)\<close>
  by (case_tac a' rule: Abs_pheap_cases, force simp add: Abs_pheap_inverse Abs_pheap_inject)+

lemma eq_Abs_pheap_iff:
  assumes
    \<open>finite (dom a)\<close>
    \<open>\<forall>p c v. a p = Some (c,v) \<longrightarrow> 0 \<le> c \<and> c \<le> 1\<close>
  shows
    \<open>a' = Abs_pheap a \<longleftrightarrow> a = app_pheap a'\<close>
    \<open>Abs_pheap a = a' \<longleftrightarrow> a = app_pheap a'\<close>
  by (force simp add: assms eq_app_pheap_iff)+

definition plus_perm :: \<open>(rat \<times> 'a) option \<Rightarrow> (rat \<times> 'a) option \<Rightarrow> (rat \<times> 'a) option\<close>
  (infixl \<open>\<oplus>\<^sub>p\<close> 65) where
  \<open>plus_perm a b \<equiv> case b of
                    Some (c2, v2) \<Rightarrow>
                      (case a of
                        Some (c1, v1) \<Rightarrow> Some (min (c1+c2) 1, v1)
                        | None \<Rightarrow> Some (c2, v2))
                    | None \<Rightarrow> a\<close>

lemma finite_dom_add[simp]:
  \<open>finite (dom (\<lambda>x. a x \<oplus>\<^sub>p b x)) \<longleftrightarrow> finite (dom a) \<and> finite (dom b)\<close>
  by (simp add: dom_def plus_perm_def imp_conv_disj del: imp_conv_disj[symmetric]
      split: option.splits, blast)

lemma plus_perm_None[simp]:
  \<open>a \<oplus>\<^sub>p None = a\<close>
  \<open>None \<oplus>\<^sub>p b = b\<close>
  by (simp add: plus_perm_def split: option.splits)+

lemma plus_perm_Some[simp]:
  \<open>Some (c1, v1) \<oplus>\<^sub>p Some (c2, v2) = Some (c, v) \<longleftrightarrow> v1 = v \<and> c = min (c1 + c2) 1\<close>
  by (force simp add: plus_perm_def split: option.splits)



definition minus_perm :: \<open>(rat \<times> 'a) option \<Rightarrow> (rat \<times> 'a) option \<Rightarrow> (rat \<times> 'a) option\<close>
  (infixl \<open>\<ominus>\<^sub>p\<close> 65) where
  \<open>minus_perm a b \<equiv> case a of
                      Some (c1, v1) \<Rightarrow>
                        (case b of
                          Some (c2, v2) \<Rightarrow> if v1 = v2 then Some (max (c2 - c1) 0, v1) else None
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
      (\<exists>c1. a = Some (c1, v) \<and> c = max (c2 - c1) 0 \<and> v = v2)\<close>
  by (force simp add: minus_perm_def max_def split: option.splits)

lemma minus_perm_eq_None[simp]:
  \<open>a \<ominus>\<^sub>p b = None \<longleftrightarrow>
    (a = None \<or> (\<exists>c1 v1. a = Some (c1, v1) \<and> (\<exists>c2 v2. b = Some (c2, v2) \<and> v1 \<noteq> v2)))\<close>
  by (simp add: minus_perm_def max_def split: option.splits)


lemma
  fixes c1 c2 :: \<open>'a :: linordered_idom\<close>
  shows
    \<open>(c2 = min (c1 + max (c1 - c2) 0) m) = (c2 = c1 \<and> c2 \<le> m \<or> c2 \<le> c1 \<and> c2 = m)\<close>
  by (fastforce simp add: min_le_iff_disj le_max_iff_disj)

lemma perm_eq_plus_minus_iff:
  \<open>b = a \<oplus>\<^sub>p (b \<ominus>\<^sub>p a) \<longleftrightarrow>
    a = None \<or>
      b = a \<and> (\<exists>c v. a = Some (c, v) \<and> c \<le> 1) \<or>
      (\<exists>v. b = Some (1, v) \<and> (\<exists>c1\<ge>1. a = Some (c1, v)))\<close>
  by (force simp add: plus_perm_def minus_perm_def split: option.splits)

lemma pheap_ext:
  fixes a b :: \<open>('a,'b) pheap\<close>
  shows \<open>(\<And>x. a \<bullet> x = b \<bullet> x) \<Longrightarrow> a = b\<close>
  by (force intro: iffD1[OF app_pheap_inject])

lemma pheap_eq_iff:
  fixes a b :: \<open>('a,'b) pheap\<close>
  shows \<open>a = b \<longleftrightarrow> (\<forall>x. a \<bullet> x = b \<bullet> x)\<close>
  using pheap_ext by blast

lemma Abs_app_pheap:
  \<open>finite (dom m) \<Longrightarrow> (\<And>p c v. m p = Some (c, v) \<Longrightarrow> 0 \<le> c \<and> c \<le> 1) \<Longrightarrow> (Abs_pheap m) \<bullet> x = m x\<close>
  using Abs_pheap_inverse
  by fastforce

lemma Abs_pheap_inverse_app[simp]:
  \<open>Abs_pheap (app_pheap h) \<bullet> x = h \<bullet> x\<close>
  by (simp add: app_pheap_inverse)


lemma app_pheap_bounded_permD:
  \<open>a \<bullet> x = Some (c, v) \<Longrightarrow> 0 \<le> c\<close>
  \<open>a \<bullet> x = Some (c, v) \<Longrightarrow> c \<le> 1\<close>
  by (metis eq_app_pheap_iff(1))+

lift_definition dom_pheap :: \<open>('a,'b) pheap \<Rightarrow> 'a set\<close> is \<open>dom\<close> .

lemma finite_dom_app_pheap[simp]:
  \<open>finite (dom (app_pheap a))\<close>
  by (metis eq_app_pheap_iff(1))

lemma finite_dom_pheap[simp]:
  \<open>finite (dom_pheap a)\<close>
  by (simp add: dom_pheap.rep_eq)

lemma app_pheap_Some_prod_set_eq:
  \<open>{x. \<exists>a1 a2. app_pheap h x = Some (a1, a2)} = dom_pheap h\<close>
  by (simp add: dom_pheap_def dom_def)

lemma Abs_pheap_lookup:
  \<open>finite (dom m) \<Longrightarrow> \<forall>p c v. m p = Some (c, v) \<longrightarrow> 0 \<le> c \<and> c \<le> 1 \<Longrightarrow>
    app_pheap (Abs_pheap m) x = m x\<close>
  by (metis eq_Abs_pheap_iff(2))


lift_definition perm_dom_pheap :: \<open>('a,'b) pheap \<Rightarrow> 'a set\<close>
  is \<open>\<lambda>m. {x|x c v. m x = Some (c, v) \<and> c > 0}\<close> .

lemma finite_perm_dom_pheap[simp]:
  \<open>finite (perm_dom_pheap a)\<close>
  by (rule rev_finite_subset[of \<open>dom_pheap a\<close>];
      force simp add: perm_dom_pheap_def dom_pheap_def subset_iff)

text \<open>Define disjointness on pheaps\<close>
instantiation pheap :: (type,type) disjoint
begin

lift_definition disjoint_pheap :: \<open>('a,'b) pheap \<Rightarrow> ('a,'b) pheap \<Rightarrow> bool\<close> is
  \<open>\<lambda>a b. \<forall>x c1 c2 v1 v2. a x = Some (c1, v1) \<longrightarrow> b x = Some (c2, v2) \<longrightarrow> c1 + c2 \<le> 1 \<and> v1 = v2\<close> .

instance by standard

end


text \<open>Define plus on pheaps\<close>
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

instance by standard

end

lemma Rep_add_in_bounds:
  assumes \<open>app_pheap a p \<oplus>\<^sub>p app_pheap b p = Some (c, v)\<close>
  shows \<open>c \<le> 1\<close> \<open>0 \<le> c\<close>
  using assms
  by (simp add: dom_def plus_pheap_def plus_perm_def
      app_pheap_bounded_permD eq_commute[of \<open>min _ _\<close>] split: option.splits prod.splits)+

lemma app_plus_pheap[simp]:
  \<open>(a + b) \<bullet> x = a \<bullet> x \<oplus>\<^sub>p b \<bullet> x\<close>
  apply (simp add: disjoint_pheap_def plus_pheap_def)
  apply (subst Abs_pheap_inverse; force simp add: Rep_add_in_bounds)
  done


text \<open>Define minus on pheaps\<close>
instantiation pheap :: (type, type) minus
begin

lift_definition minus_pheap :: \<open>('a,'b) pheap \<Rightarrow> ('a,'b) pheap \<Rightarrow> ('a,'b) pheap\<close> is
  \<open>\<lambda>ma mb. \<lambda>x. ma x \<ominus>\<^sub>p mb x\<close>
  by (force simp add: dom_def minus_perm_def split: option.splits)

instance by standard

end

lemma Rep_minus_in_bounds:
  assumes \<open>app_pheap a p \<ominus>\<^sub>p app_pheap b p = Some (c, v)\<close>
  shows \<open>c \<le> 1\<close> \<open>0 \<le> c\<close>
  using assms
  by (clarsimp simp add: dom_def minus_pheap_def minus_perm_def app_pheap_bounded_permD
      add_increasing2 diff_le_eq split: option.splits prod.splits if_splits)+

lemma minus_plus_pheap[simp]:
  \<open>(a - b) \<bullet> x = a \<bullet> x \<ominus>\<^sub>p b \<bullet> x\<close>
  apply (simp add: disjoint_pheap_def minus_pheap_def)
  apply (subst Abs_pheap_inverse; force simp add: Rep_minus_in_bounds)
  done

lemma pheap_eq_plus_minus_iff:
  fixes a b :: \<open>('p,'v) pheap\<close>
  shows \<open>b = a + (b - a) \<longleftrightarrow> (\<forall>x. a \<bullet> x = None \<or> a \<bullet> x = b \<bullet> x)\<close>
  by (simp add: pheap_eq_iff perm_eq_plus_minus_iff,
      metis app_pheap_bounded_permD(2) nle_le not_Some_prod_eq)

lemma perm_eq_diff_eq:
  \<open>Some (c2 - c1, v) = b \<longleftrightarrow> Some (c2, v) = Some (c1, v) \<oplus>\<^sub>p b\<close>
  apply (rule iffI)
  apply (simp add: plus_perm_def split: option.splits)
  prefer 2
  oops

find_theorems \<open>_ + _ = _\<close> \<open>_ = _ - _ \<longleftrightarrow> _\<close>


definition less_eq_perm :: \<open>(rat \<times> 'a) option \<Rightarrow> (rat \<times> 'a) option \<Rightarrow> bool\<close>
  (infix \<open>\<subseteq>\<^sub>p\<close> 100) where
  \<open>a \<subseteq>\<^sub>p b \<equiv> \<forall>ca v. a = Some (ca, v) \<longrightarrow> (\<exists>cb\<ge>ca. b = Some (cb, v))\<close>

lemma less_eq_perm_refl[iff]:
  \<open>a \<subseteq>\<^sub>p a\<close>
  by (simp add: less_eq_perm_def)

lemma less_eq_perm_trans:
  \<open>a \<subseteq>\<^sub>p b \<Longrightarrow> b \<subseteq>\<^sub>p c \<Longrightarrow> a \<subseteq>\<^sub>p c\<close>
  by (force simp add: less_eq_perm_def)

lemma less_eq_perm_NoneL[iff]:
  \<open>None \<subseteq>\<^sub>p a\<close>
  by (force simp add: less_eq_perm_def)

lemma less_eq_perm_NoneR[iff]:
  \<open>a \<subseteq>\<^sub>p None \<longleftrightarrow> a = None\<close>
  by (force simp add: less_eq_perm_def)


text \<open>Define less than and less than or equal on pheaps\<close>
instantiation pheap :: (type, type) preorder
begin

lift_definition less_eq_pheap :: \<open>('a,'b) pheap \<Rightarrow> ('a,'b) pheap \<Rightarrow> bool\<close> is
  \<open>\<lambda>ma mb. \<forall>x. ma x \<subseteq>\<^sub>p mb x\<close> .

lemmas pheap_le_iff = less_eq_pheap.rep_eq

definition less_pheap :: \<open>('a,'b) pheap \<Rightarrow> ('a,'b) pheap \<Rightarrow> bool\<close> where
  \<open>less_pheap a b \<equiv> a \<le> b \<and> \<not>(b \<le> a)\<close>

instance
  by standard
    (simp add: less_pheap_def less_eq_pheap.rep_eq; blast dest: less_eq_perm_trans)+

end


definition compl_perm :: \<open>(rat \<times> 'a) option \<Rightarrow> (rat \<times> 'a) option \<Rightarrow> (rat \<times> 'a) option\<close>
  (infixl \<open>\<oslash>\<^sub>p\<close> 65) where
  \<open>compl_perm a b \<equiv> case a of
                      Some (c1, v1) \<Rightarrow>
                        (case b of
                          Some (c2, v2) \<Rightarrow>
                            if c2 = c1
                            then None
                            else Some (c2 - c1, v2)
                        | None \<Rightarrow> Some (c1, v1))
                    | None \<Rightarrow> b\<close>

lemma compl_pheap_eq[simp]:
  \<open>None \<oslash>\<^sub>p b = b\<close>
  \<open>a \<oslash>\<^sub>p None = a\<close>
  \<open>Some (c, v1) \<oslash>\<^sub>p Some (c, v2) = None\<close>
  \<open>c1 \<noteq> c2 \<Longrightarrow> Some (c1, v1) \<oslash>\<^sub>p Some (c2, v2) = Some (c2 - c1, v2)\<close>
  by (force simp add: compl_perm_def split: option.splits)+


lemma subheap_plus_compl_pheap_inverse:
  \<open>a \<bullet> x \<subseteq>\<^sub>p b \<bullet> x \<Longrightarrow> (a \<bullet> x \<oplus>\<^sub>p (b \<bullet> x \<oslash>\<^sub>p a \<bullet> x)) \<subseteq>\<^sub>p b \<bullet> x\<close>
  apply (clarsimp simp add: plus_perm_def compl_perm_def less_eq_perm_def split: option.splits)
  apply (intro conjI impI allI)
     apply force
    apply force
   apply (drule_tac spec, drule_tac spec, drule_tac mp, blast)
  apply clarsimp
  done

lemma app_Abs_compl_pheap[simp]:
  \<open>\<forall>x ca v. app_pheap a x = Some (ca, v) \<longrightarrow> (\<exists>cb\<ge>ca. app_pheap b x = Some (cb, v)) \<Longrightarrow>
    Abs_pheap (\<lambda>x. a \<bullet> x \<oslash>\<^sub>p b \<bullet> x) \<bullet> x = a \<bullet> x \<oslash>\<^sub>p b \<bullet> x\<close>
  apply (subst Abs_pheap_inverse)
   apply clarsimp
   apply (rule conjI)
    apply (rule rev_finite_subset[of \<open>dom_pheap b\<close>];
      force simp add: compl_perm_def dom_pheap_def less_eq_perm_def split: option.splits)
   apply (clarsimp simp add: compl_perm_def dom_pheap_def less_eq_perm_def split: option.splits)
   apply (intro conjI allI)
     apply (force simp add: app_pheap_bounded_permD)
    apply (force simp add: app_pheap_bounded_permD)
   apply (metis app_pheap_bounded_permD cancel_comm_monoid_add_class.diff_zero diff_mono
      option.inject prod.inject)
  apply (force simp add: app_pheap_bounded_permD)
  done


instantiation pheap :: (type,type) seplogic
begin

lift_definition zero_pheap :: \<open>('a,'b) pheap\<close> is \<open>Map.empty\<close>
  by simp

lemma app_zero_pheap[simp]:
  \<open>0 \<bullet> x = None\<close>
  by (simp add: zero_pheap.rep_eq)

lift_definition bot_pheap :: \<open>('a,'b) pheap\<close> is \<open>Map.empty\<close>
  by simp

lemma app_bot_pheap[simp]:
  \<open>\<bottom> \<bullet> x = None\<close>
  by (simp add: bot_pheap.rep_eq)

lemma bot_pheap_eq_zero_pheap:
  \<open>(\<bottom> :: ('a,'b) pheap) = 0\<close>
  by (simp add: zero_pheap.abs_eq bot_pheap.abs_eq)

lemma le_iff_sepadd_helper:
  fixes a b :: \<open>('a,'b) pheap\<close>
  shows \<open>(a \<le> b) = (\<exists>c. a ## c \<and> b = a + c)\<close>
  apply (rule iffI)
   apply (clarsimp simp add: pheap_le_iff pheap_eq_iff disjoint_pheap_def less_eq_pheap_def
      less_eq_perm_def split: option.splits)
   apply (rule_tac x=\<open>Abs_pheap (\<lambda>x. a \<bullet> x \<oslash>\<^sub>p b \<bullet> x)\<close> in exI)
   apply simp
   apply (force simp add: compl_perm_def plus_perm_def app_pheap_bounded_permD split: option.splits)
  apply (force simp add: pheap_le_iff less_eq_perm_def plus_perm_def app_pheap_bounded_permD
      split: option.splits)
  done

instance
  apply standard
           apply (clarsimp simp add: less_eq_pheap_def less_eq_perm_def pheap_eq_iff)
           apply (rename_tac a b x)
           apply (case_tac \<open>app_pheap a x\<close>; case_tac \<open>app_pheap b x\<close>; force)
          apply (simp add: less_eq_pheap_def; fail)
         apply (force simp add: disjoint_pheap_def)
        apply (force simp add: disjoint_pheap_def)
  subgoal
    apply (clarsimp simp add: disjoint_pheap_def plus_perm_def split: option.splits)
    apply (drule_tac x=x in spec)+
    apply (meson add_le_cancel_left app_pheap_bounded_permD(1) le_add_same_cancel1 order_trans)
    done
  subgoal
    apply (clarsimp simp add: disjoint_pheap_def)
    apply (drule_tac x=x in spec)+
    apply (simp add: plus_perm_def split: option.splits prod.splits)
    done
     apply (simp add: le_iff_sepadd_helper; fail)
  subgoal
    apply (clarsimp simp add: pheap_eq_iff plus_perm_def split: option.splits)
    apply (simp add: add.commute disjoint_pheap.rep_eq)
    done
  subgoal
    apply (clarsimp simp add: disjoint_pheap_def pheap_eq_iff)
    apply (force simp add: plus_perm_def eq_iff min_le_iff_disj split: option.splits)
    done
  apply (simp add: pheap_eq_iff; fail)
  done

end


instantiation pheap :: (type,type) cancel_seplogic
begin

instance
  apply standard
      apply (clarsimp simp add: pheap_eq_iff plus_perm_def minus_perm_def split: option.splits)
  sorry
(*
        apply (fastforce dest: map_add_comm simp add: disjoint_pheap_def plus_pheap_def)
           apply (simp add: plus_pheap_def zero_pheap_def Abs_pheap_inverse app_pheap_inverse; fail)
      apply (simp add: plus_pheap_def minus_pheap_def disjoint_pheap_def
      Abs_pheap_inverse app_pheap_inverse
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
*)

end


lift_definition restrict_pheap :: \<open>('a,'b) pheap \<Rightarrow> 'a set \<Rightarrow> ('a,'b) pheap\<close>
  (infixl \<open>|`\<^sub>p\<close> 110) is \<open>(|`)\<close>
  by (simp, metis domI domIff restrict_in restrict_out)

lemma restrict_app_pheap_iff[simp]:
  \<open>(a |`\<^sub>p A) \<bullet> x = (if x \<in> A then a \<bullet> x else None)\<close>
  by (simp add: restrict_pheap.rep_eq)

(* not true:
lemma restrict_pheap_un_eq: \<open>h |`\<^sub>p (A \<union> B) = h |`\<^sub>p A + h |`\<^sub>p B\<close>
  by (simp add: pheap_eq_iff)
*)

lemma restrict_pheap_add_eq[simp]:
  \<open>(a + b) |`\<^sub>p A = a |`\<^sub>p A + b |`\<^sub>p A\<close>
  by (simp add: pheap_eq_iff)

lemma dom_restrict_pheap_eq[simp]: \<open>dom_pheap (h |`\<^sub>p A) = dom_pheap h \<inter> A\<close>
  by (simp add: dom_pheap.rep_eq restrict_pheap.rep_eq)

lemma dom_plus_pheap_eq[simp]: \<open>dom_pheap (h1 + h2) = dom_pheap h1 \<union> dom_pheap h2\<close>
  by (simp add: dom_pheap.rep_eq plus_perm_def dom_def set_eq_iff split: option.splits)

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
      Abs_pheap_inverse app_pheap_inverse map_restrict_un_eq[symmetric] dom_subset_restrict_eq)

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