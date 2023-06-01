theory Stabilisation
  imports SepLogic
begin

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


context sep_alg
begin

lemma swstable_sepconj_semidistrib:
  fixes P Q :: \<open>'a \<Rightarrow> bool\<close>
  assumes rely_additivity_of_update:
    \<open>\<And>a1 a2 b. a1 ## a2 \<Longrightarrow> R\<^sup>*\<^sup>* (a1 + a2) b \<Longrightarrow>
        \<exists>b1 b2. b1 ## b2 \<and> b = b1 + b2 \<and> R\<^sup>*\<^sup>* a1 b1 \<and> R\<^sup>*\<^sup>* a2 b2\<close>
  shows \<open>\<lfloor> P \<rfloor>\<^bsub>R\<^esub> \<^emph> \<lfloor> Q \<rfloor>\<^bsub>R\<^esub> \<le> \<lfloor> P \<^emph> Q \<rfloor>\<^bsub>R\<^esub>\<close>
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


class stable_sep_alg = halving_sep_alg + disjoint_parts_perm_alg +
  fixes stableres :: \<open>'a \<Rightarrow> 'a\<close>
  assumes stableres_concave: \<open>a ## b \<Longrightarrow> stableres a + stableres b \<le> stableres (a + b)\<close>
  assumes stableres_idem[simp]: \<open>stableres (stableres a) = stableres a\<close>
  assumes stableres_subres: \<open>stableres a \<le> a\<close>
  assumes stableres_add_right_mono: \<open>a ## c \<Longrightarrow> b ## c \<Longrightarrow> stableres a \<le> stableres b \<Longrightarrow> stableres (a + c) \<le> stableres (b + c)\<close>
begin

lemma stableres_mono: \<open>a \<le> b \<Longrightarrow> stableres a \<le> stableres b\<close>
  unfolding le_iff_sepadd
  by (metis disjoint_preservation disjoint_symm order.trans le_iff_sepadd stableres_concave
      stableres_subres)

lemma stableres_add_left_mono:
  \<open>a ## b \<Longrightarrow> a ## c \<Longrightarrow> stableres b \<le> stableres c \<Longrightarrow> stableres (a + b) \<le> stableres (a + c)\<close>
  by (metis disjoint_symm partial_add_commute stableres_add_right_mono)


lemma stableres_disjoint_preservation:
  \<open>a ## b \<Longrightarrow> stableres a ## stableres b\<close>
  by (meson disjoint_preservation disjoint_symm stableres_subres)

lemma stableres_plus_idem:
  \<open>stableres a ## stableres b \<Longrightarrow> stableres (stableres a + stableres b) = stableres a + stableres b\<close>
  by (metis antisym_conv stableres_concave stableres_idem stableres_subres)


lemma stableres_zero[simp]: \<open>stableres 0 = 0\<close>
  using le_zero_eq stableres_subres by blast


text \<open> this shouldn't be true. There are interesting models where it isn't true. \<close>
lemma stableres_plus_eq: \<open>stableres (a + b) = stableres a + stableres b\<close>
  nitpick
  oops


abbreviation(input) stablerel :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> where
  \<open>stablerel a b \<equiv> stableres a \<le> stableres b\<close>


lemma stablerel_reflp:
  \<open>reflp stablerel\<close>
  by (simp add: reflpI)

lemma stablerel_transp:
  \<open>transp stablerel\<close>
  using order.trans transp_def by blast

lemma stablerel_transclp[simp]:
  \<open>stablerel\<^sup>*\<^sup>* = stablerel\<close>
  by (metis stablerel_reflp stablerel_transp rtransp_rel_is_rtransclp)


lemma stablerel_additivity_of_update:
  assumes
    \<open>a1 ## a2\<close>
    \<open>stablerel (a1 + a2) b\<close> 
  shows \<open>\<exists>b1 b2. b1 ## b2 \<and> b = b1 + b2 \<and> stablerel a1 b1 \<and> stablerel a2 b2\<close>
proof -
  obtain c where c_props:
    \<open>stableres (a1 + a2) = stableres a1 + stableres a2 + c\<close>
    \<open>stableres a1 + stableres a2 ## c\<close>
    using assms(1)
    using le_iff_sepadd stableres_concave by blast
  obtain d where d_props:
    \<open>stableres b = stableres a1 + stableres a2 + c + d\<close>
    \<open>stableres a1 + stableres a2 + c ## d\<close>
    using assms c_props
    by (clarsimp simp add: le_iff_sepadd)
  then obtain e where e_props:
    \<open>b = stableres a1 + stableres a2 + c + d + e\<close>
    \<open>stableres a1 + stableres a2 + c + d ## e\<close>
    using le_iff_sepadd stableres_subres
    by metis
  
  have disjoint_props:
    \<open>stableres a1 ## stableres a2 \<and>
      stableres a1 ## c \<and> stableres a2 ## c \<and>
      stableres a1 ## d \<and> stableres a2 ## d \<and> c ## d \<and>
      stableres a1 ## e \<and> stableres a2 ## e \<and> c ## e \<and> d ## e \<and>
      stableres a1 ## half c \<and> stableres a2 ## half c \<and>
      stableres a1 ## half d \<and> stableres a2 ## half d \<and> half c ## half d \<and>
      stableres a1 ## half e \<and> stableres a2 ## half e \<and> half c ## half e \<and> half d ## half e \<and>
      half c ## half c \<and> half d ## half d \<and> half e ## half e\<close>
    using c_props(2) d_props(2) e_props(2) assms(1)
    by (force simp add: stableres_disjoint_preservation disjointness_left_plus_eq
        disjointness_right_plus_eq half_disjoint_preservation_left half_disjoint_preservation_right
        half_self_disjoint)
  moreover then have
    \<open>b = stableres a1 + half c + half d + half e + (stableres a2 + half c + half d + half e)\<close>
  proof -
    have \<open>b = stableres a1 + stableres a2 + c + d + e\<close>
      using d_props e_props by presburger
    also have \<open>... = (stableres a1 + stableres a2 + (half c + half c)) + (half d + half d) + (half e + half e)\<close>
      by (simp add: half_additive_split)
    also have \<open>... = (stableres a1 + half c + half d + half e) + (stableres a2 + half c + half d + half e)\<close>
      using disjoint_props
      by (simp add: disjointness_left_plusI' disjointness_right_plusI' partial_add_double_assoc2)
    finally show ?thesis .
qed
  ultimately show ?thesis
    using assms(1)
    apply -
    apply (rule_tac x=\<open>stableres a1 + half c + half d + half e\<close> in exI)
    apply (rule_tac x=\<open>stableres a2 + half c + half d + half e\<close> in exI)
    apply (intro conjI)
       apply (fastforce intro!: disjointness_left_plusI disjointness_right_plusI
        simp add: disjoint_symm_iff)
      apply force
     apply (metis disjoint_symm disjointness_right_plus_eq le_plus partial_add_assoc stableres_idem stableres_mono)
    apply (metis disjoint_symm disjointness_right_plus_eq le_plus partial_add_assoc stableres_idem stableres_mono)
    done
qed

abbreviation swstablerel :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> (\<open>\<lfloor> _ \<rfloor>\<close>) where
  \<open>\<lfloor> P \<rfloor> \<equiv> \<lfloor> P \<rfloor>\<^bsub>stablerel\<^esub>\<close>

abbreviation wsstablerel :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> (\<open>\<lceil> _ \<rceil>\<close>) where
  \<open>\<lceil> P \<rceil> \<equiv> \<lceil> P \<rceil>\<^bsub>stablerel\<^esub>\<close>

lemma swstablerel_sepconj_semidistrib:
  fixes P Q :: \<open>'a \<Rightarrow> bool\<close>
  shows \<open>\<lfloor> P \<rfloor> \<^emph> \<lfloor> Q \<rfloor> \<le> \<lfloor> P \<^emph> Q \<rfloor>\<close>
  by (rule swstable_sepconj_semidistrib, simp add: stablerel_additivity_of_update)

lemma wsstablerel_sepconj_semidistrib:
  fixes P Q :: \<open>'a \<Rightarrow> bool\<close>
  shows \<open>\<lceil> P \<^emph> Q \<rceil> \<le> \<lceil> P \<rceil> \<^emph> \<lceil> Q \<rceil>\<close>
  by (rule wsstable_sepconj_semidistrib, simp add: stablerel_additivity_of_update)


end

end