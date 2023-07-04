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


class stable_sep_alg = halving_sep_alg +
  fixes stableres :: \<open>'a \<Rightarrow> 'a\<close>
  assumes stableres_concave: \<open>a ## b \<Longrightarrow> stableres a + stableres b \<le> stableres (a + b)\<close>
  assumes stableres_idem[simp]: \<open>stableres (stableres a) = stableres a\<close>
  assumes stableres_subres: \<open>stableres a \<le> a\<close>
begin

lemma stableres_mono: \<open>a \<le> b \<Longrightarrow> stableres a \<le> stableres b\<close>
  unfolding le_iff_sepadd
  by (metis disjoint_preservation disjoint_symm order.trans le_iff_sepadd stableres_concave
      stableres_subres)

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
    \<open>b = stableres a1 + stableres a2 + c\<close>
    \<open>stableres a1 + stableres a2 ## c\<close>
    using assms
    by (meson order.trans le_iff_sepadd stableres_subres stableres_concave)

  have disjoint_props:
    \<open>stableres a1 ## half c\<close>
    \<open>stableres a2 ## half c\<close>
    \<open>stableres a1 ## stableres a2 + c\<close>
    \<open>stableres a1 + half c ## stableres a2 + half c\<close>
    using  assms(1) c_props(2)
    apply -
    apply (metis disjoint_add_leftL half_disjoint_preservation_right stableres_disjoint_preservation)
    apply (metis disjoint_add_leftR half_disjoint_preservation_right stableres_disjoint_preservation)
    apply (metis disjoint_add_rightR disjoint_add_right_commute disjoint_symm_iff partial_add_commute stableres_disjoint_preservation)
    apply (metis disjoint_add_leftL disjoint_add_commuteL disjoint_add_leftR half_disjoint_distribL partial_add_commute stableres_disjoint_preservation)
    done

  have \<open>b = stableres a1 + half c + (stableres a2 + half c)\<close>
    using assms(1)
    by (metis c_props disjoint_props(1-3) disjoint_add_leftR half_additive_split half_self_disjoint
        partial_add_double_assoc stableres_disjoint_preservation)
  then show ?thesis
    using assms(1)
    apply -
    apply (rule_tac x=\<open>stableres a1 + half c\<close> in exI)
    apply (rule_tac x=\<open>stableres a2 + half c\<close> in exI)
    apply (intro conjI)
       apply (simp add: disjoint_props(4))
      apply force
     apply (metis disjoint_props(1) partial_le_plus stableres_idem stableres_mono)
    apply (metis disjoint_props(2) partial_le_plus stableres_idem stableres_mono)
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


instantiation prod :: (stable_sep_alg,stable_sep_alg) stable_sep_alg
begin

definition stableres_prod :: \<open>'a \<times> 'b \<Rightarrow> 'a \<times> 'b\<close> where
  \<open>stableres_prod \<equiv> map_prod stableres stableres\<close>

definition half_prod :: \<open>'a \<times> 'b \<Rightarrow> 'a \<times> 'b\<close> where
  \<open>half_prod \<equiv> map_prod half half\<close>

instance
  apply standard 
  sorry

end


end