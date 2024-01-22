theory Stabilisation
  imports SepLogic
begin

section \<open>Stabilisation\<close>

(* strongest weaker stable predicate *) (* \<box>\<^sup>\<rightarrow> *)
definition swstable
  :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close>
  ("\<lfloor> _ \<rfloor>\<^bsub>_\<^esub>" [0,0] 90)
  where
  \<open>\<lfloor> P \<rfloor>\<^bsub>R\<^esub> \<equiv> \<lambda>s. \<forall>s'. R\<^sup>*\<^sup>* s s' \<longrightarrow> P s'\<close>

(* weakest stronger stable predicate *) (* \<diamondsuit>\<^sup>\<leftarrow> *)
definition wsstable
  :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close>
  ("\<lceil> _ \<rceil>\<^bsub>_\<^esub>" [0,0] 90)
  where
  \<open>\<lceil> P \<rceil>\<^bsub>R\<^esub> \<equiv> \<lambda>s'. \<exists>s. R\<^sup>*\<^sup>* s s' \<and> P s\<close>

subsection \<open>basic logical properties\<close>

lemma swstable_weaker[intro!]: \<open>\<lfloor> P \<rfloor>\<^bsub>R\<^esub> \<le> P\<close>
  by (force simp add: swstable_def)

lemma wsstable_stronger[intro!]: \<open>P \<le> \<lceil> P \<rceil>\<^bsub>R\<^esub>\<close>
  by (force simp add: wsstable_def)

lemma wsstable_strongerI[intro!]:
  \<open>P s \<Longrightarrow> R\<^sup>*\<^sup>* s s' \<Longrightarrow> (\<lceil> P \<rceil>\<^bsub>R\<^esub>) s'\<close>
  by (force simp add: wsstable_def)

lemma wsstable_step:
  \<open>R s s' \<Longrightarrow> (\<lceil> P \<rceil>\<^bsub>R\<^esub>) s \<Longrightarrow> (\<lceil> P \<rceil>\<^bsub>R\<^esub>) s'\<close>
  by (metis rtranclp.rtrancl_into_rtrancl wsstable_def)

lemma swstable_step:
  \<open>R s s' \<Longrightarrow> (\<lfloor> P \<rfloor>\<^bsub>R\<^esub>) s \<Longrightarrow> (\<lfloor> P \<rfloor>\<^bsub>R\<^esub>) s'\<close>
  by (simp add: converse_rtranclp_into_rtranclp swstable_def)


lemma implies_swstableD:
  \<open>p \<le> \<lfloor> q \<rfloor>\<^bsub>r\<^esub> \<Longrightarrow> r\<^sup>*\<^sup>* s s' \<Longrightarrow> p s \<Longrightarrow> q s'\<close>
  by (simp add: swstable_def le_fun_def)

lemma wsstable_impliesD:
  \<open>\<lceil> p \<rceil>\<^bsub>r\<^esub> \<le> q \<Longrightarrow> r\<^sup>*\<^sup>* s s' \<Longrightarrow> p s \<Longrightarrow> q s'\<close>
  by (force simp add: wsstable_def le_fun_def)


lemma wsstable_weaker_iff_swstable_stronger:
  \<open>p \<le> \<lfloor> p \<rfloor>\<^bsub>R\<^esub> \<longleftrightarrow> \<lceil> p \<rceil>\<^bsub>R\<^esub> \<le> p\<close>
  by (force simp add: wsstable_def swstable_def le_fun_def)

definition stable :: \<open>('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool\<close> where
  \<open>stable R p \<equiv> \<lfloor> p \<rfloor>\<^bsub>R\<^esub> = p\<close>

lemma stable_eq:
  \<open>stable R p \<longleftrightarrow> p \<le> \<lfloor> p \<rfloor>\<^bsub>R\<^esub>\<close>
  by (simp add: stable_def antisym swstable_weaker)

lemma stable_eq2:
  \<open>stable R p \<longleftrightarrow> \<lceil> p \<rceil>\<^bsub>R\<^esub> \<le> p\<close>
  by (simp add: stable_eq wsstable_weaker_iff_swstable_stronger)

lemma stable_def2:
  \<open>stable R p = (\<lceil> p \<rceil>\<^bsub>R\<^esub> = p)\<close>
  by (simp add: antisym stable_eq2 wsstable_stronger)

lemmas stableD[dest] = iffD1[OF stable_eq]
lemmas stableD2[dest] = iffD1[OF stable_eq2]

lemmas stableI[intro] = iffD2[OF stable_eq]
lemmas stableI2[intro] = iffD2[OF stable_eq2]

lemma stable_iff:
  \<open>stable r p \<longleftrightarrow> (\<forall>x y. r\<^sup>*\<^sup>* x y \<longrightarrow> p x \<longrightarrow> p y)\<close>
  by (metis predicate1I stableI stable_def2 swstable_def wsstable_strongerI)

lemma stable_antimono:
  \<open>r1 \<le> r2 \<Longrightarrow> stable r2 p \<Longrightarrow> stable r1 p\<close>
  by (simp add: stable_def swstable_def fun_eq_iff)
    (metis rev_predicate2D rtranclp.rtrancl_refl rtranclp_mono)

lemmas stable_antimono'[dest] = stable_antimono[rotated]

subsection \<open>(semi)distributivity properties\<close>

lemma swstable_conj_distrib: \<open>\<lfloor> P \<sqinter> Q \<rfloor>\<^bsub>R\<^esub> = \<lfloor> P \<rfloor>\<^bsub>R\<^esub> \<sqinter> \<lfloor> Q \<rfloor>\<^bsub>R\<^esub>\<close>
  by (force simp add: swstable_def)

lemma swstable_disj_semidistrib: \<open>\<lfloor> P \<rfloor>\<^bsub>R\<^esub> \<squnion> \<lfloor> Q \<rfloor>\<^bsub>R\<^esub> \<le> \<lfloor> P \<squnion> Q \<rfloor>\<^bsub>R\<^esub>\<close>
  by (force simp add: swstable_def)

lemma wsstable_disj_distrib: \<open>\<lceil> P \<squnion> Q \<rceil>\<^bsub>R\<^esub> = \<lceil> P \<rceil>\<^bsub>R\<^esub> \<squnion> \<lceil> Q \<rceil>\<^bsub>R\<^esub>\<close>
  by (force simp add: wsstable_def)

lemma wsstable_conj_semidistrib: \<open>\<lceil> P \<sqinter> Q \<rceil>\<^bsub>R\<^esub> \<le> \<lceil> P \<rceil>\<^bsub>R\<^esub> \<sqinter> \<lceil> Q \<rceil>\<^bsub>R\<^esub>\<close>
  by (force simp add: wsstable_def)

subsection \<open>Rely Monotonicity\<close>

lemma swstable_rely_antimono: \<open>R \<le> S \<Longrightarrow> \<lfloor> P \<rfloor>\<^bsub>S\<^esub> \<le> \<lfloor> P \<rfloor>\<^bsub>R\<^esub>\<close>
  using mono_rtranclp
  by (force simp add: swstable_def le_fun_def)

lemma wsstable_rely_le_mono:
  \<open>R \<le> S \<Longrightarrow> \<lfloor> P \<rfloor>\<^bsub>R\<^esub> \<le> Q \<Longrightarrow> \<lfloor> P \<rfloor>\<^bsub>S\<^esub> \<le> Q\<close>
  by (metis order_trans swstable_rely_antimono)

lemma wsstable_rely_ge_antimono:
  \<open>R \<le> S \<Longrightarrow> P \<le> \<lfloor> Q \<rfloor>\<^bsub>S\<^esub> \<Longrightarrow> P \<le> \<lfloor> Q \<rfloor>\<^bsub>R\<^esub>\<close>
  by (metis order_trans swstable_rely_antimono)

lemmas wsstable_rely_le_monoD = wsstable_rely_le_mono[rotated]
lemmas wsstable_rely_ge_antimonoD = wsstable_rely_ge_antimono[rotated]

lemma wsstable_rely_mono: \<open>R \<le> S \<Longrightarrow> \<lceil> P \<rceil>\<^bsub>R\<^esub> \<le> \<lceil> P \<rceil>\<^bsub>S\<^esub>\<close>
  using mono_rtranclp
  by (force simp add: wsstable_def le_fun_def)

lemma wsstable_rely_le_antimono:
  \<open>R \<le> S \<Longrightarrow> \<lceil> P \<rceil>\<^bsub>S\<^esub> \<le> Q \<Longrightarrow> \<lceil> P \<rceil>\<^bsub>R\<^esub> \<le> Q\<close>
  by (meson order_trans wsstable_rely_mono)

lemma wsstable_rely_ge_mono:
  \<open>R \<le> S \<Longrightarrow> P \<le> \<lceil> Q \<rceil>\<^bsub>R\<^esub> \<Longrightarrow> P \<le> \<lceil> Q \<rceil>\<^bsub>S\<^esub>\<close>
  by (meson order_trans wsstable_rely_mono)

lemmas wsstable_rely_le_antimonoD = wsstable_rely_le_antimono[rotated]
lemmas wsstable_rely_ge_monoD = wsstable_rely_ge_mono[rotated]

subsection \<open>nested stabilisation\<close>

lemma wsstable_absorb[simp]:
  assumes \<open>R\<^sup>*\<^sup>* = Ra\<^sup>*\<^sup>* OO Rb\<^sup>*\<^sup>*\<close>
  shows \<open>\<lceil> \<lceil> P \<rceil>\<^bsub>Ra\<^esub> \<rceil>\<^bsub>Rb\<^esub> = \<lceil> P \<rceil>\<^bsub>R\<^esub>\<close>
  by (force simp add: assms wsstable_def relcompp_apply fun_eq_iff)

lemma wsstable_absorb1[simp]: \<open>R \<le> R' \<Longrightarrow> \<lceil> \<lceil> P \<rceil>\<^bsub>R\<^esub> \<rceil>\<^bsub>R'\<^esub> = \<lceil> P \<rceil>\<^bsub>R'\<^esub>\<close>
  by (simp add: rel_le_rtranscp_relcompp_absorb)

lemma wsstable_absorb2[simp]: \<open>R \<le> R' \<Longrightarrow> \<lceil> \<lceil> P \<rceil>\<^bsub>R'\<^esub> \<rceil>\<^bsub>R\<^esub> = \<lceil> P \<rceil>\<^bsub>R'\<^esub>\<close>
  by (simp add: rel_le_rtranscp_relcompp_absorb)

lemma swstable_absorb[simp]:
  \<open>R\<^sup>*\<^sup>* = Rb\<^sup>*\<^sup>* OO Ra\<^sup>*\<^sup>* \<Longrightarrow> \<lfloor> \<lfloor> P \<rfloor>\<^bsub>Ra\<^esub> \<rfloor>\<^bsub>Rb\<^esub> = \<lfloor> P \<rfloor>\<^bsub>R\<^esub>\<close>
  by (force simp add: swstable_def relcompp_apply imp_ex imp_conjL fun_eq_iff)

lemma swstable_absorb1[simp]: \<open>R \<le> R' \<Longrightarrow> \<lfloor> \<lfloor> P \<rfloor>\<^bsub>R\<^esub> \<rfloor>\<^bsub>R'\<^esub> = \<lfloor> P \<rfloor>\<^bsub>R'\<^esub>\<close>
  by (simp add: rel_le_rtranscp_relcompp_absorb)

lemma swstable_absorb2[simp]: \<open>R \<le> R' \<Longrightarrow> \<lfloor> \<lfloor> P \<rfloor>\<^bsub>R'\<^esub> \<rfloor>\<^bsub>R\<^esub> = \<lfloor> P \<rfloor>\<^bsub>R'\<^esub>\<close>
  by (simp add: rel_le_rtranscp_relcompp_absorb)

lemma wsstable_swstable_absorb[simp]: \<open>R \<le> R' \<Longrightarrow> \<lceil> \<lfloor> P \<rfloor>\<^bsub>R'\<^esub> \<rceil>\<^bsub>R\<^esub> = \<lfloor> P \<rfloor>\<^bsub>R'\<^esub>\<close>
  unfolding wsstable_def swstable_def
  by (metis (opaque_lifting) predicate2D rtranclp.rtrancl_refl rtranclp_trans rtranclp_mono)

lemma swstable_wsstable_absorb[simp]: \<open>R \<le> R' \<Longrightarrow> \<lfloor> \<lceil> P \<rceil>\<^bsub>R'\<^esub> \<rfloor>\<^bsub>R\<^esub> = \<lceil> P \<rceil>\<^bsub>R'\<^esub>\<close>
  unfolding wsstable_def swstable_def
  by (metis (opaque_lifting) predicate2D rtranclp.rtrancl_refl rtranclp_trans rtranclp_mono)

paragraph \<open> swstable preserves precision \<close>

lemma swstable_preserves_precise[dest]:
  \<open>precise p \<Longrightarrow> precise (\<lfloor> p \<rfloor>\<^bsub>r\<^esub>)\<close>
  by (clarsimp simp add: precise_def swstable_def)

section \<open> Properties of stabilisation in a perm algebra \<close>

context perm_alg
begin

subsection \<open> Semidistributivity \<close>

paragraph \<open> Preservation of addition over a relation \<close>

text \<open> This is probably too strong a property to be useful. It essentially requires a rely
      relating two states to also relate all subparts of those states in some consistent manner.
      Compare this approach with the rely splitting approach later. \<close>

definition
  \<open>rel_add_preserve r \<equiv>
    (\<forall>h1 h2 s.
      h1 ## h2 \<longrightarrow>
      r\<^sup>=\<^sup>= (h1 + h2) s \<longrightarrow>
      (\<exists>s1 s2. s1 ## s2 \<and> s = s1 + s2 \<and> r\<^sup>=\<^sup>= h1 s1 \<and> r\<^sup>=\<^sup>= h2 s2))\<close>

definition
  \<open>weak_rel_add_preserve r \<equiv>
    \<forall>p q.
      (\<forall>h1 h2 s.
        r\<^sup>=\<^sup>= (h1 + h2) s \<longrightarrow>
        h1 ## h2 \<longrightarrow>
        p h1 \<longrightarrow>
        q h2 \<longrightarrow>
        (\<exists>s1 s2. s1 ## s2 \<and> s = s1 + s2 \<and> (\<exists>h1'. r\<^sup>=\<^sup>= h1' s1 \<and> p h1') \<and> (\<exists>h2'. r\<^sup>=\<^sup>= h2' s2 \<and> q h2')))\<close>

lemma rel_add_preserve_impl_weak[intro,dest]:
  \<open>rel_add_preserve r \<Longrightarrow> weak_rel_add_preserve r\<close>
  unfolding weak_rel_add_preserve_def rel_add_preserve_def
  by meson

paragraph \<open> Semidistributivity \<close>

lemma swstable_sepconj_semidistrib:
  fixes R :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
  assumes \<open>rel_add_preserve (R\<^sup>*\<^sup>*)\<close>
  shows \<open>\<lfloor> P \<rfloor>\<^bsub>R\<^esub> \<^emph> \<lfloor> Q \<rfloor>\<^bsub>R\<^esub> \<le> \<lfloor> P \<^emph> Q \<rfloor>\<^bsub>R\<^esub>\<close>
  using assms
  unfolding rel_add_preserve_def swstable_def sepconj_def
  by blast

lemma wsstable_sepconj_semidistrib:
  fixes R :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
  assumes \<open>weak_rel_add_preserve (R\<^sup>*\<^sup>*)\<close>
  shows \<open>\<lceil> P \<^emph> Q \<rceil>\<^bsub>R\<^esub> \<le> \<lceil> P \<rceil>\<^bsub>R\<^esub> \<^emph> \<lceil> Q \<rceil>\<^bsub>R\<^esub>\<close>
  using assms
  unfolding weak_rel_add_preserve_def wsstable_def sepconj_def
  by force

paragraph \<open> Semidistributivity by rely merging \<close>

definition
  \<open>rely_merge r1 r2 \<equiv> (\<lambda>h s. \<forall>h1 h2. h = h1 + h2 \<longrightarrow> h1 ## h2 \<longrightarrow> ((r1\<^sup>*\<^sup>* h1) \<^emph> (r2\<^sup>*\<^sup>* h2)) s)\<close>

lemma rely_merge_reflp: \<open>reflp (rely_merge r1 r2)\<close>
  by (force simp add: reflp_def rely_merge_def sepconj_def)

lemma rely_merge_transp: \<open>transp (rely_merge r1 r2)\<close>
  by (force simp add: transp_def rely_merge_def sepconj_def)

lemma rely_merge_rtranscl[simp]: \<open>(rely_merge r1 r2)\<^sup>*\<^sup>* = rely_merge r1 r2\<close>
  by (simp add: rely_merge_reflp rely_merge_transp rtransp_rel_is_rtransclp)

lemma swstable_sepconj_semidistrib_forwards:
  \<open>\<lfloor> P \<rfloor>\<^bsub>R1\<^esub> \<^emph> \<lfloor> Q \<rfloor>\<^bsub>R2\<^esub> \<le> \<lfloor> P \<^emph> Q \<rfloor>\<^bsub>rely_merge R1 R2\<^esub>\<close>
  apply (clarsimp simp add: swstable_def sepconj_def fun_eq_iff)
  apply (simp add: rely_merge_def sepconj_def)
  apply blast
  done

lemma wsstable_sepconj_semidistrib_backwards:
  \<open>\<lceil> P \<^emph> Q \<rceil>\<^bsub>rely_merge R1 R2\<^esub> \<le> \<lceil> P \<rceil>\<^bsub>R1\<^esub> \<^emph> \<lceil> Q \<rceil>\<^bsub>R2\<^esub>\<close>
  apply (clarsimp simp add: wsstable_def sepconj_def fun_eq_iff)
  apply (simp add: rely_merge_def sepconj_def)
  apply blast
  done

end


class stable_sep_alg = halving_sep_alg +
  fixes stableres :: \<open>'a \<Rightarrow> 'a\<close>
  assumes stableres_concave[intro]: \<open>a ## b \<Longrightarrow> stableres a + stableres b \<le> stableres (a + b)\<close>
  assumes stableres_idem[simp]: \<open>stableres (stableres a) = stableres a\<close>
  assumes stableres_subres[intro!]: \<open>stableres a \<le> a\<close>
begin

lemma stableres_mono: \<open>a \<le> b \<Longrightarrow> stableres a \<le> stableres b\<close>
  unfolding le_iff_sepadd
  by (metis disjoint_preservation disjoint_sym order.trans le_iff_sepadd stableres_concave
      stableres_subres)

lemma stableres_disjoint_preservation:
  \<open>a ## b \<Longrightarrow> stableres a ## stableres b\<close>
  by (meson disjoint_preservation disjoint_sym stableres_subres)

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
  using order.trans transp_def by fast

lemma stablerel_eqclp[simp]:
  \<open>stablerel\<^sup>=\<^sup>= = stablerel\<close>
  by (simp add: reflp_ge_eq stablerel_reflp sup.absorb1)

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
    using assms(1) c_props(2)
    apply -
       apply (metis disjoint_add_leftL half_disjoint_preservation_right
        stableres_disjoint_preservation)
      apply (metis disjoint_add_leftR half_disjoint_preservation_right
        stableres_disjoint_preservation)
     apply (metis disjoint_add_rightR disjoint_add_right_commute disjoint_sym_iff
        partial_add_commute stableres_disjoint_preservation)
    apply (meson disjoint_add_leftR disjoint_add_swap2 half_disjoint_distribR
        stableres_disjoint_preservation)
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

abbreviation(input) wsstablerel_temporal :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> (\<open>\<diamond>\<^sup>- _\<close> [81] 80) where
  \<open>\<diamond>\<^sup>- P \<equiv> \<lceil> P \<rceil>\<^bsub>stablerel\<^esub>\<close>

abbreviation(input) swstablerel_temporal :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> (\<open>\<box> _\<close> [81] 80) where
  \<open>\<box> P \<equiv> \<lfloor> P \<rfloor>\<^bsub>stablerel\<^esub>\<close>

lemma swstablerel_sepconj_semidistrib:
  fixes P Q :: \<open>'a \<Rightarrow> bool\<close>
  shows \<open>\<lfloor> P \<rfloor> \<^emph> \<lfloor> Q \<rfloor> \<le> \<lfloor> P \<^emph> Q \<rfloor>\<close>
  by (rule swstable_sepconj_semidistrib, simp add: rel_add_preserve_def stablerel_additivity_of_update)

lemma wsstablerel_sepconj_semidistrib:
  fixes P Q :: \<open>'a \<Rightarrow> bool\<close>
  shows \<open>\<lceil> P \<^emph> Q \<rceil> \<le> \<lceil> P \<rceil> \<^emph> \<lceil> Q \<rceil>\<close>
  by (rule wsstable_sepconj_semidistrib[OF rel_add_preserve_impl_weak])
    (simp add: rel_add_preserve_def stablerel_additivity_of_update)

end


lemma swstable_necessitation: \<open>\<top> \<le> P \<Longrightarrow> \<top> \<le> \<box> P\<close>
  by (metis order_eq_refl swstable_wsstable_absorb top.extremum_uniqueI wsstable_stronger)

lemma swstable_impl_distrib: \<open>\<box>(P \<leadsto> Q) \<sqinter> \<box> P \<le> \<box> Q\<close>
  by (metis (no_types, lifting) double_compl inf.absorb1 inf.orderI inf_idem sup_neg_inf
      swstable_conj_distrib implies_def)

lemma wsstabledual_necessitation: \<open>\<top> \<le> P \<Longrightarrow> \<top> \<le> - (\<diamond>\<^sup>- (- P))\<close>
  by (metis (mono_tags, lifting) double_compl order_antisym predicate1I top_apply uminus_apply
      wsstable_def wsstable_stronger)

lemma wsstabledual_impl_distrib: \<open>\<diamond>\<^sup>- Q \<le> \<diamond>\<^sup>-(-P \<sqinter> Q) \<squnion> \<diamond>\<^sup>-(P)\<close>
  by (force simp add: le_fun_def wsstable_def)

instantiation prod :: (stable_sep_alg,stable_sep_alg) stable_sep_alg
begin

definition stableres_prod :: \<open>'a \<times> 'b \<Rightarrow> 'a \<times> 'b\<close> where
  \<open>stableres_prod \<equiv> map_prod stableres stableres\<close>

definition half_prod :: \<open>'a \<times> 'b \<Rightarrow> 'a \<times> 'b\<close> where
  \<open>half_prod \<equiv> map_prod half half\<close>

instance
  apply standard
       apply (simp add: half_prod_def half_additive_split; fail)
      apply (simp add: half_prod_def half_self_disjoint; fail)
     apply (simp add: half_prod_def half_sepadd_distrib; fail)
    apply (simp add: stableres_prod_def stableres_concave; fail)
   apply (clarsimp simp add: stableres_prod_def; fail)
  apply (simp add: stableres_prod_def stableres_subres; fail)
  done

end

end