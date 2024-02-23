theory Stabilisation
  imports SepLogicInstances
begin

section \<open>Stabilisation\<close>

(* strongest weaker stable predicate *) (* \<box>\<^sup>\<rightarrow> *)
abbreviation swstable
  :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close>
  ("\<lfloor> _ \<rfloor>\<^bsub>_\<^esub>" [0,0] 90)
  where
  \<open>\<lfloor> P \<rfloor>\<^bsub>R\<^esub> \<equiv> wlp R\<^sup>*\<^sup>* P\<close>

(* weakest stronger stable predicate *) (* \<diamondsuit>\<^sup>\<leftarrow> *)
abbreviation wsstable
  :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close>
  ("\<lceil> _ \<rceil>\<^bsub>_\<^esub>" [0,0] 90)
  where
  \<open>\<lceil> P \<rceil>\<^bsub>R\<^esub> \<equiv> sp R\<^sup>*\<^sup>* P\<close>

subsection \<open> logical properties \<close>

lemma swstable_weaker[intro]: \<open>\<lfloor> P \<rfloor>\<^bsub>R\<^esub> \<le> P\<close>
  by (simp add: wlp_refl_rel_le)

lemma wsstable_stronger[intro]: \<open>P \<le> \<lceil> P \<rceil>\<^bsub>R\<^esub>\<close>
  by (simp add: sp_refl_rel_le)

lemma wsstable_strongerI[intro]:
  \<open>P s \<Longrightarrow> R\<^sup>*\<^sup>* s s' \<Longrightarrow> (\<lceil> P \<rceil>\<^bsub>R\<^esub>) s'\<close>
  by (force simp add: sp_def)

lemma wsstable_step:
  \<open>R s s' \<Longrightarrow> (\<lceil> P \<rceil>\<^bsub>R\<^esub>) s \<Longrightarrow> (\<lceil> P \<rceil>\<^bsub>R\<^esub>) s'\<close>
  by (metis (full_types) rtranclp.simps sp_def)

lemma swstable_step:
  \<open>R s s' \<Longrightarrow> (\<lfloor> P \<rfloor>\<^bsub>R\<^esub>) s \<Longrightarrow> (\<lfloor> P \<rfloor>\<^bsub>R\<^esub>) s'\<close>
  by (simp add: converse_rtranclp_into_rtranclp wlp_def)

definition stable :: \<open>('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool\<close> where
  \<open>stable R p \<equiv> \<lfloor> p \<rfloor>\<^bsub>R\<^esub> = p\<close>

lemma stable_eq:
  \<open>stable R p \<longleftrightarrow> p \<le> \<lfloor> p \<rfloor>\<^bsub>R\<^esub>\<close>
  by (simp add: stable_def antisym swstable_weaker)

lemma stable_eq2:
  \<open>stable R p \<longleftrightarrow> \<lceil> p \<rceil>\<^bsub>R\<^esub> \<le> p\<close>
  by (simp add: stable_eq wlp_weaker_iff_sp_stronger)

lemma stable_def2:
  \<open>stable R p = (\<lceil> p \<rceil>\<^bsub>R\<^esub> = p)\<close>
  by (simp add: antisym stable_eq2 wsstable_stronger)

lemmas stableD[dest] = iffD1[OF stable_eq]
lemmas stableD2[dest] = iffD1[OF stable_eq2]

lemmas stableI[intro] = iffD2[OF stable_eq]
lemmas stableI2[intro] = iffD2[OF stable_eq2]

lemma stable_iff:
  \<open>stable r p \<longleftrightarrow> (\<forall>x y. r\<^sup>*\<^sup>* x y \<longrightarrow> p x \<longrightarrow> p y)\<close>
  by (force simp add: stable_eq2 sp_def le_fun_def)

lemma stable_antimono:
  \<open>r1 \<le> r2 \<Longrightarrow> stable r2 p \<Longrightarrow> stable r1 p\<close>
  by (metis (full_types) mono_rtranclp predicate2D stable_iff)

lemmas stable_antimono'[dest] = stable_antimono[rotated]

subsection \<open>Rely Monotonicity\<close>

lemma swstable_rely_antimono: \<open>R \<le> S \<Longrightarrow> \<lfloor> P \<rfloor>\<^bsub>S\<^esub> \<le> \<lfloor> P \<rfloor>\<^bsub>R\<^esub>\<close>
  by (simp add: rtranclp_mono wlp_rel_antimono)

lemma wsstable_rely_le_mono:
  \<open>R \<le> S \<Longrightarrow> \<lfloor> P \<rfloor>\<^bsub>R\<^esub> \<le> Q \<Longrightarrow> \<lfloor> P \<rfloor>\<^bsub>S\<^esub> \<le> Q\<close>
  by (meson order_trans swstable_rely_antimono)

lemma wsstable_rely_ge_antimono:
  \<open>R \<le> S \<Longrightarrow> P \<le> \<lfloor> Q \<rfloor>\<^bsub>S\<^esub> \<Longrightarrow> P \<le> \<lfloor> Q \<rfloor>\<^bsub>R\<^esub>\<close>
  by (metis order_trans swstable_rely_antimono)

lemmas wsstable_rely_le_monoD = wsstable_rely_le_mono[rotated]
lemmas wsstable_rely_ge_antimonoD = wsstable_rely_ge_antimono[rotated]

lemma wsstable_rely_mono: \<open>R \<le> S \<Longrightarrow> \<lceil> P \<rceil>\<^bsub>R\<^esub> \<le> \<lceil> P \<rceil>\<^bsub>S\<^esub>\<close>
  by (simp add: rtranclp_mono wsstable_rel_mono)

lemma wsstable_rely_le_antimono:
  \<open>R \<le> S \<Longrightarrow> \<lceil> P \<rceil>\<^bsub>S\<^esub> \<le> Q \<Longrightarrow> \<lceil> P \<rceil>\<^bsub>R\<^esub> \<le> Q\<close>
  by (meson order_trans wsstable_rely_mono)

lemma wsstable_rely_ge_mono:
  \<open>R \<le> S \<Longrightarrow> P \<le> \<lceil> Q \<rceil>\<^bsub>R\<^esub> \<Longrightarrow> P \<le> \<lceil> Q \<rceil>\<^bsub>S\<^esub>\<close>
  by (meson order_trans wsstable_rely_mono)

lemmas wsstable_rely_le_antimonoD = wsstable_rely_le_antimono[rotated]
lemmas wsstable_rely_ge_monoD = wsstable_rely_ge_mono[rotated]

subsection \<open>nested stabilisation\<close>

lemma wsstable_absorb:
  \<open>R\<^sup>*\<^sup>* = Ra\<^sup>*\<^sup>* OO Rb\<^sup>*\<^sup>* \<Longrightarrow> \<lceil> \<lceil> P \<rceil>\<^bsub>Ra\<^esub> \<rceil>\<^bsub>Rb\<^esub> = \<lceil> P \<rceil>\<^bsub>R\<^esub>\<close>
  by (simp add: sp_comp_rel)

lemma wsstable_absorb1[simp]: \<open>R \<le> R' \<Longrightarrow> \<lceil> \<lceil> P \<rceil>\<^bsub>R\<^esub> \<rceil>\<^bsub>R'\<^esub> = \<lceil> P \<rceil>\<^bsub>R'\<^esub>\<close>
  by (simp add: rel_le_rtranscp_relcompp_absorb(2) wsstable_absorb)

lemma wsstable_absorb2[simp]: \<open>R \<le> R' \<Longrightarrow> \<lceil> \<lceil> P \<rceil>\<^bsub>R'\<^esub> \<rceil>\<^bsub>R\<^esub> = \<lceil> P \<rceil>\<^bsub>R'\<^esub>\<close>
  by (simp add: rel_le_rtranscp_relcompp_absorb(1) wsstable_absorb)

lemma swstable_absorb[simp]:
  \<open>R\<^sup>*\<^sup>* = Rb\<^sup>*\<^sup>* OO Ra\<^sup>*\<^sup>* \<Longrightarrow> \<lfloor> \<lfloor> P \<rfloor>\<^bsub>Ra\<^esub> \<rfloor>\<^bsub>Rb\<^esub> = \<lfloor> P \<rfloor>\<^bsub>R\<^esub>\<close>
  by (simp add: wlp_comp_rel)

lemma swstable_absorb1[simp]: \<open>R \<le> R' \<Longrightarrow> \<lfloor> \<lfloor> P \<rfloor>\<^bsub>R\<^esub> \<rfloor>\<^bsub>R'\<^esub> = \<lfloor> P \<rfloor>\<^bsub>R'\<^esub>\<close>
  by (simp add: rel_le_rtranscp_relcompp_absorb)

lemma swstable_absorb2[simp]: \<open>R \<le> R' \<Longrightarrow> \<lfloor> \<lfloor> P \<rfloor>\<^bsub>R'\<^esub> \<rfloor>\<^bsub>R\<^esub> = \<lfloor> P \<rfloor>\<^bsub>R'\<^esub>\<close>
  by (simp add: rel_le_rtranscp_relcompp_absorb)

lemma wsstable_swstable_absorb[simp]: \<open>R \<le> R' \<Longrightarrow> \<lceil> \<lfloor> P \<rfloor>\<^bsub>R'\<^esub> \<rceil>\<^bsub>R\<^esub> = \<lfloor> P \<rfloor>\<^bsub>R'\<^esub>\<close>
  by (metis order.eq_iff swstable_absorb2 wlp_weaker_iff_sp_stronger wsstable_stronger)

lemma swstable_wsstable_absorb[simp]: \<open>R \<le> R' \<Longrightarrow> \<lfloor> \<lceil> P \<rceil>\<^bsub>R'\<^esub> \<rfloor>\<^bsub>R\<^esub> = \<lceil> P \<rceil>\<^bsub>R'\<^esub>\<close>
  by (metis order.eq_iff swstable_weaker wlp_weaker_iff_sp_stronger wsstable_absorb2)

paragraph \<open> swstable preserves precision \<close>

lemma wlp_refl_preserves_precise:
  \<open>reflp r \<Longrightarrow> precise p \<Longrightarrow> precise (wlp r p)\<close>
  by (simp add: precise_def sepcoimp_def sepconj_def wlp_def le_fun_def reflp_def)

lemma wlp_refl_preserves_precise2:
  \<open>reflp r \<Longrightarrow> precise2 p \<Longrightarrow> precise2 (wlp r p)\<close>
  by (simp add: precise2_def sepcoimp_def sepconj_def wlp_def le_fun_def reflp_def, metis)


lemma swstable_preserves_precise:
  \<open>precise p \<Longrightarrow> precise (\<lfloor> p \<rfloor>\<^bsub>r\<^esub>)\<close>
  by (simp add: wlp_refl_preserves_precise)

lemma swstable_preserves_precise2:
  \<open>precise2 p \<Longrightarrow> precise2 (\<lfloor> p \<rfloor>\<^bsub>r\<^esub>)\<close>
  by (simp add: wlp_refl_preserves_precise2)


section \<open> Properties of stabilisation in a perm algebra \<close>

context perm_alg
begin

subsection \<open> Semidistributivity \<close>

paragraph \<open> Preservation of addition over a relation \<close>

text \<open> This is probably too strong a property to be useful. It essentially requires a rely
      relating two states to also relate all subparts of those states in some consistent manner.
      Compare this approach with the rely splitting approach later. \<close>

definition
  \<open>rel_add_preserve r p1 p2 \<equiv>
    (\<forall>h1 h2 s.
      h1 ## h2 \<longrightarrow>
      r (h1 + h2) s \<longrightarrow>
      p1 h1 \<longrightarrow>
      p2 h2 \<longrightarrow>
      (\<exists>s1 s2. s1 ## s2 \<and> s = s1 + s2 \<and> r h1 s1 \<and> r h2 s2))\<close>

lemma rel_add_preserve_pred_mono1:
  \<open>p1 \<le> p2 \<Longrightarrow> rel_add_preserve r p2 q \<Longrightarrow> rel_add_preserve r p1 q\<close>
  by (force simp add: rel_add_preserve_def)

lemma rel_add_preserve_pred_mono2:
  \<open>q1 \<le> q2 \<Longrightarrow> rel_add_preserve r p q2 \<Longrightarrow> rel_add_preserve r p q1\<close>
  by (force simp add: rel_add_preserve_def)

lemma rel_add_preserve_pred_mono:
  \<open>p1 \<le> p2 \<Longrightarrow> q1 \<le> q2 \<Longrightarrow> rel_add_preserve r p2 q2 \<Longrightarrow> rel_add_preserve r p1 q1\<close>
  by (force simp add: rel_add_preserve_def)

definition
  \<open>weak_rel_add_preserve r p q \<equiv>
    (\<forall>h1 h2 s.
      r (h1 + h2) s \<longrightarrow>
      h1 ## h2 \<longrightarrow>
      p h1 \<longrightarrow>
      q h2 \<longrightarrow>
      (\<exists>s1 s2. s1 ## s2 \<and> s = s1 + s2 \<and> (\<exists>h1'. r h1' s1 \<and> p h1') \<and> (\<exists>h2'. r h2' s2 \<and> q h2')))\<close>

lemma rel_add_preserve_impl_weak:
  \<open>rel_add_preserve r p q \<Longrightarrow> weak_rel_add_preserve r p q\<close>
  unfolding weak_rel_add_preserve_def rel_add_preserve_def
  by fast

lemma rel_add_preserveD:
  \<open>rel_add_preserve r p q \<Longrightarrow>
    r (a + b) c \<Longrightarrow>
    p a \<Longrightarrow>
    q b \<Longrightarrow>
    a ## b \<Longrightarrow>
    (\<exists>ca cb. ca ## cb \<and> c = ca + cb \<and> r a ca \<and> r b cb)\<close>
  by (simp add: rel_add_preserve_def)

paragraph \<open> Semidistributivity \<close>

lemma wlp_sepconj_semidistrib:
  fixes R :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
  assumes \<open>rel_add_preserve r \<top> \<top>\<close>
  shows \<open>wlp r p \<^emph> wlp r q \<le> wlp r (p \<^emph> q)\<close>
  using assms
  apply (clarsimp simp add: rel_add_preserve_def sepconj_def le_fun_def wlp_def)
  apply blast
  done

lemma sp_sepconj_semidistrib:
  fixes R :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
  assumes \<open>weak_rel_add_preserve r p q\<close>
  shows \<open>sp r (p \<^emph> q) \<le> sp r p \<^emph> sp r q\<close>
  using assms
  by (fastforce simp add: weak_rel_add_preserve_def sp_def sepconj_def le_fun_def)


lemma swstable_sepconj_semidistrib:
  fixes R :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
  assumes \<open>rel_add_preserve (R\<^sup>*\<^sup>*) \<top> \<top>\<close>
  shows \<open>\<lfloor> P \<rfloor>\<^bsub>R\<^esub> \<^emph> \<lfloor> Q \<rfloor>\<^bsub>R\<^esub> \<le> \<lfloor> P \<^emph> Q \<rfloor>\<^bsub>R\<^esub>\<close>
  using assms
  by (metis wlp_sepconj_semidistrib)

lemma wsstable_sepconj_semidistrib:
  fixes r :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
  assumes \<open>weak_rel_add_preserve r\<^sup>*\<^sup>* p q\<close>
  shows \<open>\<lceil> p \<^emph> q \<rceil>\<^bsub>r\<^esub> \<le> \<lceil> p \<rceil>\<^bsub>r\<^esub> \<^emph> \<lceil> q \<rceil>\<^bsub>r\<^esub>\<close>
  using assms
  by (metis sp_sepconj_semidistrib)


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
  apply (clarsimp simp add: wlp_def sepconj_def fun_eq_iff)
  apply (simp add: rely_merge_def sepconj_def)
  apply blast
  done

lemma wsstable_sepconj_semidistrib_backwards:
  \<open>\<lceil> P \<^emph> Q \<rceil>\<^bsub>rely_merge R1 R2\<^esub> \<le> \<lceil> P \<rceil>\<^bsub>R1\<^esub> \<^emph> \<lceil> Q \<rceil>\<^bsub>R2\<^esub>\<close>
  apply (clarsimp simp add: sp_def sepconj_def fun_eq_iff)
  apply (simp add: rely_merge_def sepconj_def)
  apply blast
  done

end


class stable_sep_alg = halving_sep_alg +
  fixes stableres :: \<open>'a \<Rightarrow> 'a\<close>
  assumes stableres_concave[intro]: \<open>a ## b \<Longrightarrow> stableres a + stableres b \<le> stableres (a + b)\<close>
  assumes stableres_idem[simp]: \<open>stableres (stableres a) = stableres a\<close>
  assumes stableres_subres[intro]: \<open>stableres a \<le> a\<close>
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

end

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