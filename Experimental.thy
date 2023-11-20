theory Experimental
  imports RGSep PermHeap
begin

section \<open> predicate transformer reasoning + other nice definitions \<close>

definition (in order) \<open>downset x \<equiv> {y. y\<le>x}\<close>

context perm_alg
begin

text \<open> addition irreducible; cf. join/meet irreducible \<close>
definition sepadd_irr :: \<open>'a \<Rightarrow> bool\<close> where
  \<open>sepadd_irr x \<equiv> (\<not> sepadd_unit x) \<and> (\<forall>a b. a < x \<longrightarrow> b < x \<longrightarrow> a ## b \<longrightarrow> a + b < x)\<close>

definition \<open>foundation a \<equiv> {j. j \<le> a \<and> sepadd_irr j}\<close>

definition \<open>frame_closed b \<equiv> (\<forall>x y f. b x y \<longrightarrow> x ## f \<longrightarrow> y ## f \<longrightarrow> b (x + f) (y + f))\<close>
definition \<open>framecl r \<equiv> (\<lambda>a b. (\<exists>x y. r x y \<and> framed_subresource_rel x y a b))\<close>

lemma framecl_frame_closed:
  \<open>frame_closed (framecl b)\<close>
  by (force simp add: frame_closed_def framecl_def intro: framed_subresource_rel_frame)

end

definition \<open>deterministic r \<equiv> (\<forall>x y1 y2. r x y1 \<longrightarrow> r x y2 \<longrightarrow> y1 = y2)\<close>

definition \<open>tentatively_deterministic r \<equiv> (\<forall>x y1 y2. r x y1 \<longrightarrow> r x y2 \<longrightarrow> y1 = x \<or> y2 = x \<or> y1 = y2)\<close>

lemma reflcl_deterministic_impl_tentatively_deterministic:
  \<open>deterministic r \<Longrightarrow> tentatively_deterministic ((=) \<squnion> r)\<close>
  by (simp add: deterministic_def tentatively_deterministic_def)

lemma non_refl_then_deterministic_iff_reflcl_tentatively_deterministic:
  \<open>\<forall>x. \<not> r x x \<Longrightarrow> deterministic r \<longleftrightarrow> tentatively_deterministic ((=) \<squnion> r)\<close>
  by (fastforce simp add: deterministic_def tentatively_deterministic_def)

definition \<open>changes r \<equiv> \<lambda>x y. r x y \<and> y \<noteq> x\<close>
abbreviation \<open>changedom r \<equiv> \<lambda>x. \<exists>y. changes r x y\<close>
lemmas changedom_def = changes_def

lemma pre_state_eq_changedom_and_refl:
  \<open>pre_state r = (changedom r) \<squnion> (\<lambda>x. r x x)\<close>
  by (force simp add: changedom_def pre_state_def)
  

lemma changedom_rtranclp[simp]:
  \<open>changedom (r\<^sup>*\<^sup>*) = changedom r\<close>
proof -
  { fix x y
    assume \<open>r\<^sup>*\<^sup>* x y\<close> \<open>y \<noteq> x\<close>
    then have \<open>\<exists>y. r x y \<and> y \<noteq> x\<close>
      by (induct rule: rtranclp_induct) blast+
  } then show ?thesis
    by (fastforce simp add: changedom_def dest: r_into_rtranclp[of r])
qed

text \<open> strongest postcondition, by way of relations \<close>
definition \<open>sp r p \<equiv> \<lambda>y. (\<exists>x. r x y \<and> p x)\<close>

text \<open> weakest liberal precondition, by way of relations \<close>
definition \<open>wlp r q \<equiv> \<lambda>x. (\<forall>y. r x y \<longrightarrow> q y)\<close>


lemma \<open>p \<le> q \<Longrightarrow> wlp r p \<le> wlp r q\<close>
  by (force simp add: wlp_def)

lemma \<open>wlp r \<top> = \<top>\<close>
  by (force simp add: wlp_def)

lemma \<open>wlp r (p \<sqinter> q) = wlp r p \<sqinter> wlp r q\<close>
  by (force simp add: wlp_def)

lemma \<open>wlp r (\<Sqinter>P) = \<Sqinter>{wlp r p| p. p \<in> P}\<close>
  by (fastforce simp add: wlp_def)

lemma \<open>wlp r \<bottom> = - pre_state r\<close>
  by (simp add: wlp_def fun_eq_iff pre_state_def)

lemma \<open>wlp r p \<squnion> wlp r q \<le> wlp r (p \<squnion> q)\<close>
  by (force simp add: wlp_def)

lemma \<open>deterministic r \<Longrightarrow> wlp r p \<squnion> wlp r q = wlp r (p \<squnion> q)\<close>
  by (force simp add: deterministic_def wlp_def)

lemma wlp_Sup_semidistrib: \<open>\<Squnion>{wlp r p| p. p \<in> P} \<le> wlp r (\<Squnion>P)\<close>
  by (force simp add: wlp_def)

lemma
  assumes \<open>deterministic r\<close>
    and \<open>P \<noteq> {}\<close>
  shows \<open>wlp r (\<Squnion>P) = \<Squnion>{wlp r p| p. p \<in> P}\<close>
proof (rule order.antisym; auto simp add: wlp_def)
  fix x
  assume \<open>\<forall>y. r x y \<longrightarrow> (\<exists>px\<in>P. px y)\<close>
  then obtain px where \<open>r x \<le> px\<close> \<open>px \<in> P\<close>
    using assms unfolding deterministic_def
    by (metis ex_in_conv predicate1I)
  then show \<open>\<exists>q. (\<exists>p. q = (\<lambda>x. \<forall>y. r x y \<longrightarrow> p y) \<and> p \<in> P) \<and> q x\<close>
    by blast
qed

lemma \<open>wlp (=) p = p\<close>
  by (force simp add: wlp_def)

lemma \<open>wlp \<bottom> p = \<top>\<close>
  by (force simp add: wlp_def)

lemma \<open>p < \<top> \<Longrightarrow> wlp \<top> p = \<bottom>\<close>
  by (force simp add: wlp_def less_fun_def)

lemma \<open>wlp (r1 \<squnion> r2) p = wlp r1 p \<sqinter> wlp r2 p\<close>
  by (force simp add: wlp_def fun_eq_iff)

lemma \<open>wlp r1 p \<squnion> wlp r2 p \<le> wlp (r1 \<sqinter> r2) p\<close>
  by (force simp add: wlp_def fun_eq_iff)

lemma \<open>wlp (r1 OO r2) p = wlp r1 (wlp r2 p)\<close>
  by (force simp add: wlp_def)


lemma \<open>p \<le> q \<Longrightarrow> sp r p \<le> sp r q\<close>
  by (force simp add: sp_def)

lemma \<open>sp r \<bottom> = \<bottom>\<close>
  by (force simp add: sp_def)

lemma \<open>sp r (p \<squnion> q) = sp r p \<squnion> sp r q\<close>
  by (force simp add: sp_def)

lemma \<open>\<Squnion>{sp r p| p. p \<in> P} = sp r (\<Squnion>P)\<close>
  by (fastforce simp add: sp_def)

lemma \<open>sp r \<top> = post_state r\<close>
  by (clarsimp simp add: sp_def post_state_def fun_eq_iff)

lemma \<open>sp r (p \<sqinter> q) \<le> sp r p \<sqinter> sp r q\<close>
  by (force simp add: sp_def)

lemma \<open>deterministic (r\<inverse>\<inverse>) \<Longrightarrow> sp r (p \<sqinter> q) = sp r p \<sqinter> sp r q\<close>
  by (simp add: sp_def deterministic_def, blast)

lemma sp_Inf_semidistrib: \<open>sp r (\<Sqinter>P) \<le> \<Sqinter>{sp r p| p. p \<in> P}\<close>
  by (fastforce simp add: sp_def)

lemma
  assumes \<open>deterministic (r\<inverse>\<inverse>)\<close>
    and \<open>P \<noteq> {}\<close>
  shows \<open>sp r (\<Sqinter>P) = \<Sqinter>{sp r p| p. p \<in> P}\<close>
  using assms
  apply (intro order.antisym sp_Inf_semidistrib)
  apply (clarsimp simp add: sp_def imp_ex deterministic_def)
  apply (metis ex_in_conv)
  done

lemma \<open>sp (=) p = p\<close>
  by (force simp add: sp_def)

lemma \<open>sp \<bottom> p = \<bottom>\<close>
  by (force simp add: sp_def)

lemma \<open>\<bottom> < p \<Longrightarrow> sp \<top> p = \<top>\<close>
  by (force simp add: sp_def less_fun_def fun_eq_iff)

lemma \<open>sp (r1 \<squnion> r2) p = sp r1 p \<squnion> sp r2 p\<close>
  by (force simp add: sp_def)

lemma \<open>sp (r1 \<sqinter> r2) p \<le> sp r1 p \<sqinter> sp r2 p\<close>
  by (force simp add: sp_def)

lemma \<open>sp (r1 OO r2) p = sp r2 (sp r1 p)\<close>
  by (force simp add: sp_def relcompp_apply)


lemma \<open>reflp r1 \<Longrightarrow> transp r2 \<Longrightarrow> r1 \<le> r2 \<Longrightarrow> sp r1 (sp r2 p) = sp r2 p\<close>
  by (simp add: reflp_def transp_def sp_def, fast)

lemma \<open>reflp r1 \<Longrightarrow> transp r2 \<Longrightarrow> r1 \<le> r2 \<Longrightarrow> sp r2 (sp r1 p) = sp r2 p\<close>
  by (simp add: reflp_def transp_def sp_def, fast)

lemma \<open>reflp r1 \<Longrightarrow> transp r2 \<Longrightarrow> r1 \<le> r2 \<Longrightarrow> wlp r1 (wlp r2 p) = wlp r2 p\<close>
  by (simp add: reflp_def transp_def wlp_def, fast)

lemma \<open>reflp r1 \<Longrightarrow> transp r2 \<Longrightarrow> r1 \<le> r2 \<Longrightarrow> wlp r2 (wlp r1 p) = wlp r2 p\<close>
  by (simp add: reflp_def transp_def wlp_def, fast)

lemma \<open>reflp r1 \<Longrightarrow> transp r2 \<Longrightarrow> r1 \<le> r2 \<Longrightarrow> wlp r1 (sp r2 p) = sp r2 p\<close>
  by (simp add: reflp_def transp_def wlp_def sp_def, fast)

lemma \<open>reflp r1 \<Longrightarrow> transp r2 \<Longrightarrow> r1 \<le> r2 \<Longrightarrow> sp r1 (wlp r2 p) = wlp r2 p\<close>
  by (simp add: reflp_def transp_def wlp_def sp_def, blast)


section \<open> Labelled Permission algebra \<close>

text \<open>
  This subclass is supposed to be the algebraic version of a heap.
  It introduces an order which must be compatible with, but can be more coarse than,
  the subresource relation. The equivalence classes induced by this order represent
  resources with the same set of labels.

  We want labels to form a distributive lattice, to take advantage of
  Birkhoff's representation theorem.
  TODO,sorry: The law \<open>labels_strong_distrib_law\<close> probably does this, but I need to check.
\<close>

class labelled_perm_alg = perm_alg +
  fixes labels_leq :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (infix \<open>\<le>\<^sub>l\<close> 50)
    and labels_less :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (infix \<open><\<^sub>l\<close> 50)
  assumes labels_leq_less_preorder:
    \<open>preordering labels_leq labels_less\<close>
  assumes labels_less_embeds: \<open>\<And>a b. a < b \<Longrightarrow> a <\<^sub>l b\<close>
  assumes labels_leq_upper_bound:
    \<open>\<And>a b c. a ## b \<Longrightarrow> a \<le>\<^sub>l c \<Longrightarrow> b \<le>\<^sub>l c \<Longrightarrow> a + b \<le>\<^sub>l c\<close>
  assumes labels_strong_distrib_law:
    \<open>\<And>a b c.
      a ## b \<Longrightarrow> a ## c \<Longrightarrow> inf_exists b c \<Longrightarrow> inf_exists (a + b) (a + c) \<Longrightarrow>
        glb (a + b) (a + c) \<le>\<^sub>l a + glb b c\<close>
begin

lemma labels_leq_embeds:
  \<open>a \<le> b \<Longrightarrow> a \<le>\<^sub>l b\<close>
  using labels_leq_less_preorder labels_less_embeds
  by (metis order.order_iff_strict preordering.axioms(1) partial_preordering.refl
      preordering.strict_implies_order)

lemma labels_leq_add:
  \<open>a ## b \<Longrightarrow> a \<le>\<^sub>l (a + b)\<close>
  by (simp add: labels_leq_embeds)

definition labels_eq :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (infix \<open>=\<^sub>l\<close> 50) where
  \<open>labels_eq a b \<equiv> a \<le>\<^sub>l b \<and> b \<le>\<^sub>l a\<close>

lemma labels_eq_equivp: \<open>equivp (=\<^sub>l)\<close>
  unfolding labels_eq_def
  using labels_leq_less_preorder
  by (force intro: equivpI reflpI sympI transpI dest: preordering_refl preordering_trans)

lemma disjoint_units_have_same_labels:
  assumes
    \<open>a ## b\<close>
    \<open>sepadd_unit a\<close>
    \<open>sepadd_unit b\<close>
  shows
    \<open>a =\<^sub>l b\<close>
  using assms
  by (metis labels_eq_def labels_leq_add disjoint_sym sepadd_unit_def)

lemma same_labels_as_unit_is_unit:
  assumes
    \<open>a ## b\<close>
    \<open>sepadd_unit a\<close>
    \<open>a =\<^sub>l b\<close>
  shows
    \<open>sepadd_unit b\<close>
  using assms
  by (metis labels_eq_def order.order_iff_strict labels_leq_less_preorder labels_less_embeds
      partial_le_plus sepadd_unit_def preordering.strict_iff_not)

subsection  \<open> Label overlap \<close>

definition \<open>label_overlap a b \<equiv> \<exists>c. c \<le>\<^sub>l a \<and> c \<le>\<^sub>l b \<and> \<not> sepadd_unit c\<close>

lemma label_overlap_refl:
  \<open>\<not> sepadd_unit a \<Longrightarrow> label_overlap a a\<close>
  using label_overlap_def labels_leq_embeds by blast

lemma label_overlap_sym:
  \<open>label_overlap a b \<Longrightarrow> label_overlap b a\<close>
  using label_overlap_def by blast

lemma same_labels_implies_label_overlap:
  \<open>a =\<^sub>l b \<Longrightarrow> \<not> sepadd_unit a \<Longrightarrow> \<not> sepadd_unit b \<Longrightarrow> label_overlap a b\<close>
  using label_overlap_def labels_eq_def labels_leq_embeds by blast

end

class halving_labelled_perm_alg = halving_perm_alg + labelled_perm_alg
begin

lemma half_subseteq_labels: \<open>half a \<le>\<^sub>l a\<close>
  by (metis half_additive_split half_self_disjoint labels_leq_embeds partial_le_plus2)

lemma half_superseteq_labels: \<open>a \<le>\<^sub>l half a\<close>
  by (metis half_additive_split half_self_disjoint labels_leq_upper_bound labels_leq_embeds
      order.refl)

lemma half_has_same_labels: \<open>half a =\<^sub>l a\<close>
  by (simp add: half_subseteq_labels half_superseteq_labels labels_eq_def)

end



context sep_alg
begin

lemma sepadd_irr_eq:
  \<open>sepadd_irr x \<longleftrightarrow> x \<noteq> 0 \<and> (\<forall>a b. a < x \<longrightarrow> b < x \<longrightarrow> a ## b \<longrightarrow> a + b < x)\<close>
  unfolding sepadd_irr_def
  using zero_only_unit by presburger

lemma sepadd_irr_eq2:
  \<open>sepadd_irr x \<longleftrightarrow> x \<noteq> 0 \<and> (\<forall>a b. a ## b \<longrightarrow> x = a + b \<longrightarrow> x = a \<or> x = b)\<close>
  unfolding sepadd_irr_eq
  apply (rule iffI)
   apply (metis order.not_eq_order_implies_strict order.irrefl partial_le_plus partial_le_plus2)
  apply (metis less_iff_sepadd nless_le sepadd_left_mono)
  done

end


lemma (in distrib_sep_alg) sepadd_irr_distrib_eq:
  shows \<open>sepadd_irr x \<longleftrightarrow> x \<noteq> 0 \<and> (\<forall>a b. a ## b \<longrightarrow> x \<le> a + b \<longrightarrow> x \<le> a \<or> x \<le> b)\<close>
  unfolding sepadd_irr_eq
  apply (rule iffI)
   apply (simp add: inf.order_iff inf_add_distrib1, metis disjoint_add_rightL disjoint_preservation
      le_iff_sepadd order.strict_implies_not_eq inf.cobounded1 inf.cobounded2 neq_le_trans)
  apply (force simp add: order.strict_iff_not inf.absorb_iff2 inf_add_distrib1)
  done

class big_sep_alg = distrib_sep_alg + cancel_perm_alg
begin

lemma False
  nitpick
  oops


definition
  \<open>good_prog b \<equiv>
      (\<forall>j. sepadd_irr j \<longrightarrow>
        ((\<exists>x y. b x y \<and> j \<le> x \<and> \<not> j \<le> y) \<longrightarrow> (\<forall>x' y'. b x' y' \<longrightarrow> j \<le> x' \<and> \<not> j \<le> y')) \<and>
        ((\<exists>x y. b x y \<and> \<not> j \<le> x \<and> j \<le> y) \<longrightarrow> (\<forall>x' y'. b x' y' \<longrightarrow> \<not> j \<le> x' \<and> j \<le> y'))
      ) \<and> frame_closed b\<close>

definition
  \<open>rgsep_rely S \<equiv> (\<lambda>a b. \<exists>x y. (x, y) \<in> S \<and> framed_subresource_rel x y a b)\<^sup>*\<^sup>*\<close>

definition
  \<open>good_rely b \<equiv>
      (\<forall>j. sepadd_irr j \<longrightarrow>
        ((\<exists>x y. b x y \<and> j \<le> x \<and> \<not> j \<le> y) \<longrightarrow> (\<forall>x' y'. b x' y' \<longrightarrow> j \<le> x' \<and> \<not> j \<le> y')) \<and>
        ((\<exists>x y. b x y \<and> \<not> j \<le> x \<and> j \<le> y) \<longrightarrow> (\<forall>x' y'. b x' y' \<longrightarrow> \<not> j \<le> x' \<and> j \<le> y'))
      ) \<and>
      (\<forall>x y f. b x y \<longrightarrow> x ## f \<longrightarrow> y ## f \<longrightarrow> b (x + f) (y + f))\<close>

lemma wsstable_sepconj_semidistrib_backwards:
  \<open>r = rgsep_rely S \<Longrightarrow>
    S = {a} \<Longrightarrow>
    X = \<lceil> P \<^emph> Q \<rceil>\<^bsub>r\<^esub> \<Longrightarrow>
    Y = \<lceil> P \<rceil>\<^bsub>r\<^esub> \<Longrightarrow>
    Z = \<lceil> Q \<rceil>\<^bsub>r\<^esub> \<Longrightarrow>
    X \<le> Y \<^emph> Z\<close>
  nitpick
  oops

end

lemma (in perm_alg) wsstable_semidistrib_disjoint_pre_state_strong:
  \<open>\<forall>a. (P \<^emph> Q) a \<longrightarrow> changedom r\<^sup>*\<^sup>* a \<longrightarrow> sepadd_unit a \<Longrightarrow>
    changes r\<^sup>*\<^sup>* \<sqinter> rel_liftL (P \<^emph> Q) \<le> compatible \<Longrightarrow>
    \<lceil> P \<^emph> Q \<rceil>\<^bsub>r\<^esub> \<le> \<lceil> P \<rceil>\<^bsub>r\<^esub> \<^emph> \<lceil> Q \<rceil>\<^bsub>r\<^esub>\<close>
  apply (clarsimp simp add: changedom_def rel_liftL_def)
  apply (clarsimp simp add: wsstable_def sepconj_def pre_state_def le_fun_def
      fun_eq_iff imp_ex imp_conjL simp del: all_simps(5))
  apply (drule spec2, drule mp, assumption, drule mp, assumption, drule mp, assumption)
  apply (drule spec, drule mp, assumption)
  apply (case_tac \<open>x = h1 + h2\<close>, blast)
  apply clarsimp
  apply (frule(2) disjoint_units_identical)
  apply (clarsimp simp add: sepadd_unit_left)
  apply (metis compatible_to_unit_is_unit_right compatible_unit_disjoint sepadd_unit_idem_add
      sepadd_unit_selfsep rtranclp.rtrancl_refl)
(*
  apply (rule_tac x=x in exI)
  apply (rule_tac x=h2 in exI)
  apply (rule conjI)
   apply (metis compatible_unit_disjoint)
  apply (rule conjI)
   apply (metis compatible_to_unit_is_unit_right)
  apply force
*)
  done

lemma (in perm_alg) wsstable_semidistrib_no_pre_state:
  \<open>\<forall>h1. (P \<^emph> Q) h1 \<longrightarrow> pre_state r h1 \<longrightarrow> False \<Longrightarrow>
    \<lceil> P \<^emph> Q \<rceil>\<^bsub>r\<^esub> \<le> \<lceil> P \<rceil>\<^bsub>r\<^esub> \<^emph> \<lceil> Q \<rceil>\<^bsub>r\<^esub>\<close>
  apply (insert wsstable_semidistrib_disjoint_pre_state_strong[of P Q r])
  apply (drule meta_mp)
   apply (metis changes_def converse_rtranclpE pre_state_def)
  apply (drule meta_mp)
   apply (clarsimp simp add: rel_liftL_def changes_def pre_state_def)
   apply (metis converse_rtranclpE)
  apply assumption
  done

lemma (in inf_sep_alg) wsstable_semidistrib_disjoint_pre_state:
  \<open>\<forall>h1 h2. (P \<^emph> Q) h1 \<longrightarrow> changedom r h2 \<longrightarrow> h1 \<sqinter> h2 = 0 \<Longrightarrow>
    \<lceil> P \<^emph> Q \<rceil>\<^bsub>r\<^esub> \<le> \<lceil> P \<rceil>\<^bsub>r\<^esub> \<^emph> \<lceil> Q \<rceil>\<^bsub>r\<^esub>\<close>
  apply (insert wsstable_semidistrib_disjoint_pre_state_strong[of P Q r])
  apply (drule meta_mp)
   apply (metis changedom_rtranclp sepinf_idem zero_only_unit)
  apply (drule meta_mp)
   apply (force simp add: rel_liftL_def changes_def pre_state_def all_compatible)
  apply assumption
  done

lemma (in inf_perm_alg) wsstable_semidistrib_disjoint_pre_state_strong2:
  \<open>\<forall>h1 h2. (P \<^emph> Q) h1 \<longrightarrow> changedom r h2 \<longrightarrow> compatible h1 h2 \<longrightarrow> sepadd_unit (h1 \<sqinter> h2) \<Longrightarrow>
    changes r\<^sup>*\<^sup>* \<sqinter> rel_liftL (P \<^emph> Q) \<le> compatible \<Longrightarrow>
    \<lceil> P \<^emph> Q \<rceil>\<^bsub>r\<^esub> \<le> \<lceil> P \<rceil>\<^bsub>r\<^esub> \<^emph> \<lceil> Q \<rceil>\<^bsub>r\<^esub>\<close>
  apply (insert wsstable_semidistrib_disjoint_pre_state_strong[of P Q r])
  apply (metis changedom_rtranclp compatible_refl sepinf_idem)
  done


(* The situation that we want to prove is *)
lemma (in perm_alg) wsstable_semidistrib_realistic:
  \<open>p = pab \<^emph> pc \<Longrightarrow>
    r = c\<^sup>*\<^sup>* \<Longrightarrow>
    \<lceil> pab \<rceil>\<^bsub>c\<^esub> = pa' \<^emph> pb' \<Longrightarrow>
    pab = pa \<^emph> pb \<Longrightarrow>
    wpa' = \<lceil> pa \<rceil>\<^bsub>c\<^esub> \<Longrightarrow>
    wpb' = \<lceil> pb \<rceil>\<^bsub>c\<^esub> \<Longrightarrow>
    \<lceil> pa' \<rceil>\<^bsub>b \<squnion> c\<^esub> \<^emph> \<lceil> pb' \<rceil>\<^bsub>a \<squnion> c\<^esub> \<^emph> \<lceil> pc \<rceil>\<^bsub>a \<squnion> b\<^esub>
    \<le>
    \<lceil> wpa' \<rceil>\<^bsub>b \<squnion> c\<^esub> \<^emph> \<lceil> wpb' \<rceil>\<^bsub>a \<squnion> c\<^esub> \<^emph> \<lceil> pc \<rceil>\<^bsub>a \<squnion> b\<^esub>\<close>
  oops


class finite_sep_alg = distrib_sep_alg +
  assumes finite_univ: \<open>finite (UNIV :: 'a set)\<close>
  fixes \<II> :: \<open>'a set\<close>
  assumes \<open>\<II> = Collect sepadd_irr\<close>
begin

lemma \<open>sepadd_irr a \<Longrightarrow> sepadd_irr b \<Longrightarrow> a \<noteq> b \<Longrightarrow> a \<le> c \<Longrightarrow> b \<le> c \<Longrightarrow> a ## b\<close>
  apply (clarsimp simp add: sepadd_irr_distrib_eq)
  by (metis disjoint_preservation disjoint_sym dual_order.antisym le_iff_sepadd)

end


end