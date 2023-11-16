theory Experimental
  imports RGSep PermHeap
begin

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

class labelled_perm_alg = perm_alg + indivisible_units_perm_alg +
  fixes labels_leq :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (infix \<open>\<le>\<^sub>l\<close> 50)
    and labels_less :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (infix \<open><\<^sub>l\<close> 50)
  assumes labels_leq_less_preorder:
    \<open>preordering labels_leq labels_less\<close>
  assumes labels_less_embeds: \<open>\<And>a b. a < b \<Longrightarrow> a <\<^sub>l b\<close>
  assumes labels_leq_upper_bound:
    \<open>\<And>a b c. a ## b \<Longrightarrow> a \<le>\<^sub>l c \<Longrightarrow> b \<le>\<^sub>l c \<Longrightarrow> a + b \<le>\<^sub>l c\<close>
  assumes labels_strong_distrib_law:
    \<open>\<And>a b c.
      a ## b \<Longrightarrow> a ## c \<Longrightarrow> glb_exists b c \<Longrightarrow> glb_exists (a + b) (a + c) \<Longrightarrow>
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
    \<open>unit_sepadd a\<close>
    \<open>unit_sepadd b\<close>
  shows
    \<open>a =\<^sub>l b\<close>
  using assms
  by (metis labels_eq_def labels_leq_add disjoint_symm unit_sepadd_def)

lemma same_labels_as_unit_is_unit:
  assumes
    \<open>a ## b\<close>
    \<open>unit_sepadd a\<close>
    \<open>a =\<^sub>l b\<close>
  shows
    \<open>unit_sepadd b\<close>
  using assms
  by (metis labels_eq_def order.order_iff_strict labels_leq_less_preorder labels_less_embeds
      partial_le_plus unit_sepadd_def preordering.strict_iff_not)

subsection  \<open> Label overlap \<close>

definition \<open>label_overlap a b \<equiv> \<exists>c. c \<le>\<^sub>l a \<and> c \<le>\<^sub>l b \<and> \<not> unit_sepadd c\<close>

lemma label_overlap_refl:
  \<open>\<not> unit_sepadd a \<Longrightarrow> label_overlap a a\<close>
  using label_overlap_def labels_leq_embeds by blast

lemma label_overlap_sym:
  \<open>label_overlap a b \<Longrightarrow> label_overlap b a\<close>
  using label_overlap_def by blast

lemma same_labels_implies_label_overlap:
  \<open>a =\<^sub>l b \<Longrightarrow> \<not> unit_sepadd a \<Longrightarrow> \<not> unit_sepadd b \<Longrightarrow> label_overlap a b\<close>
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

section \<open> \<close>

context perm_alg
begin

(* sepadd irreducible *)
definition sepadd_irr :: \<open>'a \<Rightarrow> bool\<close> where
  \<open>sepadd_irr x \<equiv> (\<not> unit_sepadd x) \<and> (\<forall>a b. a < x \<longrightarrow> b < x \<longrightarrow> a ## b \<longrightarrow> a + b < x)\<close>

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


definition \<open>foundation a \<equiv> {j. j \<le> a \<and> sepadd_irr j}\<close>

definition
  \<open>frame_closed b \<equiv> (\<forall>x y f. b x y \<longrightarrow> x ## f \<longrightarrow> y ## f \<longrightarrow> b (x + f) (y + f))\<close>

definition
  \<open>good_prog b \<equiv>
      (\<forall>j. sepadd_irr j \<longrightarrow>
        ((\<exists>x y. b x y \<and> j \<le> x \<and> \<not> j \<le> y) \<longrightarrow> (\<forall>x' y'. b x' y' \<longrightarrow> j \<le> x' \<and> \<not> j \<le> y')) \<and>
        ((\<exists>x y. b x y \<and> \<not> j \<le> x \<and> j \<le> y) \<longrightarrow> (\<forall>x' y'. b x' y' \<longrightarrow> \<not> j \<le> x' \<and> j \<le> y'))
      ) \<and> frame_closed b\<close>

definition \<open>framecl r \<equiv> (\<lambda>a b. (\<exists>x y. r x y \<and> framed_subresource_rel x y a b))\<close>

lemma framecl_frame_closed:
  \<open>frame_closed (framecl b)\<close>
  by (force simp add: frame_closed_def framecl_def intro: framed_subresource_rel_frame)

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
    X = \<lceil> P \<^emph> Q \<rceil>\<^bsub>r\<^esub> \<Longrightarrow>
    Y = \<lceil> P \<rceil>\<^bsub>r\<^esub> \<Longrightarrow>
    Z = \<lceil> Q \<rceil>\<^bsub>r\<^esub> \<Longrightarrow>
    X \<le> Y \<^emph> Z\<close>
  nitpick
  oops

definition \<open>downset x \<equiv> {y. y\<le>x}\<close>

(*
  alloc a; dealloc a
*)

lemma
  fixes p :: \<open>'a \<Rightarrow> bool\<close>
  assumes
    \<open>good_prog b\<close>
    and
    \<open>z \<le> pre_state b\<close>
    \<open>r = b\<^sup>*\<^sup>*\<close>
    \<open>\<exists>!h. z h\<close>
    \<open>\<exists>h. p h\<close>
    \<open>\<exists>!h. p1 h\<close>
    \<open>\<exists>!h. p2 h\<close>
    and \<open>J = Collect sepadd_irr\<close>
    and \<open>p = p1 \<^emph> p2\<close>
    and \<open>p' = \<lceil> p \<rceil>\<^bsub>r\<^esub>\<close>
    and \<open>pb = \<lceil> p1 \<rceil>\<^bsub>r\<^esub> \<^emph> \<lceil> p2 \<rceil>\<^bsub>r\<^esub>\<close>
    and \<open>\<exists>h. (p \<^emph> z) h\<close>
  shows
    \<open>J = J \<union> J \<and> (p' \<le> pb)\<close>
  nitpick
  oops

lemma
  fixes p :: \<open>'a \<Rightarrow> bool\<close>
  assumes
    \<open>good_prog b1\<close>
    \<open>good_prog b2\<close>
    \<open>good_prog b3\<close>
    and
    \<open>\<exists>!h. p h\<close>
    \<open>r1 = (b2 \<squnion> b3)\<^sup>*\<^sup>*\<close>
    \<open>r2 = (b1 \<squnion> b3)\<^sup>*\<^sup>*\<close>
    \<open>r12 = (b3)\<^sup>*\<^sup>*\<close>
    \<open>r3 = (b1 \<squnion> b2)\<^sup>*\<^sup>*\<close>
    \<open>p = p12 \<^emph> p3\<close>
    \<open>\<lceil> p12 \<rceil>\<^bsub>r12\<^esub> = p1 \<^emph> p2\<close>
    \<open>p1 = \<lfloor> p1 \<rfloor>\<^bsub>r1\<^esub>\<close>
    \<open>p2 = \<lfloor> p2 \<rfloor>\<^bsub>r2\<^esub>\<close>
    \<open>p3 = \<lfloor> p3 \<rfloor>\<^bsub>r3\<^esub>\<close>
    \<open>p1x \<le> pre_state b1\<close>
    \<open>p2x \<le> pre_state b2\<close>
    \<open>p3x \<le> pre_state b3\<close>
    \<open>q1 = \<lceil> post_state (rel_liftL p1 \<sqinter> b1) \<rceil>\<^bsub>r1\<^esub>\<close>
    \<open>q2 = \<lceil> post_state (rel_liftL p2 \<sqinter> b2) \<rceil>\<^bsub>r2\<^esub>\<close>
    \<open>q3 = \<lceil> post_state (rel_liftL p3 \<sqinter> b3) \<rceil>\<^bsub>r3\<^esub>\<close>
    \<open>q = q1 \<^emph> q2 \<^emph> q3\<close>
    \<open>\<exists>!h. p1 h\<close>
    \<open>\<exists>!h. p12 h\<close>
    \<open>\<exists>!h. p2 h\<close>
    \<open>\<exists>!h. p3 h\<close>
    \<open>\<exists>!h. q h\<close>
  and \<comment> \<open> bad reasoning \<close>
    \<open>p12 = p1b \<^emph> p2b\<close>
    \<open>\<lceil> p1b \<rceil>\<^bsub>r12\<^esub> = \<lfloor> p1bx \<rfloor>\<^bsub>r1\<^esub>\<close>
    \<open>\<lceil> p2b \<rceil>\<^bsub>r12\<^esub> = \<lfloor> p2bx \<rfloor>\<^bsub>r2\<^esub>\<close>
    \<open>p1bx \<le> pre_state b1\<close>
    \<open>p2bx \<le> pre_state b2\<close>
    \<open>q1b = \<lceil> post_state (rel_liftL p1bx \<sqinter> b1) \<rceil>\<^bsub>r1\<^esub>\<close>
    \<open>q2b = \<lceil> post_state (rel_liftL p2bx \<sqinter> b2) \<rceil>\<^bsub>r2\<^esub>\<close>
    \<open>qy = q1b \<^emph> q2b \<^emph> q3\<close>
    and \<open>J = Collect sepadd_irr\<close>
  shows
    \<open>J = J \<union> J \<and> (q \<le> qy)\<close>
  oops

lemma
  fixes p :: \<open>'a \<Rightarrow> bool\<close>
  assumes
    \<open>good_prog b1\<close>
    \<open>good_prog b2\<close>
    \<open>good_prog b3\<close>
    and
    \<open>\<exists>!h. p h\<close>
    \<open>r1 = (b2 \<squnion> b3)\<^sup>*\<^sup>*\<close>
    \<open>r2 = (b1 \<squnion> b3)\<^sup>*\<^sup>*\<close>
    \<open>r12 = (b3)\<^sup>*\<^sup>*\<close>
    \<open>r3 = (b1 \<squnion> b2)\<^sup>*\<^sup>*\<close>
    \<open>p = p12 \<^emph> p3\<close>
    \<open>\<lceil> p12 \<rceil>\<^bsub>r12\<^esub> = p1 \<^emph> p2\<close>
    \<open>p1 \<le> pre_state b1\<close>
    \<open>p2 \<le> pre_state b2\<close>
    \<open>p3 \<le> pre_state b3\<close>
    \<open>p1 = \<lfloor> p1 \<rfloor>\<^bsub>r1\<^esub>\<close>
    \<open>p2 = \<lfloor> p2 \<rfloor>\<^bsub>r1\<^esub>\<close>
    \<open>p3 = \<lfloor> p3 \<rfloor>\<^bsub>r1\<^esub>\<close>
    \<open>q1 = \<lceil> post_state (rel_liftL p1 \<sqinter> b1) \<rceil>\<^bsub>r1\<^esub>\<close>
    \<open>q2 = \<lceil> post_state (rel_liftL p2 \<sqinter> b2) \<rceil>\<^bsub>r2\<^esub>\<close>
    \<open>q3 = \<lceil> post_state (rel_liftL p3 \<sqinter> b3) \<rceil>\<^bsub>r3\<^esub>\<close>
    \<open>q = \<lceil> q1 \<^emph> q2 \<rceil>\<^bsub>r12\<^esub> \<^emph> q3\<close>
  and \<comment> \<open> bad reasoning \<close>
    \<open>q1b = \<lceil> q1 \<rceil>\<^bsub>r12\<^esub>\<close>
    \<open>q2b = \<lceil> q2 \<rceil>\<^bsub>r12\<^esub> \<close>
    \<open>qy = q1b \<^emph> q2b \<^emph> q3\<close>
  shows
    \<open>(q \<le> qy)\<close>
  oops

end



lemma (in perm_alg) wsstable_semidistrib_not_pre_state:
  \<open>\<forall>h. (P \<^emph> Q) h \<longrightarrow> \<not> pre_state r h \<Longrightarrow>
    \<lceil> P \<^emph> Q \<rceil>\<^bsub>r\<^esub> \<le> \<lceil> P \<rceil>\<^bsub>r\<^esub> \<^emph> \<lceil> Q \<rceil>\<^bsub>r\<^esub>\<close>
  apply (simp add: wsstable_def sepconj_def fun_eq_iff le_fun_def pre_state_def)
  apply (metis converse_rtranclpE rtranclp.rtrancl_refl)
  done

lemma (in glb_sep_alg) wsstable_semidistrib_disjoint_pre_state:
  \<open>\<forall>h1 h2. (P \<^emph> Q) h1 \<longrightarrow> pre_state r h2 \<longrightarrow> h1 \<sqinter> h2 = 0 \<Longrightarrow>
    \<lceil> P \<^emph> Q \<rceil>\<^bsub>r\<^esub> \<le> \<lceil> P \<rceil>\<^bsub>r\<^esub> \<^emph> \<lceil> Q \<rceil>\<^bsub>r\<^esub>\<close>
  apply (clarsimp simp add: wsstable_def sepconj_def fun_eq_iff le_fun_def)
  apply (clarsimp simp del: all_simps(5) simp add: imp_ex imp_conjL)
  apply (simp add: pre_state_def)
  apply (metis converse_rtranclpE inf_idem sepadd_0_right sepadd_eq_0_iff_both_eq_0 zero_disjointR
      rtranclp.rtrancl_refl)
  done

lemma (in perm_alg)
  \<open>unit_sepadd a \<Longrightarrow> b \<le> a \<Longrightarrow> unit_sepadd b\<close>
  by (metis disjoint_add_rightL dual_order.antisym le_iff_sepadd_weak unit_sepadd_def)

class test_perm_alg = indivisible_units_perm_alg + disjoint_parts_perm_alg + strong_sep_perm_alg
begin

definition \<open>changedom r \<equiv> \<lambda>x. \<exists>y. r x y \<and> y \<noteq> x\<close>

lemma wsstable_semidistrib_disjoint_pre_state:
  \<open>\<forall>h h'. P h \<longrightarrow> changedom r h' \<longrightarrow> h ## h' \<Longrightarrow>
    \<forall>h h'. Q h \<longrightarrow> changedom r h' \<longrightarrow> h ## h' \<Longrightarrow>
    \<forall>h h'. (P \<^emph> Q) h \<longrightarrow> changedom r h' \<longrightarrow> h ## h' \<Longrightarrow>
    reflp r \<Longrightarrow>
    transp r \<Longrightarrow>
    X = \<lceil> P \<^emph> Q \<rceil>\<^bsub>r\<^esub> \<Longrightarrow>
    Y = \<lceil> P \<rceil>\<^bsub>r\<^esub> \<Longrightarrow>
    Z = \<lceil> Q \<rceil>\<^bsub>r\<^esub> \<Longrightarrow>
    YZ = Y \<^emph> Z \<Longrightarrow>
    X \<le> YZ\<close>
  nitpick
  sorry

end


class finite_sep_alg = distrib_sep_alg +
  assumes finite_univ: \<open>finite (UNIV :: 'a set)\<close>
  fixes \<II> :: \<open>'a set\<close>
  assumes \<open>\<II> = Collect sepadd_irr\<close>
begin

lemma \<open>sepadd_irr a \<Longrightarrow> sepadd_irr b \<Longrightarrow> a \<noteq> b \<Longrightarrow> a \<le> c \<Longrightarrow> b \<le> c \<Longrightarrow> a ## b\<close>
  apply (clarsimp simp add: sepadd_irr_distrib_eq)
  by (metis disjoint_preservation disjoint_symm dual_order.antisym le_iff_sepadd)

end


end