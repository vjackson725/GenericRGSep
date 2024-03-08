theory Experimental
  imports Soundness
begin

class pre_semi_sep_alg = disjoint + plus +
  (* ordered partial commutative monoid *)
  assumes partial_add_assoc: \<open>a ## b \<Longrightarrow> b ## c \<Longrightarrow> a ## c \<Longrightarrow> (a + b) + c = a + (b + c)\<close>
  assumes partial_add_commute: \<open>a ## b \<Longrightarrow> a + b = b + a\<close>
  (* separation laws *)
  assumes disjoint_sym: \<open>a ## b \<Longrightarrow> b ## a\<close>
  assumes disjoint_add_rightL: \<open>b ## c \<Longrightarrow> a ## b + c \<Longrightarrow> a ## b\<close>
  assumes disjoint_add_right_commute: \<open>b ## c \<Longrightarrow> a ## b + c \<Longrightarrow> b ## a + c\<close>
  (* assumes positivity: \<open>a ## b \<Longrightarrow> a + b = c \<Longrightarrow> c ## c \<Longrightarrow> c + c = c \<Longrightarrow> a + a = a\<close> *)
  assumes unit_sub_closure:
    \<open>a ## b \<Longrightarrow> a + b ## c \<Longrightarrow> b ## b \<Longrightarrow> c ## c \<Longrightarrow> a + (b + c) = a \<Longrightarrow> a + b = a\<close>
begin

definition subadd :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (infix \<open>\<prec>\<^sub>+\<close> 50) where
  \<open>a \<prec>\<^sub>+ b \<equiv> a \<noteq> b \<and> (\<exists>c. a ## c \<and> a + c = b)\<close>

definition subaddeq :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (infix \<open>\<preceq>\<^sub>+\<close> 50) where
  \<open>a \<preceq>\<^sub>+ b \<equiv> a = b \<or> (\<exists>c. a ## c \<and> a + c = b)\<close>

lemma subadd_order:
  \<open>class.order (\<preceq>\<^sub>+) (\<prec>\<^sub>+)\<close>
  apply (unfold subadd_def subaddeq_def)
  apply standard
     apply (rule iffI conjI impI; elim conjE exE disjE)
       apply clarsimp
       apply (rule conjI, force)
       apply clarsimp
       apply (metis disjoint_add_rightL disjoint_sym partial_add_assoc partial_add_commute unit_sub_closure)
      apply blast
     apply blast
    apply blast
   apply clarsimp
   apply (elim disjE)
      apply blast
     apply blast
    apply blast
   apply clarsimp
   apply (metis disjoint_add_rightL disjoint_add_right_commute disjoint_sym partial_add_assoc
      partial_add_commute)
  apply (metis disjoint_add_rightL disjoint_sym partial_add_assoc partial_add_commute unit_sub_closure)
  done

definition \<open>is_sepunit u \<equiv> u ## u \<and> (\<forall>a. u ## a \<longrightarrow> a + u = a)\<close>

lemma \<open>is_sepunit u \<Longrightarrow> u \<preceq>\<^sub>+ a \<Longrightarrow> a ## b \<Longrightarrow> u \<preceq>\<^sub>+ a + b\<close>
  unfolding is_sepunit_def subaddeq_def
  by (metis disjoint_add_right_commute disjoint_sym partial_add_commute)

lemma \<open>is_sepunit u \<Longrightarrow> u \<preceq>\<^sub>+ a \<Longrightarrow> a ## b \<Longrightarrow> u \<preceq>\<^sub>+ b\<close>
  unfolding is_sepunit_def subaddeq_def
  by (metis disjoint_add_rightL disjoint_sym partial_add_commute)

lemma \<open>is_sepunit u \<Longrightarrow> u \<preceq>\<^sub>+ a \<Longrightarrow> a ## b \<Longrightarrow> u \<preceq>\<^sub>+ a + b\<close>
  unfolding is_sepunit_def subaddeq_def
  by (metis disjoint_add_right_commute disjoint_sym partial_add_commute)

lemma \<open>is_sepunit u \<Longrightarrow> u \<preceq>\<^sub>+ a \<Longrightarrow> a ## b \<Longrightarrow> u \<preceq>\<^sub>+ b\<close>
  unfolding is_sepunit_def subaddeq_def
  by (metis disjoint_add_rightL disjoint_sym partial_add_commute)

lemma 
    \<open>\<forall>u a. a \<preceq>\<^sub>+ u \<longrightarrow> is_sepunit u \<longrightarrow> is_sepunit a\<close>
   by (clarsimp simp add: is_sepunit_def subaddeq_def,
      metis unit_sub_closure disjoint_add_rightL disjoint_sym partial_add_commute)

lemma \<open>is_sepunit u \<Longrightarrow> a ## b \<Longrightarrow> a + b = u \<Longrightarrow> is_sepunit a\<close>
  unfolding is_sepunit_def subaddeq_def
  by (metis disjoint_add_rightL disjoint_sym partial_add_commute unit_sub_closure[of _ a b])


definition \<open>is_sepdup a \<equiv> a ## a \<and> a + a = a\<close>

lemma \<open>is_sepunit u \<Longrightarrow> is_sepdup u\<close>
  by (simp add: is_sepdup_def is_sepunit_def)

lemma sepdup_antimono_iff_positivity:
  \<open>(\<forall>a b. a \<preceq>\<^sub>+ b \<longrightarrow> is_sepdup b \<longrightarrow> is_sepdup a) \<longleftrightarrow>
    (\<forall>a b c. a ## b \<longrightarrow> a + b = c \<longrightarrow> c ## c \<longrightarrow> c + c = c \<longrightarrow> a + a = a)\<close>
  apply (rule iffI)
   apply (meson is_sepdup_def subaddeq_def; fail)
  apply (simp add: is_sepdup_def subaddeq_def, clarify)
  apply (meson disjoint_add_rightL disjoint_sym)
  done
  

lemma \<open>a \<preceq>\<^sub>+ b \<Longrightarrow> is_sepdup b \<Longrightarrow> is_sepdup a\<close>
  nitpick
  oops

end

context order
begin

definition covered_by :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (infix \<open>\<prec>\<^sub>c\<close> 50) where
  \<open>x \<prec>\<^sub>c y \<equiv> x < y \<and> (\<forall>z. x \<le> z \<longrightarrow> z < y \<longrightarrow> z = x)\<close>

end

context perm_alg
begin

text \<open> addition irreducible; cf. join/meet irreducible \<close>
definition sepadd_irr :: \<open>'a \<Rightarrow> bool\<close> where
  \<open>sepadd_irr x \<equiv> (\<not> sepadd_unit x) \<and> (\<forall>a b. a < x \<longrightarrow> b < x \<longrightarrow> a ## b \<longrightarrow> a + b < x)\<close>

definition \<open>foundation a \<equiv> {j. j \<le> a \<and> sepadd_irr j}\<close>

end

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
  \<open>rgsep_rely S \<equiv> (\<lambda>a b. \<exists>x y. (x, y) \<in> S \<and> framed_subresource_rel \<top> x y a b)\<^sup>*\<^sup>*\<close>

definition
  \<open>good_rely b \<equiv>
      (\<forall>j. sepadd_irr j \<longrightarrow>
        ((\<exists>x y. b x y \<and> j \<le> x \<and> \<not> j \<le> y) \<longrightarrow> (\<forall>x' y'. b x' y' \<longrightarrow> j \<le> x' \<and> \<not> j \<le> y')) \<and>
        ((\<exists>x y. b x y \<and> \<not> j \<le> x \<and> j \<le> y) \<longrightarrow> (\<forall>x' y'. b x' y' \<longrightarrow> \<not> j \<le> x' \<and> j \<le> y'))
      ) \<and>
      (\<forall>x y f. b x y \<longrightarrow> x ## f \<longrightarrow> y ## f \<longrightarrow> b (x + f) (y + f))\<close>

(*
lemma wsstable_sepconj_semidistrib_backwards:
  \<open>r = rgsep_rely S \<Longrightarrow>
    S = {a} \<Longrightarrow>
    deterministic (r - (=)) \<Longrightarrow>
    Ex1 P \<Longrightarrow> Ex1 Q \<Longrightarrow>
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
*)

(* The situation that we want to prove is
   { pa \<^emph> pb \<^emph> pc              }
   { pa \<^emph> pb  }         \<parallel> { pc }
    skip                \<parallel>
    { sp c\<^sup>\<star> (pa \<^emph> pb) } \<parallel>
     a       \<parallel>  b       \<parallel>  c
    { qa   } \<parallel> { qb   } \<parallel> { qc }
    { qa \<^emph> qb \<^emph> qc             }
*)
lemma (in perm_alg) wsstable_semidistrib_realistic:
  \<open>r = c\<^sup>*\<^sup>* \<Longrightarrow>
    \<forall>r\<in>{a,b,c}.
      (\<forall>x. \<not> r x x) \<and>
      (\<forall>x y z. r x y \<longrightarrow> r y z \<longrightarrow> \<not> r x z) \<and>
      frame_closed r \<and>
      Ex (pre_state r) \<and>
      deterministic r \<Longrightarrow>
    Ex1 pa \<Longrightarrow>
    Ex1 pb \<Longrightarrow>
    Ex1 pc \<Longrightarrow>
    \<comment> \<open> stability \<close>
    sp ((a \<squnion> b)\<^sup>*\<^sup>*) pc = pc \<Longrightarrow>
    sp ((a \<squnion> c)\<^sup>*\<^sup>*) pb' = pb' \<Longrightarrow>
    sp ((b \<squnion> c)\<^sup>*\<^sup>*) pa' = pa' \<Longrightarrow>
    sp ((a \<squnion> c)\<^sup>*\<^sup>*) pb = pb \<Longrightarrow>
    sp ((b \<squnion> c)\<^sup>*\<^sup>*) pa = pa \<Longrightarrow>
    sp (c\<^sup>*\<^sup>*) (pa \<^emph> pb) = pa' \<^emph> pb' \<Longrightarrow>
    \<comment> \<open> the goal \<close>
    pa' \<^emph> pb' \<^emph> pc \<le> sp (c\<^sup>*\<^sup>*) pa \<^emph> sp (c\<^sup>*\<^sup>*) pb \<^emph> pc\<close>
  nitpick
  oops

(*
class finite_sep_alg = distrib_sep_alg +
  assumes finite_univ: \<open>finite (UNIV :: 'a set)\<close>
  fixes \<II> :: \<open>'a set\<close>
  assumes \<open>\<II> = Collect sepadd_irr\<close>
begin

lemma \<open>sepadd_irr a \<Longrightarrow> sepadd_irr b \<Longrightarrow> a \<noteq> b \<Longrightarrow> a \<le> c \<Longrightarrow> b \<le> c \<Longrightarrow> a ## b\<close>
  apply (clarsimp simp add: sepadd_irr_distrib_eq)
  by (metis disjoint_preservation disjoint_sym dual_order.antisym le_iff_sepadd)

end
*)


subsection \<open> Refinement closure \<close>

lemma safe_refinement_mono:
  \<open>safe n prg hl hs r g q \<Longrightarrow> prg = (Atomic a) \<Longrightarrow> c \<le> a \<Longrightarrow> safe n (Atomic c) hl hs r g q\<close>
  apply (induct arbitrary: a c rule: safe.inducts)
   apply force
  apply (simp add: safe_sucE)
  apply (rule safe_suc)
        apply blast
       apply blast
      apply (clarsimp simp add: opstep_iff le_fun_def; fail)
     apply (clarsimp simp add: opstep_iff le_fun_def, metis)
    apply (clarsimp simp add: opstep_iff le_fun_def, metis)
  done

lemma refinement_atomic_condition1:
  \<open>b' \<le> b \<Longrightarrow> sp b (wlp R P) s \<le> Q \<Longrightarrow> sp b' (wlp R P) s \<le> Q\<close>
  using sp_rel_mono
  by auto

lemma refinement_atomic_condition2:
  \<open>b' \<le> b \<Longrightarrow> unframe_prop f b \<Longrightarrow> unframe_prop f b'\<close>
  oops


end