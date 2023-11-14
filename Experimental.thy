theory Experimental
  imports Stabilisation PermHeap
begin

context perm_alg
begin

(* sepadd irreducible *)
definition sepadd_irr :: \<open>'a \<Rightarrow> bool\<close> where
  \<open>sepadd_irr x \<equiv> (\<not> unit_sepadd x) \<and> (\<forall>a b. a < x \<longrightarrow> b < x \<longrightarrow> a ## b \<longrightarrow> a + b < x)\<close>

end

instantiation pheap :: (compatible_glb_perm_alg, type, type) glb_sep_alg
begin

lift_definition inf_pheap :: \<open>('a,'b,'c) pheap \<Rightarrow> ('a,'b,'c) pheap \<Rightarrow> ('a,'b,'c) pheap\<close> is
  \<open>\<lambda>ha hb.
    (\<lambda>x. case ha x of Some (pa, va) \<Rightarrow>
          (case hb x of Some (pb, vb) \<Rightarrow>
            if va = vb
            then Some (pa \<sqinter> pb, va)
            else None
          | None \<Rightarrow> None)
        | None \<Rightarrow> None)\<close>
  by (simp add: dom_def option.case_eq_if)

lemma app_inf_pheap_eq:
  fixes a b :: \<open>('a,'b,'c) pheap\<close>
  shows
  \<open>(a \<sqinter> b) \<bullet> x =
    (case a \<bullet> x of Some (pa, va) \<Rightarrow>
          (case b \<bullet> x of Some (pb, vb) \<Rightarrow>
            if va = vb
            then Some (pa \<sqinter> pb, va)
            else None
          | None \<Rightarrow> None)
        | None \<Rightarrow> None)\<close>
  by (simp add: inf_pheap.rep_eq split: option.splits)

instance
  apply standard
    apply (force simp add: less_eq_pheap_def app_inf_pheap_eq split: option.splits)
   apply (force simp add: less_eq_pheap_def app_inf_pheap_eq split: option.splits)

  apply (simp add: all_compatible less_eq_pheap_def app_inf_pheap_eq split: option.splits)
  apply clarsimp
  apply (rule conjI, metis not_Some_prod_eq)
  apply clarsimp
  apply (rename_tac pa va)
  apply (rule conjI, metis not_Some_prod_eq)
  apply clarsimp
  apply (rename_tac pb vb)
  apply (rule conjI)
   apply fastforce
  apply clarsimp
  apply (rule ccontr)
  apply fastforce
  done

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

class distrib_sep_alg = glb_sep_alg +
  assumes inf_add_distrib1:
    \<open>\<And>x a b. a ## b \<Longrightarrow> x \<sqinter> (a + b) = (x \<sqinter> a) + (x \<sqinter> b)\<close>
begin

lemma False
  nitpick
  oops

lemma inf_add_distrib2:
    \<open>\<And>x a b. a ## b \<Longrightarrow> (a + b) \<sqinter> x = (a \<sqinter> x) + (b \<sqinter> x)\<close>
  by (simp add: inf_add_distrib1 inf_commute)

lemma distrib_join_disjoint: \<open>a ## b \<Longrightarrow> x \<sqinter> a ## x \<sqinter> b\<close>
  by (meson disjoint_preservation disjoint_symm inf.cobounded2)

lemma sepadd_irr_distrib_eq:
  shows \<open>sepadd_irr x \<longleftrightarrow> x \<noteq> 0 \<and> (\<forall>a b. a ## b \<longrightarrow> x \<le> a + b \<longrightarrow> x \<le> a \<or> x \<le> b)\<close>
  unfolding sepadd_irr_eq
  apply (rule iffI)
   apply (simp add: inf.order_iff inf_add_distrib1, metis disjoint_add_rightL disjoint_preservation
      le_iff_sepadd order.strict_implies_not_eq inf.cobounded1 inf.cobounded2 neq_le_trans)
  apply (force simp add: order.strict_iff_not inf.absorb_iff2 inf_add_distrib1)
  done

end

class big_sep_alg = disjoint_parts_sep_alg + cancel_perm_alg
begin

lemma False
  nitpick
  oops

definition \<open>foundation a \<equiv> {j. j \<le> a \<and> sepadd_irr j}\<close>

definition
  \<open>good_prog b \<equiv>
      (\<forall>j. sepadd_irr j \<longrightarrow>
        ((\<exists>x y. b x y \<and> j \<le> x \<and> \<not> j \<le> y) \<longrightarrow> (\<forall>x' y'. b x' y' \<longrightarrow> j \<le> x' \<and> \<not> j \<le> y')) \<and>
        ((\<exists>x y. b x y \<and> \<not> j \<le> x \<and> j \<le> y) \<longrightarrow> (\<forall>x' y'. b x' y' \<longrightarrow> \<not> j \<le> x' \<and> j \<le> y'))
      ) \<and>
      (\<forall>x y f. b x y \<longrightarrow> x ## f \<longrightarrow> y ## f \<longrightarrow> b (x + f) (y + f))\<close>

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


end