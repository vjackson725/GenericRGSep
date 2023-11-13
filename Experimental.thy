theory Experimental
  imports Stabilisation
begin


class distrib_sep_alg = glb_multiunit_sep_alg + cancel_multiunit_sep_alg +
  assumes distrib_law:
    \<open>a ## b \<Longrightarrow> a ## c \<Longrightarrow>
      \<not> b ## c \<Longrightarrow> \<not> (a + b ## a + c) \<Longrightarrow>
         (a + b) \<sqinter> (a + c) \<le> a + (b \<sqinter> c)\<close>


class big_sep_alg = disjoint_parts_sep_alg + cancel_sep_alg +
  fixes join_irr :: \<open>'a set\<close>
  assumes join_irr_def:
    \<open>join_irr = {x. x \<noteq> 0 \<and> (\<forall>a b. a < x \<longrightarrow> b < x \<longrightarrow> a ## b \<longrightarrow> a + b < x)}\<close>
begin

lemma inf_exists:
  \<open>\<exists>!c. c \<le> a \<and> c \<le> b \<and> (\<forall>c'. c' \<le> a \<longrightarrow> c' \<le> b \<longrightarrow> c' \<le> c)\<close>
  nitpick
  oops

definition
  \<open>good_prog b \<equiv>
    (\<exists>A D F. A \<union> D \<union> F = join_irr \<and>
        A \<inter> D = {} \<and>
        A \<inter> F = {} \<and>
        D \<inter> F = {} \<and>
        (\<forall>a\<in>A. \<forall>a'\<in>A. a ## a') \<and>
        (\<forall>d\<in>D. \<forall>d'\<in>D. d ## d') \<and>
        (\<forall>x y. b x y \<longrightarrow>
          (\<forall>f\<in>F. f \<le> x \<longrightarrow> (\<exists>f'\<in>F. \<not> f ## f' \<and> f' \<le> y)) \<and> \<comment> \<open> transmute 1 \<close>
          (\<forall>f\<in>F. f \<le> y \<longrightarrow> (\<exists>f'\<in>F. \<not> f ## f' \<and> f' \<le> x)) \<and> \<comment> \<open> transmute 2 \<close>
          (\<forall>a\<in>A. \<not> a \<le> x \<and> a \<le> y) \<and> \<comment> \<open> allocate \<close>
          (\<forall>d\<in>D. d \<le> x \<and> \<not> d \<le> y)))  \<comment> \<open> deallocate \<close>\<close>

definition
  \<open>good_prog2 b \<equiv>
    (\<forall>x y. b x y \<longrightarrow> (\<forall>j\<in>join_irr.
      (j \<le> x \<longrightarrow> j \<le> y \<longrightarrow> (\<forall>x' y'. b x' y' \<longrightarrow> (j \<le> x' \<longleftrightarrow> j \<le> y'))) \<and>
      (j \<le> x \<longrightarrow> \<not> j \<le> y \<longrightarrow> (\<forall>x' y'. b x' y' \<longrightarrow> j \<le> x' \<and> \<not> j \<le> y')) \<and>
      (\<not> j \<le> x \<longrightarrow> j \<le> y \<longrightarrow> (\<forall>x' y'. b x' y' \<longrightarrow> \<not> j \<le> x' \<and> j \<le> y'))
    ))\<close>

lemma
  \<open>good_prog2 b \<Longrightarrow>
    r = b\<^sup>*\<^sup>* \<Longrightarrow>
    px = \<lfloor> p1 \<rfloor>\<^bsub>r\<^esub> \<Longrightarrow>
    py = \<lfloor> p2 \<rfloor>\<^bsub>r\<^esub> \<Longrightarrow>
    pxy = px \<^emph> py \<Longrightarrow>
    p = \<lfloor> p1 \<^emph> p2 \<rfloor>\<^bsub>r\<^esub> \<Longrightarrow>
    pxy \<le> p\<close>
  oops

lemma
  \<open>good_prog2 b \<Longrightarrow>
    z \<le> pre_state b \<Longrightarrow>
    r = b\<^sup>*\<^sup>* \<Longrightarrow>
    px = \<lceil> p1 \<rceil>\<^bsub>r\<^esub> \<Longrightarrow>
    py = \<lceil> p2 \<rceil>\<^bsub>r\<^esub> \<Longrightarrow>
    pxy = px \<^emph> py \<Longrightarrow>
    p = \<lceil> p1 \<^emph> p2 \<rceil>\<^bsub>r\<^esub> \<Longrightarrow>
    \<exists>!h. p1 h \<Longrightarrow>
    \<exists>!h. p2 h \<Longrightarrow>
    p \<^emph> z \<le> pxy \<^emph> z\<close>
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
    \<open>p1 = \<lfloor> p1x \<rfloor>\<^bsub>r1\<^esub>\<close>
    \<open>p2 = \<lfloor> p2x \<rfloor>\<^bsub>r2\<^esub>\<close>
    \<open>p3 = \<lfloor> p3x \<rfloor>\<^bsub>r3\<^esub>\<close>
    \<open>p1x \<le> pre_state b1\<close>
    \<open>p2x \<le> pre_state b2\<close>
    \<open>p3x \<le> pre_state b3\<close>
    \<open>q1 = \<lceil> post_state (rel_liftL p1x \<sqinter> b1) \<rceil>\<^bsub>r1\<^esub>\<close>
    \<open>q2 = \<lceil> post_state (rel_liftL p2x \<sqinter> b2) \<rceil>\<^bsub>r2\<^esub>\<close>
    \<open>q3 = \<lceil> post_state (rel_liftL p3x \<sqinter> b3) \<rceil>\<^bsub>r3\<^esub>\<close>
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
  shows
    \<open>(q \<le> qy)\<close>
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
    \<open>p1 \<le> pre_state b1\<close>
    \<open>p2 \<le> pre_state b2\<close>
    \<open>p3 \<le> pre_state b3\<close>
    \<open>p1 = \<lfloor> p1x \<rfloor>\<^bsub>r1\<^esub>\<close>
    \<open>p2 = \<lfloor> p2x \<rfloor>\<^bsub>r1\<^esub>\<close>
    \<open>p3 = \<lfloor> p3x \<rfloor>\<^bsub>r1\<^esub>\<close>
    \<open>q1 = \<lceil> post_state (rel_liftL p1x \<sqinter> b1) \<rceil>\<^bsub>r1\<^esub>\<close>
    \<open>q2 = \<lceil> post_state (rel_liftL p2x \<sqinter> b2) \<rceil>\<^bsub>r2\<^esub>\<close>
    \<open>q3 = \<lceil> post_state (rel_liftL p3x \<sqinter> b3) \<rceil>\<^bsub>r3\<^esub>\<close>
    \<open>q = \<lceil> q1 \<^emph> q2 \<rceil>\<^bsub>r12\<^esub> \<^emph> q3\<close>
  and \<comment> \<open> bad reasoning \<close>
    \<open>q1b = \<lceil> q1 \<rceil>\<^bsub>r12\<^esub>\<close>
    \<open>q2b = \<lceil> q2 \<rceil>\<^bsub>r12\<^esub> \<close>
    \<open>qy = q1b \<^emph> q2b \<^emph> q3\<close>
  shows
    \<open>(q \<le> qy)\<close>
  nitpick
  oops

end


end