theory RGSep
  imports Stabilisation
begin

section \<open> frame consistent predicate \<close>

definition \<open>frame_pred_extends f b \<equiv>
  \<forall>h1 h2 hf1.
    b h1 h2 \<longrightarrow> h1 ## hf1 \<longrightarrow> f hf1 \<longrightarrow>
      (\<exists>hf2. h2 ## hf2 \<and> f hf2 \<and> b (h1 + hf1) (h2 + hf2))\<close>

definition
  \<open>frame_pred_maintains f r \<equiv>
    \<forall>x y z. r x y \<longrightarrow> f z \<longrightarrow> x ## z \<longrightarrow> (y ## z \<and> r (x+z) (y+z))\<close>

lemma frame_pred_maintains_implies_extends:
  \<open>frame_pred_maintains f \<le> frame_pred_extends f\<close>
  unfolding frame_pred_maintains_def frame_pred_extends_def
  by auto

subsection \<open> Framed step relation \<close>

context perm_alg
begin

text \<open>
  This predicate ensures that an update between two subresources preserve the rest of the heap.
  We need this in the perm_alg case, when we don't necessarily have a unit.
\<close>
definition
  \<open>framed_subresource_rel (ha::'a) ha' h h' \<equiv>
    ha = h \<and> ha' = h' \<or> (\<exists>hf. ha ## hf \<and> ha' ## hf \<and> h = ha + hf \<and> h' = ha' + hf)\<close>

lemma framed_subresource_relI1:
  \<open>ha = h \<Longrightarrow> ha' = h' \<Longrightarrow> framed_subresource_rel ha ha' h h'\<close>
  by (simp add: framed_subresource_rel_def)

lemma framed_subresource_relI2:
  \<open>ha ## hf \<Longrightarrow> ha' ## hf \<Longrightarrow> h = ha + hf \<Longrightarrow> h' = ha' + hf \<Longrightarrow>
    framed_subresource_rel ha ha' h h'\<close>
  by (force simp add: framed_subresource_rel_def)

lemma framed_subresource_rel_refl[intro!]:
  \<open>framed_subresource_rel h h' h h'\<close>
  by (simp add: framed_subresource_rel_def)

lemma framed_subresource_rel_frame:
  \<open>framed_subresource_rel ha ha' h h' \<Longrightarrow>
    h ## hf \<Longrightarrow>
    h' ## hf \<Longrightarrow>
    framed_subresource_rel ha ha' (h + hf) (h' + hf)\<close>
  using disjoint_add_swap2 partial_add_assoc2
  apply (simp add: framed_subresource_rel_def)
  apply (erule disjE)
   apply blast
  apply metis
  done

lemma framed_subresource_rel_sym:
  \<open>framed_subresource_rel a b a' b' \<Longrightarrow> framed_subresource_rel b a b' a'\<close>
  using framed_subresource_rel_def by auto

end

lemma (in multiunit_sep_alg) mu_sep_alg_compatible_framed_subresource_rel_iff:
  assumes
    \<open>compatible h h'\<close>
  shows
  \<open>framed_subresource_rel ha ha' h h' \<longleftrightarrow>
    (\<exists>hf. ha ## hf \<and> ha' ## hf \<and> h = ha + hf \<and> h' = ha' + hf)\<close>
  by (metis assms compatible_then_same_unit framed_subresource_rel_def unitof_disjoint2
      unitof_is_unitR2)

lemma (in sep_alg) sep_alg_framed_subresource_rel_iff:
  \<open>framed_subresource_rel ha ha' h h' \<longleftrightarrow>
    (\<exists>hf. ha ## hf \<and> ha' ## hf \<and> h = ha + hf \<and> h' = ha' + hf)\<close>
  by (metis framed_subresource_rel_def sepadd_0_right zero_disjointR)


section \<open> Language Definition \<close>

subsection \<open> Commands \<close>

datatype 'h comm =
  Skip
  | Seq \<open>'h comm\<close> \<open>'h comm\<close> (infixr \<open>;;\<close> 75)
  | Par \<open>'h comm\<close> \<open>'h comm\<close> (infixr \<open>\<parallel>\<close> 65)
  | Ndet \<open>'h comm\<close> \<open>'h comm\<close> (infixr \<open>\<^bold>+\<close> 65)
  | Iter \<open>'h comm\<close> (\<open>_\<^sup>\<star>\<close> [80] 80)
  | Atomic \<open>'h \<Rightarrow> 'h \<Rightarrow> bool\<close>

paragraph \<open> Predicate to determine if a command is a subexpression of another \<close>

primrec comm_subexpr :: \<open>'a comm \<Rightarrow> 'a comm \<Rightarrow> bool\<close> where
  \<open>comm_subexpr c Skip = (c = Skip)\<close>
| \<open>comm_subexpr c (c1' ;; c2') = (c = c1' ;; c2' \<or> comm_subexpr c c1' \<or> comm_subexpr c c2')\<close>
| \<open>comm_subexpr c (c1' \<parallel> c2') = (c = c1' \<parallel> c2' \<or> comm_subexpr c c1' \<or> comm_subexpr c c2')\<close>
| \<open>comm_subexpr c (c1' \<^bold>+ c2') = (c = c1' \<^bold>+ c2' \<or> comm_subexpr c c1' \<or> comm_subexpr c c2')\<close>
| \<open>comm_subexpr c (c'\<^sup>\<star>) = (c = c'\<^sup>\<star> \<or> comm_subexpr c c')\<close>
| \<open>comm_subexpr c (Atomic b) = (c = Atomic b)\<close>

lemma comm_subexpr_refl[simp]:
  \<open>comm_subexpr c c\<close>
  by (induct c) simp+

lemma comm_subexpr_trans:
  \<open>comm_subexpr c1 c2 \<Longrightarrow> comm_subexpr c2 c3 \<Longrightarrow> comm_subexpr c1 c3\<close>
  by (induct c3 arbitrary: c1 c2) force+

lemma comm_subexpr_antisym:
  \<open>comm_subexpr c1 c2 \<Longrightarrow> comm_subexpr c2 c1 \<Longrightarrow> c1 = c2\<close>
  by (induct c2 arbitrary: c1)
    (metis comm_subexpr.simps comm_subexpr_refl comm_subexpr_trans)+

lemma no_comm_subexpr_constructorsD:
  \<open>comm_subexpr (c1 ;; c2) c \<Longrightarrow> comm_subexpr c c1 \<Longrightarrow> False\<close>
  \<open>comm_subexpr (c1 ;; c2) c \<Longrightarrow> comm_subexpr c c2 \<Longrightarrow> False\<close>
  \<open>comm_subexpr (c1 \<^bold>+ c2) c \<Longrightarrow> comm_subexpr c c1 \<Longrightarrow> False\<close>
  \<open>comm_subexpr (c1 \<^bold>+ c2) c \<Longrightarrow> comm_subexpr c c2 \<Longrightarrow> False\<close>
  \<open>comm_subexpr (c1 \<parallel> c2) c \<Longrightarrow> comm_subexpr c c1 \<Longrightarrow> False\<close>
  \<open>comm_subexpr (c1 \<parallel> c2) c \<Longrightarrow> comm_subexpr c c2 \<Longrightarrow> False\<close>
  \<open>comm_subexpr (cb\<^sup>\<star>) c \<Longrightarrow> comm_subexpr c cb \<Longrightarrow> False\<close>
  by (fastforce dest: comm_subexpr_antisym)+

lemma comm_subexpr_subexprsD:
  \<open>comm_subexpr (c1 ;; c2) c \<Longrightarrow> comm_subexpr c1 c\<close>
  \<open>comm_subexpr (c1 ;; c2) c \<Longrightarrow> comm_subexpr c2 c\<close>
  \<open>comm_subexpr (c1 \<^bold>+ c2) c \<Longrightarrow> comm_subexpr c1 c\<close>
  \<open>comm_subexpr (c1 \<^bold>+ c2) c \<Longrightarrow> comm_subexpr c2 c\<close>
  \<open>comm_subexpr (c1 \<parallel> c2) c \<Longrightarrow> comm_subexpr c1 c\<close>
  \<open>comm_subexpr (c1 \<parallel> c2) c \<Longrightarrow> comm_subexpr c2 c\<close>
  \<open>comm_subexpr (cb\<^sup>\<star>) c \<Longrightarrow> comm_subexpr cb c\<close>
  by (meson comm_subexpr.simps comm_subexpr_refl comm_subexpr_trans)+

paragraph \<open> Predicate to ensure atomic actions have a given property \<close>

inductive all_atom_comm :: \<open>(('h \<Rightarrow> 'h \<Rightarrow> bool) \<Rightarrow> bool) \<Rightarrow> 'h comm \<Rightarrow> bool\<close> where
  skip[iff]: \<open>all_atom_comm p Skip\<close>
| seq[intro!]: \<open>all_atom_comm p c1 \<Longrightarrow> all_atom_comm p c2 \<Longrightarrow> all_atom_comm p (c1 ;; c2)\<close>
| par[intro!]: \<open>all_atom_comm p c1 \<Longrightarrow> all_atom_comm p c2 \<Longrightarrow> all_atom_comm p (c1 \<parallel> c2)\<close>
| ndet[intro!]: \<open>all_atom_comm p c1 \<Longrightarrow> all_atom_comm p c2 \<Longrightarrow> all_atom_comm p (c1 \<^bold>+ c2)\<close>
| iter[intro!]: \<open>all_atom_comm p c \<Longrightarrow> all_atom_comm p (c\<^sup>\<star>)\<close>
| atom[intro!]: \<open>p b \<Longrightarrow> all_atom_comm p (Atomic b)\<close>

inductive_cases all_atom_comm_doneE[elim!]: \<open>all_atom_comm p Skip\<close>
inductive_cases all_atom_comm_seqE[elim!]: \<open>all_atom_comm p (c1 ;; c2)\<close>
inductive_cases all_atom_comm_ndetE[elim!]: \<open>all_atom_comm p (c1 \<^bold>+ c2)\<close>
inductive_cases all_atom_comm_parE[elim!]: \<open>all_atom_comm p (c1 \<parallel> c2)\<close>
inductive_cases all_atom_comm_iterE[elim!]: \<open>all_atom_comm p (c\<^sup>\<star>)\<close>
inductive_cases all_atom_comm_atomE[elim!]: \<open>all_atom_comm p (Atomic b)\<close>

lemma all_atom_comm_simps[simp]:
  \<open>all_atom_comm p Skip \<longleftrightarrow> True\<close>
  \<open>all_atom_comm p (c1 ;; c2) \<longleftrightarrow> all_atom_comm p c1 \<and> all_atom_comm p c2\<close>
  \<open>all_atom_comm p (c1 \<^bold>+ c2) \<longleftrightarrow> all_atom_comm p c1 \<and> all_atom_comm p c2\<close>
  \<open>all_atom_comm p (c1 \<parallel> c2) \<longleftrightarrow> all_atom_comm p c1 \<and> all_atom_comm p c2\<close>
  \<open>all_atom_comm p (c\<^sup>\<star>) \<longleftrightarrow> all_atom_comm p c\<close>
  \<open>all_atom_comm p (Atomic b) \<longleftrightarrow> p b\<close>
  by fastforce+

lemma all_atom_comm_pred_mono:
  \<open>p \<le> q \<Longrightarrow> all_atom_comm p c \<Longrightarrow> all_atom_comm q c\<close>
  by (induct c) force+

lemmas all_atom_comm_pred_monoD =
  all_atom_comm_pred_mono[rotated]


abbreviation \<open>atoms_guarantee g \<equiv>
  all_atom_comm (\<lambda>b. b \<le> g \<and> (\<forall>s. Ex (g s) \<longrightarrow> Ex (b s)))\<close>


section \<open> Rely-Guarantee Separation Logic \<close>

inductive rgsat
  :: \<open>('h::perm_alg) comm \<Rightarrow> ('h \<Rightarrow> 'h \<Rightarrow> bool) \<Rightarrow> ('h \<Rightarrow> 'h \<Rightarrow> bool) \<Rightarrow> ('h \<Rightarrow> bool) \<Rightarrow> ('h \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where
  rgsat_skip:
  \<open>\<lceil> p \<rceil>\<^bsub>r\<^esub> \<le> q \<Longrightarrow> rgsat Skip r g p q\<close>
| rgsat_iter:
  \<open>rgsat c r g p' q' \<Longrightarrow>
      p \<le> i \<Longrightarrow> i \<le> p' \<Longrightarrow> q' \<le> i \<Longrightarrow> \<lceil> i \<rceil>\<^bsub>r\<^esub> \<le> q \<Longrightarrow>
      rgsat (c\<^sup>\<star>) r g p q\<close>
| rgsat_ndet:
  \<open>rgsat s1 r g1 p q1 \<Longrightarrow>
    rgsat s2 r g2 p q2 \<Longrightarrow>
    g1 \<le> g \<Longrightarrow> g2 \<le> g \<Longrightarrow>
    q1 \<le> q \<Longrightarrow> q2 \<le> q \<Longrightarrow>
    rgsat (s1 \<^bold>+ s2) r g p q\<close>
| rgsat_parallel:
  \<open>rgsat s1 (r \<squnion> g2) g1 p1 q1 \<Longrightarrow>
    rgsat s2 (r \<squnion> g1) g2 p2 q2 \<Longrightarrow>
    g1 \<le> g \<Longrightarrow> g2 \<le> g \<Longrightarrow>
    p \<le> p1 \<^emph> p2 \<Longrightarrow>
    q1 \<^emph> q2 \<le> q \<Longrightarrow>
    rgsat (s1 \<parallel> s2) r g p q\<close>
| rgsat_atom:
  \<open>rel_liftL p \<sqinter> b \<le> rel_liftR q \<Longrightarrow>
    b \<le> g \<Longrightarrow>
    p' \<le> p \<^emph> f \<Longrightarrow>
    q \<^emph> f \<le> q' \<Longrightarrow>
    rgsat (Atomic b) r g p' q'\<close>
| rgsat_frame:
  \<open>rgsat c r g p q \<Longrightarrow>
    all_atom_comm (frame_pred_maintains f) c \<Longrightarrow>
    frame_pred_extends f r \<Longrightarrow>
    rgsat c r g (p \<^emph> f) (q \<^emph> f)\<close>
| rgsat_weaken:
  \<open>rgsat c r' g' p' q' \<Longrightarrow>
    p \<le> p' \<Longrightarrow> q' \<le> q \<Longrightarrow> r \<le> r' \<Longrightarrow> g' \<le> g \<Longrightarrow>
    rgsat c r g p q\<close>
inductive_cases rgsep_doneE[elim]: \<open>rgsat Skip r g p q\<close>
inductive_cases rgsep_iterE[elim]: \<open>rgsat (c\<^sup>\<star>) r g p q\<close>
inductive_cases rgsep_parE[elim]: \<open>rgsat (s1 \<parallel> s2) r g p q\<close>
inductive_cases rgsep_atomE[elim]: \<open>rgsat (Atomic c) r g p q\<close>

lemma rgsat_iter':
  \<open>rgsat c r g i i \<Longrightarrow> rgsat (c\<^sup>\<star>) r g i (\<lceil> i \<rceil>\<^bsub>r\<^esub>)\<close>
  using rgsat_iter[OF _ order.refl order.refl order.refl]
  by blast
  

lemma frame_conj_helper:
  fixes p1 :: \<open>'a::cancel_perm_alg \<Rightarrow> bool\<close>
  assumes precise_f: \<open>\<And>h h'. (\<lceil> f \<rceil>\<^bsub>r1\<^esub>) h \<Longrightarrow> (\<lceil> f \<rceil>\<^bsub>r2\<^esub>) h' \<Longrightarrow> h' = h\<close>
  shows \<open>p1 \<^emph> \<lceil> f \<rceil>\<^bsub>r1\<^esub> \<sqinter> p2 \<^emph> \<lceil> f \<rceil>\<^bsub>r2\<^esub> \<le> (p1 \<sqinter> p2) \<^emph> \<lceil> f \<rceil>\<^bsub>r1 \<squnion> r2\<^esub>\<close>
  apply (clarsimp simp add: sepconj_def)
  apply (rename_tac h1a h1b h2a h2b)
  apply (frule(1) precise_f)
  apply simp
  apply (metis precise_f predicate1D wsstable_def wsstable_stronger)
  done

lemma backwards_frame:
  \<open>rgsat c r g p q \<Longrightarrow> rel_add_preserve (r\<^sup>*\<^sup>*) \<Longrightarrow> rgsat c r g (p \<^emph> \<lfloor> f \<rfloor>\<^bsub>r \<squnion> g\<^esub>) (q \<^emph> f)\<close>
  oops

lemma backwards_done:
  \<open>rgsat Skip r g (\<lfloor> p \<rfloor>\<^bsub>r\<^esub>) p\<close>
  by (rule rgsat_weaken[OF rgsat_skip _ _ order.refl order.refl, where p'=\<open>\<lfloor> p \<rfloor>\<^bsub>r\<^esub>\<close> and q'=p])
    (clarsimp simp add: wsstable_def swstable_def le_fun_def)+

end