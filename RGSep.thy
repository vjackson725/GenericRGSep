theory RGSep
  imports Stabilisation
begin

subsection \<open> Seperation algebras + relations \<close>

definition
  \<open>minchange_rel (r :: ('a::semigroup_add) \<Rightarrow> 'a \<Rightarrow> bool) \<equiv>
    \<lambda>h1 h2. r h1 h2 \<and> (\<forall>h'. \<not>(\<forall>x. x + h' = x) \<longrightarrow> (\<nexists>h1' h2'. h1 = h1' + h' \<and> h2 = h2' + h'))\<close>

definition
  \<open>rel_frame_closed (r :: ('a::perm_alg) \<Rightarrow> 'a \<Rightarrow> bool) \<equiv>
      \<forall>h1 h2. r h1 h2 \<longrightarrow> (\<forall>h. h ## h1 \<longrightarrow> h ## h2 \<longrightarrow> r (h1 + h) (h2 + h))\<close>

definition
  \<open>rel_frame_cl (r :: ('a::perm_alg) \<Rightarrow> 'a \<Rightarrow> bool) \<equiv> \<lambda>h1 h2.
    r h1 h2 \<or>
      (\<exists>h1' h2'. r h1' h2' \<and> (\<exists>h'. h1' ## h' \<and> h2' ## h' \<and> h1 = h1' + h' \<and> h2 = h2' + h'))\<close>

lemma rel_frame_cl_is_least_frame_closure:
  \<open>rel_frame_cl r = (LEAST r'. r \<le> r' \<and> rel_frame_closed r')\<close>
  unfolding rel_frame_cl_def rel_frame_closed_def
  apply (rule Least_equality[symmetric])
   apply (rule conjI)
    apply force
  subgoal
    apply clarsimp
    apply (rule conjI)
     apply (force intro: disjoint_symm)
    apply (clarsimp, metis disjoint_add_rightL disjoint_add_rightR disjoint_add_right_commute
        partial_add_commute partial_add_left_commute)
    done
  apply (clarsimp, metis disjoint_symm predicate2D)
  done

lemma frame_closed_frame_cl_of_minimal_pairs_eq:
  \<open>rel_frame_closed r \<Longrightarrow> rel_frame_cl (minchange_rel r) = r\<close>
  unfolding rel_frame_cl_def rel_frame_closed_def minchange_rel_def
  apply (clarsimp simp add: fun_eq_iff)
  apply (rule iffI)
   apply (force simp add: disjoint_symm_iff)
  apply clarsimp
  oops

subsection \<open> Framed step relation \<close>

(* we need this in the perm_alg case, when we don't necessarily have a unit. *)
text \<open>
  This predicate ensures that an update between two subresources preserve the rest of the heap.
\<close>
definition
  \<open>framed_subresource_rel (ha::'a::perm_alg) ha' h h' \<equiv>
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
  apply (rule disjI2)
  apply (auto; fail)
  done


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

subsection \<open> For the variable restriction \<close>

definition
  \<open>atom_frame_pred p c \<equiv>
    all_atom_comm
      (\<lambda>b. \<forall>h1 h2 hf. b h1 h2 \<longrightarrow> p hf \<longrightarrow> h1 ## hf \<longrightarrow> h2 ## hf \<longrightarrow> b (h1 + hf) (h2 + hf))
      c\<close>

lemma atom_frame_pred_simps[simp]:
  \<open>atom_frame_pred p Skip \<longleftrightarrow> True\<close>
  \<open>atom_frame_pred p (c1 ;; c2) \<longleftrightarrow> atom_frame_pred p c1 \<and> atom_frame_pred p c2\<close>
  \<open>atom_frame_pred p (c1 \<^bold>+ c2) \<longleftrightarrow> atom_frame_pred p c1 \<and> atom_frame_pred p c2\<close>
  \<open>atom_frame_pred p (c1 \<parallel> c2) \<longleftrightarrow> atom_frame_pred p c1 \<and> atom_frame_pred p c2\<close>
  \<open>atom_frame_pred p (c\<^sup>\<star>) \<longleftrightarrow> atom_frame_pred p c\<close>
  \<open>atom_frame_pred p (Atomic b) \<longleftrightarrow>
    (\<forall>h1 h2 hf. b h1 h2 \<longrightarrow> p hf \<longrightarrow> h1 ## hf \<longrightarrow> h2 ## hf \<longrightarrow> b (h1 + hf) (h2 + hf))\<close>
  by (fastforce simp add: atom_frame_pred_def)+

lemma atom_frame_pred_antimono:
  \<open>p \<le> q \<Longrightarrow> atom_frame_pred q c \<Longrightarrow> atom_frame_pred p c\<close>
  by (induct c arbitrary: p q)
    (fastforce simp add: atom_frame_pred_def)+

lemma atom_frame_pred_mono:
  \<open>p \<le> q \<Longrightarrow> atom_frame_pred p c \<Longrightarrow> atom_frame_pred q c\<close>
  apply (induct c arbitrary: p q)
       apply (fastforce simp add: atom_frame_pred_def)+
  apply (clarsimp simp add: atom_frame_pred_def)
  oops

section \<open> Operational Semantics \<close>

definition \<open>frame_consistent f b \<equiv>
  \<forall>h1 h2. b h1 h2 \<longrightarrow>
    (\<forall>hf1. h1 ## hf1 \<longrightarrow> f hf1 \<longrightarrow>
      (\<exists>hf2. h2 ## hf2 \<and> f hf2 \<and> b (h1 + hf1) (h2 + hf2)))\<close>

definition
  \<open>frame_closed r \<equiv>
    \<forall>h h'. r h h' \<longrightarrow> (\<forall>hf. h ## hf \<longrightarrow> h' ## hf \<longrightarrow> r (h + hf) (h' + hf))\<close>

subsection \<open> Actions \<close>

datatype 'h act =
  Tau
  | Local 'h 'h
  | Env 'h 'h

lemma act_not_eq_iff:
  \<open>a \<noteq> Tau \<longleftrightarrow> (\<exists>h1 h2. a = Local h1 h2) \<or> (\<exists>h1 h2. a = Env h1 h2)\<close>
  \<open>(\<forall>h1 h2. a \<noteq> Local h1 h2) \<longleftrightarrow> a = Tau \<or> (\<exists>h1 h2. a = Env h1 h2)\<close>
  \<open>(\<forall>h1 h2. a \<noteq> Env h1 h2) \<longleftrightarrow> a = Tau \<or> (\<exists>h1 h2. a = Local h1 h2)\<close>
  by (meson act.distinct act.exhaust)+

subsection \<open> Operational semantics steps \<close>

inductive opstep :: \<open>('h::perm_alg) act \<Rightarrow> 'h \<times> 'h comm \<Rightarrow> 'h \<times> 'h comm \<Rightarrow> bool\<close> where
  seq_left[intro!]:
  \<open>(\<forall>ha hb. a \<noteq> Env ha hb) \<Longrightarrow>
    opstep a (h, c1) (h', c1') \<Longrightarrow>
    opstep a (h, c1 ;; c2) (h', c1' ;; c2)\<close>
| seq_right[intro!]: \<open>opstep Tau (h, Skip ;; c2) (h, c2)\<close>
| ndet_left[intro]: \<open>(\<forall>ha hb. a \<noteq> Env ha hb) \<Longrightarrow> opstep a (h, c1) s' \<Longrightarrow> opstep a (h, c1 \<^bold>+ c2) s'\<close>
| ndet_right[intro]: \<open>(\<forall>ha hb. a \<noteq> Env ha hb) \<Longrightarrow> opstep a (h, c2) s' \<Longrightarrow> opstep a (h, c1 \<^bold>+ c2) s'\<close>
| ndet_skip_left[intro!]: \<open>opstep Tau (h, Skip \<^bold>+ c2) (h, Skip)\<close>
| ndet_skip_right[intro!]: \<open>opstep Tau (h, c1 \<^bold>+ Skip) (h, Skip)\<close>
| par_left[intro]:
  \<open>(\<forall>ha hb. a \<noteq> Env ha hb) \<Longrightarrow>
    opstep a (h, s) (h', s') \<Longrightarrow>
    opstep a (h, s \<parallel> t) (h', s' \<parallel> t)\<close>
| par_right[intro]:
  \<open>(\<forall>ha hb. a \<noteq> Env ha hb) \<Longrightarrow>
    opstep a (h, t) (h', t') \<Longrightarrow>
    opstep a (h, s \<parallel> t) (h', s \<parallel> t')\<close>
| par_skip_left[intro!]: \<open>opstep Tau (h, Skip \<parallel> s2) (h, s2)\<close>
| par_skip_right[intro!]: \<open>opstep Tau (h, s1 \<parallel> Skip) (h, s1)\<close>
| iter_skip[intro]: \<open>opstep Tau (h, c\<^sup>\<star>) (h, Skip)\<close>
| iter_step[intro]: \<open>opstep Tau (h, c\<^sup>\<star>) (h, c ;; c\<^sup>\<star>)\<close>
| atom[intro!]:
  \<open>b ha ha' \<Longrightarrow>
    framed_subresource_rel ha ha' h h' \<Longrightarrow>
    opstep (Local ha ha') (h, Atomic b) (h', Skip)\<close>
| env[intro!]:
  \<open>framed_subresource_rel ha ha' (fst s) (fst s') \<Longrightarrow>
    snd s' = snd s \<Longrightarrow>
    opstep (Env ha ha') s s'\<close>

inductive_cases opstep_tauE[elim]: \<open>opstep Tau s s'\<close>
inductive_cases opstep_localE[elim]: \<open>opstep (Local x y) s s'\<close>
inductive_cases opstep_envE[elim]: \<open>opstep (Env x y) s s'\<close>

inductive_cases opstep_skipE[elim!]: \<open>opstep a (h, Skip) s'\<close>
inductive_cases opstep_seqE[elim]: \<open>opstep a (h, c1 ;; c2) s'\<close>
inductive_cases opstep_ndetE[elim]: \<open>opstep a (h, c1 \<^bold>+ c2) s'\<close>
inductive_cases opstep_parE[elim]: \<open>opstep a (h, c1 \<parallel> c2) s'\<close>
inductive_cases opstep_iterE[elim]: \<open>opstep a (h, c\<^sup>\<star>) s'\<close>
inductive_cases opstep_atomE[elim!]: \<open>opstep a (h, Atomic b) s'\<close>

inductive_cases opstep_tau_seqE[elim!]: \<open>opstep Tau (h, c1 ;; c2) s'\<close>
inductive_cases opstep_tau_ndetE[elim!]: \<open>opstep Tau (h, c1 \<^bold>+ c2) s'\<close>
inductive_cases opstep_tau_parE[elim!]: \<open>opstep Tau (h, c1 \<parallel> c2) s'\<close>
inductive_cases opstep_tau_iterE[elim!]: \<open>opstep Tau (h, c\<^sup>\<star>) s'\<close>

paragraph \<open> Pretty operational semantics \<close>

abbreviation(input) pretty_opstep :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _\<close> (\<open>_ \<midarrow>(_)\<rightarrow> _\<close> [60,0,60] 60) where
  \<open>hs \<midarrow>a\<rightarrow> ht \<equiv> opstep a hs ht\<close>

subsection \<open> operational semantics lemmas \<close>

lemma opstep_tau_iff:
  \<open>opstep Tau (h, Skip) s' \<longleftrightarrow> False\<close>
  \<open>opstep Tau (h, c1 ;; c2) s' \<longleftrightarrow>
    c1 = Skip \<and> s' = (h, c2) \<or>
    (\<exists>h' c1'. opstep Tau (h,c1) (h',c1') \<and> s' = (h', c1' ;; c2))\<close>
  \<open>opstep Tau (h, c1 \<^bold>+ c2) s' \<longleftrightarrow>
    c1 = Skip \<and> s' = (h, Skip) \<or>
    c2 = Skip \<and> s' = (h, Skip) \<or>
    opstep Tau (h, c1) s' \<or>
    opstep Tau (h, c2) s'\<close>
  \<open>opstep Tau (h, c1 \<parallel> c2) s' \<longleftrightarrow>
    c1 = Skip \<and> s' = (h, c2) \<or>
    c2 = Skip \<and> s' = (h, c1) \<or>
    (\<exists>h' c1'. opstep Tau (h,c1) (h',c1') \<and> s' = (h', c1' \<parallel> c2)) \<or>
    (\<exists>h' c2'. opstep Tau (h,c2) (h',c2') \<and> s' = (h', c1 \<parallel> c2'))\<close>
  \<open>opstep Tau (h, c\<^sup>\<star>) s' \<longleftrightarrow> s' = (h, Skip) \<or> s' = (h, c ;; c\<^sup>\<star>)\<close>
  \<open>opstep Tau (h, Atomic b) s' \<longleftrightarrow> False\<close>
  by force+

lemma opstep_not_env_iff:
  assumes
    \<open>\<forall>h1 h2. a \<noteq> Env h1 h2\<close>
  shows
    \<open>opstep a (h, Skip) s' \<longleftrightarrow> False\<close>
    \<open>opstep a (h, c1 ;; c2) s' \<longleftrightarrow>
      a = Tau \<and> c1 = Skip \<and> s' = (h, c2) \<or>
      (\<exists>h' c1'. opstep a (h,c1) (h',c1') \<and> s' = (h', c1' ;; c2))\<close>
    \<open>opstep a (h, c1 \<^bold>+ c2) s' \<longleftrightarrow>
      a = Tau \<and> c1 = Skip \<and> s' = (h, Skip) \<or>
      a = Tau \<and> c2 = Skip \<and> s' = (h, Skip) \<or>
      opstep a (h, c1) s' \<or>
      opstep a (h, c2) s'\<close>
    \<open>opstep a (h, c1 \<parallel> c2) s' \<longleftrightarrow>
      a = Tau \<and> c1 = Skip \<and> s' = (h, c2) \<or>
      a = Tau \<and> c2 = Skip \<and> s' = (h, c1) \<or>
      (\<exists>h' c1'. opstep a (h,c1) (h',c1') \<and> s' = (h', c1' \<parallel> c2)) \<or>
      (\<exists>h' c2'. opstep a (h,c2) (h',c2') \<and> s' = (h', c1 \<parallel> c2'))\<close>
    \<open>opstep a (h, c\<^sup>\<star>) s' \<longleftrightarrow> a = Tau \<and> s' = (h, Skip) \<or> a = Tau \<and> s' = (h, c ;; c\<^sup>\<star>)\<close>
    \<open>opstep a (h, Atomic b) (h', c') \<longleftrightarrow>
      (\<exists>ha ha'. a = Local ha ha' \<and> b ha ha' \<and> framed_subresource_rel ha ha' h h') \<and> c' = Skip\<close>
  using assms
  by (cases a; force simp add: opstep_tau_iff)+

lemma opstep_env_iff[simp]:
  \<open>opstep (Env ha ha') s s' \<longleftrightarrow> framed_subresource_rel ha ha' (fst s) (fst s') \<and> snd s' = snd s\<close>
  by fast

lemma opstep_tau_preserves_heap:
  assumes \<open>s \<midarrow>Tau\<rightarrow> s'\<close>
  shows \<open>fst s' = fst s\<close>
proof -
  { fix a
    have \<open>s \<midarrow>a\<rightarrow> s' \<Longrightarrow> a = Tau \<Longrightarrow> fst s' = fst s\<close>
      by (induct rule: opstep.inducts) force+
  }
  then show ?thesis
    using assms by force
qed

lemma opstep_to_ndet_no_subexprL:
  \<open>opstep a s s' \<Longrightarrow> snd s' = c1 \<^bold>+ c2 \<Longrightarrow> comm_subexpr (snd s) c1 \<Longrightarrow> False\<close>
  by (induct arbitrary: c1 c2 rule: opstep.inducts)
    (force dest: no_comm_subexpr_constructorsD comm_subexpr_subexprsD)+

lemma opstep_to_ndet_no_subexprR:
  \<open>opstep a s s' \<Longrightarrow> snd s' = c1 \<^bold>+ c2 \<Longrightarrow> comm_subexpr (snd s) c2 \<Longrightarrow> False\<close>
  by (induct arbitrary: c1 c2 rule: opstep.inducts)
    (force dest: no_comm_subexpr_constructorsD comm_subexpr_subexprsD)+

lemma opstep_same_commD:
  \<open>opstep a s s' \<Longrightarrow> snd s' = snd s \<Longrightarrow> (\<exists>s1 s2. a = Env s1 s2)\<close>
  apply (induct rule: opstep.induct)
               apply force
              apply force
             apply (metis comm_subexpr_refl opstep_to_ndet_no_subexprL snd_conv)
            apply (metis comm_subexpr_refl opstep_to_ndet_no_subexprR snd_conv)
           apply force+
  done

lemma all_atom_comm_opstep:
  assumes
    \<open>opstep a (h, c) (h', c')\<close>
    \<open>all_atom_comm p c\<close>
  shows
    \<open>all_atom_comm p c'\<close>
proof -
  { fix s s'
    assume \<open>opstep a s s'\<close>
      and \<open>all_atom_comm p (snd s)\<close>
    then have \<open>all_atom_comm p (snd s')\<close>
      by (induct rule: opstep.inducts) force+
  }
  then show ?thesis
    using assms
    by force
qed

lemmas all_atom_comm_opstepD =
  all_atom_comm_opstep[rotated]

lemma opstep_frame:
  \<open>s \<midarrow>a\<rightarrow> s' \<Longrightarrow>
    fst s ## hf \<Longrightarrow>
    fst s' ## hf \<Longrightarrow>
    (fst s + hf, snd s) \<midarrow>a\<rightarrow> (fst s' + hf, snd s')\<close>
  by (induct rule: opstep.induct)
    (force simp add: framed_subresource_rel_frame)+

lemma opstep_frame_consistent:
  \<open>opstep a s s' \<Longrightarrow>
    all_atom_comm (frame_consistent f) (snd s) \<Longrightarrow>
    fst s ## hf \<Longrightarrow>
    f hf \<Longrightarrow>
    \<exists>hf'. f hf' \<and> fst s' ## hf' \<and> opstep a (fst s + hf, snd s) (fst s' + hf', snd s')\<close>
  apply (induct arbitrary: hf rule: opstep.inducts)
               apply force+
   apply (clarsimp simp add: framed_subresource_rel_def frame_consistent_def)
   apply (erule disjE)
    apply (clarsimp, rename_tac h' h hf)
    apply (drule spec2, drule mp, assumption)
    apply (drule_tac x=hf in spec, drule mp, assumption)
    apply (clarsimp, rename_tac hf')
    apply (rule_tac x=hf' in exI)
    apply clarsimp
    apply (rule framed_subresource_relI2)
  oops

subsubsection \<open>sugared atomic programs\<close>



definition \<open>passert p \<equiv> \<lambda>a b. p a \<and> a = b\<close>

abbreviation \<open>Assert p \<equiv> Atomic (passert p)\<close>
abbreviation \<open>Assume p \<equiv> Atomic (\<lambda>a. p)\<close>

lemmas Assert_def = arg_cong[where f=Atomic, OF meta_eq_to_obj_eq[OF passert_def]]

lemma passert_simps[simp]:
  \<open>passert p a b \<longleftrightarrow> p a \<and> b = a\<close>
  by (force simp add: passert_def)

lemma opstep_assert[intro!]: \<open>p h \<Longrightarrow> opstep (Local h h) (h, Assert p) (h, Skip)\<close>
  by (force simp add: opstep.atom passert_def)

lemma opstep_assume[intro!]: \<open>q h' \<Longrightarrow> opstep (Local h h') (h, Assume q) (h', Skip)\<close>
  by (force simp add: opstep.atom rel_liftR_def)

subsubsection \<open> Skipped and Aborted Programs \<close>

definition \<open>can_compute s \<equiv> \<exists>a s'. (\<forall>h1 h2. a \<noteq> Env h1 h2) \<and> s \<midarrow>a\<rightarrow> s'\<close>

lemma can_compute_iff:
  \<open>can_compute (h, Skip) \<longleftrightarrow> False\<close>
  \<open>can_compute (h, c1 ;; c2) \<longleftrightarrow> c1 = Skip \<or> can_compute (h,c1)\<close>
  \<open>can_compute (h, c1 \<^bold>+ c2) \<longleftrightarrow>
    c1 = Skip \<or> c2 = Skip \<or> can_compute (h,c1) \<or> can_compute (h,c2)\<close>
  \<open>can_compute (h, c1 \<parallel> c2) \<longleftrightarrow>
    c1 = Skip \<or> c2 = Skip \<or> can_compute (h,c1) \<or> can_compute (h,c2)\<close>
  \<open>can_compute (h, c\<^sup>\<star>) \<longleftrightarrow> True\<close>
  \<open>can_compute (h, Atomic b) \<longleftrightarrow> (\<exists>ha ha' h'. b ha ha' \<and> framed_subresource_rel ha ha' h h')\<close>
  unfolding can_compute_def
  by (simp, blast del: opstep_seqE opstep_parE elim!: opstep_seqE opstep_parE)+

lemma not_skip_can_compute:
  \<open>c \<noteq> Skip \<Longrightarrow> \<exists>y. g h y \<Longrightarrow> atoms_guarantee g c \<Longrightarrow> can_compute (h, c)\<close>
  by (induct c arbitrary: h)
    (fastforce simp add: can_compute_iff)+

subsubsection \<open> Sugared programs \<close>

abbreviation \<open>IfThenElse p ct cf \<equiv> Assert p ;; ct \<^bold>+ Assert (-p) ;; cf\<close>
abbreviation \<open>WhileLoop p c \<equiv> (Assert p ;; c)\<^sup>\<star> ;; Assert (-p)\<close>



subsection \<open> Operational Semantics \<close>

inductive opsem
  :: \<open>('a::perm_alg) act list \<Rightarrow> 'a \<times> 'a comm \<Rightarrow> 'a \<times> 'a comm \<Rightarrow> bool\<close>
  where
  base[intro!]: \<open>opsem [] s s\<close>
| step[intro!]: \<open>s \<midarrow>a\<rightarrow> s' \<Longrightarrow> opsem as s' s'' \<Longrightarrow> opsem (a # as) s s''\<close>

inductive_cases opsem_NilE[elim!]: \<open>opsem [] s s'\<close>
inductive_cases opsem_ConsE[elim!]: \<open>opsem (a # as) s s'\<close>

lemma opsem_iff[simp]:
  \<open>opsem [] s s' \<longleftrightarrow> s' = s\<close>
  \<open>opsem (a # as) s s'' \<longleftrightarrow> (\<exists>s'. (s \<midarrow>a\<rightarrow> s') \<and> opsem as s' s'')\<close>
  by force+

paragraph \<open> pretty opsem \<close>

abbreviation(input) pretty_opsem :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _\<close> (\<open>_ \<midarrow>(_)\<rightarrow>\<^sup>\<star> _\<close> [60,0,60] 60) where
  \<open>hc \<midarrow>as\<rightarrow>\<^sup>\<star> hc' \<equiv> opsem as hc hc'\<close>

subsection \<open> Theorems about the operational semantics \<close>

paragraph \<open> Reverse-cons transitive closure rules \<close>

lemma opsem_step_rev:
  \<open>opsem as s s' \<Longrightarrow> s' \<midarrow>a\<rightarrow> s'' \<Longrightarrow> opsem (as @ [a]) s s''\<close>
  apply (induct rule: opsem.induct)
   apply (metis append_self_conv2 opsem.simps)
  apply force
  done

lemma opsem_step_revE:
  \<open>opsem (as @ [a]) s s'' \<Longrightarrow> (\<And>s'. opsem as s s' \<Longrightarrow> opstep a s' s'' \<Longrightarrow> P) \<Longrightarrow> P\<close>
  by (induct as arbitrary: a s s'')
    (simp, blast)+

lemma opsem_rev_cons_iff[simp]:
  \<open>opsem (as @ [a]) s s'' \<longleftrightarrow> (\<exists>s'. opsem as s s' \<and> (s' \<midarrow>a\<rightarrow> s''))\<close>
  by (meson opsem_step_rev opsem_step_revE)

lemma opsem_rev_induct[consumes 1, case_names Nil Snoc]:
  \<open>opsem as s s' \<Longrightarrow>
    (\<And>r s. P r [] s s) \<Longrightarrow>
    (\<And>s r a s' as s''.
      opsem as s s' \<Longrightarrow>
      opstep a s' s'' \<Longrightarrow>
      P r as s s' \<Longrightarrow>
      P r (as @ [a]) s s'') \<Longrightarrow>
    P r as s s'\<close>
  by (induct as arbitrary: s s' rule: rev_induct) force+

lemma opsem_stepI:
  \<open>s \<midarrow>a\<rightarrow> s' \<Longrightarrow> s \<midarrow>[a]\<rightarrow>\<^sup>\<star> s'\<close>
  by blast

lemma opsem_trans:
  \<open>s \<midarrow>as1\<rightarrow>\<^sup>\<star> s' \<Longrightarrow> s' \<midarrow>as2\<rightarrow>\<^sup>\<star> s'' \<Longrightarrow> s \<midarrow>as1 @ as2\<rightarrow>\<^sup>\<star> s''\<close>
  by (induct arbitrary: as2 s'' rule: opsem.induct)
    force+

lemma skipped_opsem_only_env:
  \<open>s \<midarrow>as\<rightarrow>\<^sup>\<star> s' \<Longrightarrow> snd s = Skip \<Longrightarrow> list_all (case_act \<bottom> \<bottom> \<top>) as\<close>
  by (induct rule: opsem.induct)
    (force elim: opstep.cases)+

(*
paragraph \<open> relation for reasoning about the effect if several environment steps \<close>

inductive env_chain :: \<open>('h::perm_alg) act list \<Rightarrow> 'h \<Rightarrow> 'h \<Rightarrow> bool\<close> where
  \<open>env_chain [] x x\<close>
| step_exact: \<open>env_chain as x z \<Longrightarrow> env_chain (Env y x # as) y z\<close>
| step_framed:
  \<open>x = xa + hf \<Longrightarrow>
    xa ## hf \<Longrightarrow>
    ya ## hf \<Longrightarrow>
    env_chain as (ya + hf) z \<Longrightarrow>
    env_chain (Env xa ya # as) x z\<close>

inductive_cases env_chain_NilE[elim!]: \<open>env_chain [] x z\<close>
inductive_cases env_chain_ConsE[elim!]: \<open>env_chain (a # as) x z\<close>

lemma env_chain_iff[simp]:
  \<open>env_chain [] x z \<longleftrightarrow> x = z\<close>
  \<open>env_chain (a # as) x z \<longleftrightarrow>
    (\<exists>y. a = Env x y \<and> env_chain as y z) \<or>
    (\<exists>xa ya hf. xa ## hf \<and> x = xa + hf \<and> ya ## hf \<and> a = Env xa ya \<and> env_chain as (ya + hf) z)\<close>
  by (force intro: env_chain.intros)+

definition
  \<open>frame_compatible_rel r \<equiv>
    (\<forall>a b. r a b \<longrightarrow> (\<forall>c. a ## c \<and> b ## c \<and> r (a + c) (b + c)))\<close>

lemma env_chain_rely:
  assumes
    \<open>env_chain as h h'\<close>
    \<open>frame_compatible_rel r\<close>
    \<open>list_all (case_act True r) as\<close>
  shows
    \<open>r\<^sup>*\<^sup>* h h'\<close>
  using assms
  unfolding frame_compatible_rel_def
  by (induct rule: env_chain.induct)
    (force intro: converse_rtranclp_into_rtranclp)+
*)

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
    all_atom_comm (frame_consistent f) c \<Longrightarrow>
    frame_consistent f r \<Longrightarrow>
    rgsat c r g (p \<^emph> f) (q \<^emph> f)\<close>
inductive_cases rgsep_doneE[elim]: \<open>rgsat Skip r g p q\<close>
inductive_cases rgsep_iterE[elim]: \<open>rgsat (c\<^sup>\<star>) r g p q\<close>
inductive_cases rgsep_parE[elim]: \<open>rgsat (s1 \<parallel> s2) r g p q\<close>
inductive_cases rgsep_atomE[elim]: \<open>rgsat (Atomic c) r g p q\<close>

lemma rgsat_weaken:
  \<open>rgsat c r' g' p' q' \<Longrightarrow>
    p \<le> p' \<Longrightarrow> q' \<le> q \<Longrightarrow> r \<le> r' \<Longrightarrow> g' \<le> g \<Longrightarrow>
    rgsat c r g p q\<close>
  apply (induct arbitrary: p r g q rule: rgsat.induct)
       apply (rule rgsat_done, metis le_supE sup.absorb_iff2 wsstable_disj_distrib wsstable_rely_mono)
      apply (rule_tac i=i in rgsat_iter)
          apply blast
         apply (simp; fail)
        apply (simp; fail)
       apply blast
      apply (meson order.trans wsstable_rely_le_antimono; fail)
     apply (meson order.eq_iff order.trans rgsat_ndet; fail)
    apply (meson order.eq_iff order.trans sup_mono rgsat_parallel; fail)
   apply (meson order.trans rgsat_atom; fail)
  sorry

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
  by (rule rgsat_weaken[OF rgsat_done _ _ order.refl order.refl, where p'=\<open>\<lfloor> p \<rfloor>\<^bsub>r\<^esub>\<close> and q'=p])
    (clarsimp simp add: wsstable_def swstable_def le_fun_def)+

inductive safe
  :: \<open>('s::perm_alg) act list \<Rightarrow> 's comm \<Rightarrow> 's \<Rightarrow>
        ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where
  safe_nil[intro!]: \<open>safe [] c h r g q\<close>
| safe_cons[intro!]:
  \<open>\<comment> \<open> the command does not fail + respects the guarantee \<close>
    (h, c) \<midarrow>a\<rightarrow> (h', c') \<Longrightarrow>
    \<comment> \<open> the command is frame safe \<close>
    (\<forall>hf. h ## hf \<longrightarrow> h' ## hf \<longrightarrow> (h + hf, c) \<midarrow>a\<rightarrow> (h' + hf, c')) \<Longrightarrow>
    \<comment> \<open> env steps respect the rely \<close>
    (\<forall>ha ha'. a = Env ha ha' \<longrightarrow> r ha ha' \<and> framed_subresource_rel h h' h h') \<Longrightarrow>
    \<comment> \<open> local steps respect the guarantee \<close>
    (\<forall>ha ha'. a = Local ha ha' \<longrightarrow> g ha ha') \<Longrightarrow>
    \<comment> \<open> if the result is Skip, the postcondition is established \<close>
    (c' = Skip \<longrightarrow> q h') \<Longrightarrow>
    \<comment> \<open> the subsequent execution is safe \<close>
    safe as c' h' r g q \<Longrightarrow>
    safe (a # as) c h r g q\<close>

inductive_cases safe_nilE[elim!]: \<open>safe [] c s r g q\<close>
inductive_cases safe_consE[elim!]: \<open>safe (a # as) c s r g q\<close>

lemma safe_nil_iff[simp]:
  \<open>safe [] c h r g q \<longleftrightarrow> True\<close>
  by force

lemma safe_cons_iff:
  \<open>safe (a # as) c h r g q \<longleftrightarrow>
    (\<exists>h' c'.
      (h, c) \<midarrow>a\<rightarrow> (h', c') \<and>
      (\<forall>hf. h ## hf \<longrightarrow> h' ## hf \<longrightarrow> (h + hf, c) \<midarrow>a\<rightarrow> (h' + hf, c')) \<and>
      (\<forall>ha ha'. a = Env ha ha' \<longrightarrow> r ha ha' \<and> framed_subresource_rel h h' h h') \<and>
      (\<forall>ha ha'. a = Local ha ha' \<longrightarrow> g ha ha') \<and>
      (c' = Skip \<longrightarrow> q h') \<and>
      safe as c' h' r g q)\<close>
  by (rule iffI, blast, force)

lemma opstep_nonenv_frame:
  \<open>opstep a s s' \<Longrightarrow>
    (\<forall>ha hb. a \<noteq> Env ha hb) \<Longrightarrow>
    s = (r, c) \<Longrightarrow>
    s' = (r', c') \<Longrightarrow>
    all_atom_comm (frame_consistent f) c \<Longrightarrow>
    f rf \<Longrightarrow>
    r ## rf \<Longrightarrow>
    (\<exists>rf'. r' ## rf' \<and> f rf' \<and> opstep a (r + rf, c) (r' + rf', c'))\<close>
  apply (induct arbitrary: r c r' c' rule: opstep.inducts)
               apply (fastforce simp add: opstep_not_env_iff frame_consistent_def)+
   apply (clarsimp simp add: framed_subresource_rel_def)
   apply (elim disjE; clarsimp)
    apply (clarsimp simp add: frame_consistent_def)
    apply (drule spec2, drule mp, assumption, drule spec, drule mp, assumption, clarsimp)
  oops


lemma opstep_tau_guarantee:
  \<open>opstep a s s' \<Longrightarrow>
    a = Tau \<Longrightarrow>
    s = (h, c) \<Longrightarrow>
    s' = (h', c') \<Longrightarrow>
    reflp g \<Longrightarrow>
    all_atom_comm ((\<ge>) g) c \<Longrightarrow>
    g h h'\<close>
  by (induct arbitrary: h c h' c' rule: opstep.inducts)
    (force simp add: reflpD)+

lemma opstep_env_same_comm:
  assumes
    \<open>opstep (Env ha ha') (h, c) (h', c')\<close>
    \<open>r ha ha'\<close>
  shows
    \<open>c' = c\<close>
proof -
  {
    fix a s s'
    have \<open>opstep a s s' \<Longrightarrow> \<exists>x y. a = Env x y \<Longrightarrow> case_act \<bottom> \<bottom> r a \<Longrightarrow> snd s' = snd s\<close>
      by (induct arbitrary: h c h' c' rule: opstep.inducts) force+
  }
  then show ?thesis
    using assms
    by force
qed

lemma opstep_preserves_all_atom_comm:
  assumes
    \<open>opstep a (h, c) (h', c')\<close>
    \<open>all_atom_comm p c\<close>
  shows \<open>all_atom_comm p c'\<close>
proof -
  { fix s s'
    have \<open>opstep a s s' \<Longrightarrow> all_atom_comm p (snd s) \<Longrightarrow> all_atom_comm p (snd s')\<close>
      by (induct arbitrary: h' rule: opstep.inducts) force+
  }
  then show ?thesis
    using assms
    by force
qed

lemmas rev_opstep_preserves_all_atom_comm = opstep_preserves_all_atom_comm[rotated]

thm opstep_frame

lemma safe_frame:
  \<open>safe as c h r g q \<Longrightarrow>
    all_atom_comm (frame_consistent f) c \<Longrightarrow>
    all_atom_comm ((\<ge>) g) c \<Longrightarrow>
    reflp g \<Longrightarrow>
    frame_consistent f r \<Longrightarrow>
    h ## hf \<Longrightarrow>
    f hf \<Longrightarrow>
    safe as c (h + hf) r g (q \<^emph> f)\<close>
proof (induct arbitrary: hf rule: safe.induct)
  case (safe_cons h c a h' c' r g q as hf1)
  moreover have
    \<open>h' ## hf1\<close>
    \<open>opstep a (h + hf1, c) (h' + hf1, c')\<close>
    using safe_cons.hyps(2) safe_cons.prems(1,5)
    sledgehammer
  ultimately show ?case
    apply -
    apply (rule safe.safe_cons)
         apply assumption
        apply (metis disjoint_add_leftR disjoint_add_swap disjoint_add_swap2 partial_add_assoc3)
       apply (metis framed_subresource_rel_refl)
      apply blast
     apply (metis sepconj_def)
    apply (metis opstep_preserves_all_atom_comm)
    done
qed fast

lemma safe_frame2:
  \<open>safe as c h r g q \<Longrightarrow>
    all_atom_comm (frame_consistent f) c \<Longrightarrow>
    all_atom_comm ((\<ge>) g) c \<Longrightarrow>
    frame_consistent f r \<Longrightarrow>
    reflp g \<Longrightarrow>
    h ## hf \<Longrightarrow>
    f hf \<Longrightarrow>
    safe as c (h + hf) r g (q \<^emph> \<lceil> f \<rceil>\<^bsub>r \<squnion> g\<^esub>)\<close>
proof (induct arbitrary: hf rule: safe.induct)
  case (safe_cons h c a h' c' r g q as hf1)
  moreover have
    \<open>h' ## hf1\<close>
    \<open>opstep a (h + hf1, c) (h' + hf1, c')\<close>
    using safe_cons.hyps(2) safe_cons.prems(5) by blast+
  ultimately show ?case
    apply -
    apply (rule safe.safe_cons)
         apply assumption
        apply (metis disjoint_add_leftR disjoint_add_swap disjoint_add_swap2 partial_add_assoc3)
       apply (metis framed_subresource_rel_refl)
      apply blast
     apply (metis predicate1D sepconj_iff wsstable_stronger)
    apply (metis opstep_preserves_all_atom_comm)
    done
qed fast

lemma safe_skip:
  assumes
    \<open>\<exists>s'. (h, Skip) \<midarrow>as\<rightarrow>\<^sup>\<star> s'\<close>
    \<open>list_all (case_act \<top> g r) as\<close>
    \<open>\<forall>h h'. r h h' \<longrightarrow> q h \<longrightarrow> q h'\<close>
    \<open>\<forall>h h'. r h h' \<longrightarrow> (\<forall>hf. h ## hf \<longrightarrow> h' ## hf \<longrightarrow> r (h + hf) (h' + hf))\<close>
    \<open>q h\<close>
  shows
    \<open>safe as Skip h r g q\<close>
  using assms
proof (induct as arbitrary: h)
  case (Cons a as)
  obtain se h' ha ha' where
    \<open>opsem as (h', Skip) se\<close>
    \<open>a = Env ha ha'\<close>
    \<open>framed_subresource_rel ha ha' h h'\<close>
    \<open>r ha ha'\<close>
    using Cons.prems(1-)
    by force
  moreover then have \<open>safe as Skip h' r g q\<close>
    using Cons.prems(2-)
    apply (intro Cons.hyps)
        apply blast
       apply force
      apply force
     apply force
    apply (simp add: framed_subresource_rel_def, blast)
    done
  ultimately show ?case
    using Cons.prems
    apply (intro safe_cons)
         apply (force split: act.splits)
        apply (force simp add: framed_subresource_rel_frame)
       apply force
      apply force
     apply (simp add: framed_subresource_rel_def, blast)
    apply force
    done
qed force

lemma safe_weaken:
  \<open>safe as c h r g q' \<Longrightarrow>
    q' \<le> q \<Longrightarrow>
    safe as c h r g q\<close>
  by (induct rule: safe.induct) force+

lemma opstep_tau_extendD:
  \<open>opstep a s s' \<Longrightarrow>
    a = Tau \<Longrightarrow>
    all_atom_comm (\<lambda>b. \<forall>s s'. b s s' \<longrightarrow> (\<forall>sa\<ge>s. \<exists>sa'\<ge>s'. b sa sa')) (snd s) \<Longrightarrow>
    fst s ## h2 \<Longrightarrow>
    \<exists>h''\<ge>fst s'. opstep a (fst s + h2, snd s) (h'', snd s')\<close>
  by (induct rule: opstep.induct)
    (force dest: partial_le_plus)+

lemma can_compute_frame:
  \<open>can_compute s \<Longrightarrow>
    all_atom_comm (\<lambda>b. \<forall>s s'. b s s' \<longrightarrow> (\<forall>sa\<ge>s. \<exists>sa'\<ge>s'. b sa sa')) (snd s) \<Longrightarrow>
    fst s ## r \<Longrightarrow>
    can_compute (fst s + r, snd s)\<close>
  unfolding can_compute_def
  using opstep_tau_extendD
  oops

lemma safe_subtrace:
  assumes inductive_assms:
    \<open>safe as c h r g q\<close>
    \<open>as = as1 @ as2\<close>
  shows
    \<open>safe as1 c h r g q\<close>
  using inductive_assms
proof (induct arbitrary: as1 as2 rule: safe.inducts)
  case (safe_nil c1 h r g q1)
  then show ?case by fast
next
  case (safe_cons h c h' c' g q as r)
  then show ?case
    by (fastforce simp add: Cons_eq_append_conv)
qed

lemma soundness:
  fixes p q :: \<open>'a::perm_alg \<Rightarrow> bool\<close>
  assumes \<open>rgsat c r g p q\<close>
    \<comment>\<open>and \<open>all_atom_comm ((\<ge>) g) c\<close>\<close>
    and \<open>list_all (case_act \<top> g r) as\<close>
    and \<open>c = Skip \<longrightarrow> list_all (case_act \<bottom> \<bottom> (\<lambda>ha ha'. \<exists>h'. framed_subresource_rel ha ha' h h')) as\<close>
    and 
      \<open>\<exists>s'. (h, Skip) \<midarrow>as\<rightarrow>\<^sup>\<star> s'\<close>
      \<open>\<forall>h h'. r h h' \<longrightarrow> q h \<longrightarrow> q h'\<close>
      \<open>frame_closed_rel r\<close>
      \<open>\<forall>h h'. r h h' \<longrightarrow> (\<forall>hf. h ## hf \<longrightarrow> h' ## hf \<longrightarrow> r (h + hf) (h' + hf))\<close>
\<comment>\<open> and \<open>reflp r\<close>
    and \<open>reflp g\<close>  \<close>
    and \<open>p h\<close>
  shows \<open>safe as c h r g q\<close>
  using assms
proof (induct c r g p q arbitrary: as h rule: rgsat.inducts)
  case (rgsat_done p r q g as h)
  then show ?case
    by (blast intro: safe_skip)
next
  case (rgsat_iter c r g p' q' p i q)
  then show ?case sorry
next
  case (rgsat_ndet s1 r g1 p q1 s2 g2 q2 g q)
  then show ?case sorry
next
  case (rgsat_parallel s1 r g2 g1 p1 q1 s2 p2 q2 g p q)
  then show ?case sorry
next
  case (rgsat_atom p b q g p' f q' r)
  then show ?case sorry
next
  case (rgsat_frame c r g p q f as)
  obtain h1 h2
    where
      \<open>h1 ## h2\<close>
      \<open>h = h1 + h2\<close>
      \<open>p h1\<close>
      \<open>f h2\<close>
    using rgsat_frame.prems
    by (clarsimp simp add: sepconj_def)
  then show ?case
    using rgsat_frame.hyps rgsat_frame.prems(1,2,4-)
    by (blast intro: safe_frame)
qed

end