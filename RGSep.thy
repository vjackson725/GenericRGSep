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


section \<open> Language Definition \<close>

datatype 'h comm =
  Stop
  | Seq \<open>'h comm\<close> \<open>'h comm\<close> (infixr \<open>;;\<close> 75)
  | Par \<open>'h comm\<close> \<open>'h comm\<close> (infixr \<open>\<parallel>\<close> 65)
  | Ndet \<open>'h comm\<close> \<open>'h comm\<close> (infixr \<open>\<^bold>+\<close> 65)
(*
  | ExtNdet \<open>'h comm\<close> \<open>'h comm\<close> (infixr \<open>\<^bold>\<box>\<close> 65)
*)
  | Iter \<open>'h comm\<close> (\<open>_\<^sup>\<star>\<close> [80] 80)
  | Atomic \<open>'h \<Rightarrow> 'h \<Rightarrow> bool\<close>

datatype 'h act =
    Tau
  | Env 'h 'h

lemma act_neq_iff[simp]:
  \<open>a \<noteq> Tau \<longleftrightarrow> (\<exists>x y. a = Env x y)\<close>
  \<open>Tau \<noteq> a \<longleftrightarrow> (\<exists>x y. a = Env x y)\<close>
  by (metis act.distinct(1) act.exhaust)+


paragraph \<open> Predicate to ensure atomic actions have a given property \<close>

inductive all_atom_comm :: \<open>(('h \<Rightarrow> 'h \<Rightarrow> bool) \<Rightarrow> bool) \<Rightarrow> 'h comm \<Rightarrow> bool\<close> where
  skip[iff]: \<open>all_atom_comm p Stop\<close>
| seq[intro!]: \<open>all_atom_comm p c1 \<Longrightarrow> all_atom_comm p c2 \<Longrightarrow> all_atom_comm p (c1 ;; c2)\<close>
| par[intro!]: \<open>all_atom_comm p c1 \<Longrightarrow> all_atom_comm p c2 \<Longrightarrow> all_atom_comm p (c1 \<parallel> c2)\<close>
| ndet[intro!]: \<open>all_atom_comm p c1 \<Longrightarrow> all_atom_comm p c2 \<Longrightarrow> all_atom_comm p (c1 \<^bold>+ c2)\<close>
| iter[intro!]: \<open>all_atom_comm p c \<Longrightarrow> all_atom_comm p (c\<^sup>\<star>)\<close>
| atom[intro!]: \<open>p b \<Longrightarrow> all_atom_comm p (Atomic b)\<close>

inductive_cases all_atom_comm_doneE[elim!]: \<open>all_atom_comm p Stop\<close>
inductive_cases all_atom_comm_seqE[elim!]: \<open>all_atom_comm p (c1 ;; c2)\<close>
inductive_cases all_atom_comm_ndetE[elim!]: \<open>all_atom_comm p (c1 \<^bold>+ c2)\<close>
inductive_cases all_atom_comm_parE[elim!]: \<open>all_atom_comm p (c1 \<parallel> c2)\<close>
inductive_cases all_atom_comm_iterE[elim!]: \<open>all_atom_comm p (c\<^sup>\<star>)\<close>
inductive_cases all_atom_comm_atomE[elim!]: \<open>all_atom_comm p (Atomic b)\<close>

lemma all_atom_comm_simps[simp]:
  \<open>all_atom_comm p Stop \<longleftrightarrow> True\<close>
  \<open>all_atom_comm p (c1 ;; c2) \<longleftrightarrow> all_atom_comm p c1 \<and> all_atom_comm p c2\<close>
  \<open>all_atom_comm p (c1 \<^bold>+ c2) \<longleftrightarrow> all_atom_comm p c1 \<and> all_atom_comm p c2\<close>
  \<open>all_atom_comm p (c1 \<parallel> c2) \<longleftrightarrow> all_atom_comm p c1 \<and> all_atom_comm p c2\<close>
  \<open>all_atom_comm p (c\<^sup>\<star>) \<longleftrightarrow> all_atom_comm p c\<close>
  \<open>all_atom_comm p (Atomic b) \<longleftrightarrow> p b\<close>
  by fastforce+

lemma all_atom_comm_mono:
  \<open>p \<le> q \<Longrightarrow> all_atom_comm p c \<Longrightarrow> all_atom_comm q c\<close>
  by (induct c) force+

lemmas all_atom_comm_monoD =
  all_atom_comm_mono[rotated]


abbreviation \<open>atoms_guarantee g \<equiv>
  all_atom_comm (\<lambda>b. b \<le> g \<and> (\<forall>s. Ex (g s) \<longrightarrow> Ex (b s)))\<close>

subsection \<open> For the variable restriction \<close>

definition
  \<open>atom_frame_pred p c \<equiv>
    all_atom_comm
      (\<lambda>b. \<forall>h1 h2 hf. b h1 h2 \<longrightarrow> p hf \<longrightarrow> h1 ## hf \<longrightarrow> h2 ## hf \<longrightarrow> b (h1 + hf) (h2 + hf))
      c\<close>

lemma atom_frame_pred_simps[simp]:
  \<open>atom_frame_pred p Stop \<longleftrightarrow> True\<close>
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

inductive opsem :: \<open>('h::perm_alg) act \<Rightarrow> 'h \<times> 'h comm \<Rightarrow> 'h \<times> 'h comm \<Rightarrow> bool\<close> where
  seq_left[intro!]: \<open>opsem a (h,c1) (h',c1') \<Longrightarrow> opsem a (h, c1 ;; c2) (h', c1' ;; c2)\<close>
| seq_right[intro!]: \<open>opsem Tau (h, Stop ;; c2) (h, c2)\<close>
| ndet_left[intro!]: \<open>opsem Tau (h, s \<^bold>+ t) (h, s)\<close>
| ndet_right[intro!]: \<open>opsem Tau (h, s \<^bold>+ t) (h, t)\<close>
(*
| extndet_resolve_left[intro]:
  \<open>opsem a (h, c1) (h', c1') \<Longrightarrow> a \<noteq> Tau \<Longrightarrow> opsem a (h, c1 \<^bold>\<box> c2) (h', c1')\<close>
| extndet_resolve_right[intro]:
  \<open>opsem a (h, c2) (h', c2') \<Longrightarrow> a \<noteq> Tau \<Longrightarrow> opsem a (h, c1 \<^bold>\<box> c2) (h', c2')\<close>
| extndet_step_left[intro]:
  \<open>opsem Tau (h, c1) (h', c1') \<Longrightarrow> opsem Tau (h, c1 \<^bold>\<box> c2) (h', c1' \<^bold>\<box> c2)\<close>
| extndet_step_right[intro]:
  \<open>opsem Tau (h, c2) (h', c2') \<Longrightarrow> opsem Tau (h, c1 \<^bold>\<box> c2) (h', c1 \<^bold>\<box> c2')\<close>
*)
| par_step_left[intro]: \<open>opsem a (h, s) (h', s') \<Longrightarrow> opsem a (h, s \<parallel> t) (h', s' \<parallel> t)\<close>
| par_step_right[intro]: \<open>opsem a (h, t) (h', t') \<Longrightarrow> opsem a (h, s \<parallel> t) (h', s \<parallel> t')\<close>
| par_left[intro!]: \<open>opsem Tau (h, Stop \<parallel> t) (h, t)\<close>
| par_right[intro!]: \<open>opsem Tau (h, s \<parallel> Stop) (h, s)\<close>
| iter[intro]: \<open>opsem Tau (h, c\<^sup>\<star>) (h, (Stop \<^bold>+ c) ;; c\<^sup>\<star>)\<close>
| atom[intro!]: \<open>b h h' \<Longrightarrow> opsem Tau (h, Atomic b) (h', Stop)\<close>
(* FIXME: testing out an external env relation *)
| env_exact[intro!]: \<open>opsem (Env a b) (h, t) (h', t)\<close>

inductive_cases opsem_seqE[elim!]: \<open>opsem a (h, c1 ;; c2) (h', c')\<close>
inductive_cases opsem_ndetE[elim!]: \<open>opsem a (h, c1 \<^bold>+ c2) (h', c')\<close>
inductive_cases opsem_parE[elim!]: \<open>opsem a (h, c1 \<parallel>  c2) (h', c')\<close>
inductive_cases opsem_iterE[elim!]: \<open>opsem a (h, c\<^sup>\<star>) (h', c')\<close>
inductive_cases opsem_atomE[elim!]: \<open>opsem a (h, Atomic g) (h', c')\<close>
inductive_cases opsem_skipE[elim!]: \<open>opsem a (h, Stop) (h', c')\<close>
inductive_cases opsem_envE[elim]: \<open>opsem (Env x y) s s'\<close>

paragraph \<open> Pretty operational semantics \<close>

abbreviation(input) pretty_opsem :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _\<close> (\<open>_ \<midarrow>(_)\<rightarrow> _\<close> [60,0,60] 60) where
  \<open>hs \<midarrow>a\<rightarrow> ht \<equiv> opsem a hs ht\<close>

subsection \<open> operational semantics lemmas \<close>

lemma opsem_tau_iff:
  \<open>opsem Tau (h, Stop) s' \<longleftrightarrow> False\<close>
  \<open>opsem Tau (h, c1 ;; c2) s' \<longleftrightarrow>
    c1 = Stop \<and> s' = (h, c2) \<or> (\<exists>h' c1'. opsem Tau (h,c1) (h',c1') \<and> s' = (h', c1' ;; c2))\<close>
  \<open>opsem Tau (h, c1 \<parallel> c2) s' \<longleftrightarrow>
    c1 = Stop \<and> s' = (h, c2) \<or>
    c2 = Stop \<and> s' = (h, c1) \<or>
    (\<exists>h' c1'. opsem Tau (h,c1) (h',c1') \<and> s' = (h', c1' \<parallel> c2) \<or>
    (\<exists>h' c2'. opsem Tau (h,c2) (h',c2') \<and> s' = (h', c1 \<parallel> c2')))\<close>
  \<open>opsem Tau (h, c1 \<^bold>+ c2) s' \<longleftrightarrow> s' = (h, c2) \<or> s' = (h, c1)\<close>
  \<open>opsem Tau (h, c\<^sup>\<star>) s' \<longleftrightarrow> s' = (h, (Stop \<^bold>+ c) ;; c\<^sup>\<star>)\<close>
  \<open>opsem Tau (h, Atomic g) s' \<longleftrightarrow> (\<exists>h'. g h h' \<and> s' = (h', Stop))\<close>
  by (cases s', force)+

(*
lemma opsem_envD:
  \<open>opsem a s s' \<Longrightarrow> a = Env x y \<Longrightarrow>
    (fst s = x \<and> fst s' = y \<or>
      (\<exists>hf. x ## hf \<and> y ## hf \<and> fst s = x + hf \<and> fst s' = y + hf)) \<and>
    snd s' = snd s\<close>
  by (induct arbitrary: x y rule: opsem.induct) force+

lemma opsem_env_same_unitD:
  fixes x y :: \<open>'a :: multiunit_sep_alg\<close>
  shows
  \<open>opsem a s s' \<Longrightarrow> a = Env x y \<Longrightarrow>
    unitof x = unitof y \<Longrightarrow>
    (\<exists>hf. x ## hf \<and> y ## hf \<and> fst s = x + hf \<and> fst s' = y + hf) \<and> snd s' = snd s\<close>
  by (drule opsem_envD, assumption, metis unitof_disjoint2 unitof_is_unitR2)

lemma opsem_env_sep_algD:
  fixes x y :: \<open>'a :: sep_alg\<close>
  shows
  \<open>opsem a s s' \<Longrightarrow> a = Env x y \<Longrightarrow>
    (\<exists>hf. x ## hf \<and> y ## hf \<and> fst s = x + hf \<and> fst s' = y + hf) \<and> snd s' = snd s\<close>
  by (force dest!: opsem_envD)

lemma opsem_env_iff:
  \<open>opsem (Env x y) s s' \<longleftrightarrow>
    (fst s = x \<and> fst s' = y \<or>
      (\<exists>hf. x ## hf \<and> y ## hf \<and> fst s = x + hf \<and> fst s' = y + hf)) \<and>
    snd s' = snd s\<close>
  by (rule iffI, metis opsem_envD, metis env_exact env_framed prod.collapse)

lemma opsem_env_sep_alg_iff:
  fixes x y :: \<open>'a :: sep_alg\<close>
  shows
  \<open>opsem (Env x y) s s' \<longleftrightarrow>
    (\<exists>hf. x ## hf \<and> y ## hf \<and> fst s = x + hf \<and> fst s' = y + hf) \<and>
    snd s' = snd s\<close>
  by (force simp add: opsem_env_iff)

lemma opsem_preserves_all_atom_comm:
  \<open>opsem a s s' \<Longrightarrow> all_atom_comm p (snd s) \<Longrightarrow> all_atom_comm p (snd s')\<close>
  by (induct rule: opsem.inducts) simp+
*)

subsubsection \<open>sugared atomic programs\<close>

definition \<open>passert p \<equiv> \<lambda>a b. p a \<and> a = b\<close>

abbreviation \<open>Assert p \<equiv> Atomic (passert p)\<close>
abbreviation \<open>Assume p \<equiv> Atomic (rel_liftR p)\<close>
abbreviation \<open>Skip \<equiv> Atomic (passert \<top>)\<close>

lemma passert_simps[simp]:
  \<open>passert p a b \<longleftrightarrow> p a \<and> b = a\<close>
  by (force simp add: passert_def)

lemma opsem_assert[intro!]: \<open>p h \<Longrightarrow> opsem Tau (h, Assert p) (h, Stop)\<close>
  by (simp add: opsem.atom passert_def)

lemma opsem_assume[intro!]: \<open>q h' \<Longrightarrow> opsem Tau (h, Assume q) (h', Stop)\<close>
  by (simp add: opsem.atom rel_liftR_def)

lemma opsem_skip[intro!]: \<open>opsem Tau (h, Skip) (h, Stop)\<close>
  by (simp add: opsem.atom passert_def)

subsubsection \<open> Sugared programs \<close>

abbreviation \<open>IfThenElse p ct cf \<equiv> Assert p ;; ct \<^bold>+ Assert (-p) ;; cf\<close>
abbreviation \<open>WhileLoop p c \<equiv> (Assert p ;; c)\<^sup>\<star> ;; Assert (-p)\<close>

(*
subsection \<open> Operational semantics transitive closure \<close>

(* TODO: infinite behaviou*)
(* TODO: actions *)
inductive opsem_rtrancl
  :: \<open>('a::perm_alg) act list \<Rightarrow> 'a \<times> 'a comm \<Rightarrow> 'a \<times> 'a comm \<Rightarrow> bool\<close>
  where
  base[intro!]: \<open>opsem_rtrancl [] s s\<close>
| step[intro!]: \<open>s \<midarrow>a\<rightarrow> s' \<Longrightarrow> opsem_rtrancl as s' s'' \<Longrightarrow> opsem_rtrancl (a # as) s s''\<close>

inductive_cases opsem_rtrancl_NilE[elim!]: \<open>opsem_rtrancl [] s s'\<close>
inductive_cases opsem_rtrancl_ConsE[elim!]: \<open>opsem_rtrancl (a # as) s s'\<close>

lemma opsem_rtrancl_iff[simp]:
  \<open>opsem_rtrancl [] s s' \<longleftrightarrow> s' = s\<close>
  \<open>opsem_rtrancl (a # as) s s'' \<longleftrightarrow> (\<exists>s'. (s \<midarrow>a\<rightarrow> s') \<and> opsem_rtrancl as s' s'')\<close>
  by force+

paragraph \<open> pretty opsem transitive closure \<close>

abbreviation(input) pretty_opsem_rtrancl :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _\<close> (\<open>_ \<midarrow>(_)\<rightarrow>\<^sup>\<star> _\<close> [60,0,60] 60) where
  \<open>hs \<midarrow>as\<rightarrow>\<^sup>\<star> ht \<equiv> opsem_rtrancl as hs ht\<close>

subsection \<open> Theorems about the operational semantics \<close>

paragraph \<open> Reverse-cons transitive closure rules \<close>

lemma opsem_rtrancl_step_rev:
  \<open>opsem_rtrancl as s s' \<Longrightarrow> s' \<midarrow>a\<rightarrow> s'' \<Longrightarrow> opsem_rtrancl (as @ [a]) s s''\<close>
  apply (induct rule: opsem_rtrancl.induct)
   apply (metis append_self_conv2 opsem_rtrancl.simps)
  apply force
  done

lemma opsem_rtrancl_step_revE:
  \<open>opsem_rtrancl (as @ [a]) s s'' \<Longrightarrow> (\<And>s'. opsem_rtrancl as s s' \<Longrightarrow> opsem a s' s'' \<Longrightarrow> P) \<Longrightarrow> P\<close>
  by (induct as arbitrary: a s s'') force+

lemma opsem_rtrancl_rev_cons_iff[simp]:
  \<open>opsem_rtrancl (as @ [a]) s s'' \<longleftrightarrow> (\<exists>s'. opsem_rtrancl as s s' \<and> (s' \<midarrow>a\<rightarrow> s''))\<close>
  by (meson opsem_rtrancl_step_rev opsem_rtrancl_step_revE)

lemma opsem_rtrancl_stepI:
  \<open>s \<midarrow>a\<rightarrow> s' \<Longrightarrow> s \<midarrow>[a]\<rightarrow>\<^sup>\<star> s'\<close>
  by blast

lemma opsem_rtrancl_trans:
  \<open>s \<midarrow>as1\<rightarrow>\<^sup>\<star> s' \<Longrightarrow> s' \<midarrow>as2\<rightarrow>\<^sup>\<star> s'' \<Longrightarrow> s \<midarrow>as1 @ as2\<rightarrow>\<^sup>\<star> s''\<close>
  by (induct arbitrary: as2 s'' rule: opsem_rtrancl.induct)
    force+

lemma opsem_rtrancl_rev_induct[consumes 1, case_names Nil Snoc]:
  \<open>opsem_rtrancl as s s' \<Longrightarrow>
    (\<And>r s. P r [] s s) \<Longrightarrow>
    (\<And>s r a s' as s''.
      opsem_rtrancl as s s' \<Longrightarrow>
      opsem a s' s'' \<Longrightarrow>
      P r as s s' \<Longrightarrow>
      P r (as @ [a]) s s'') \<Longrightarrow>
    P r as s s'\<close>
  by (induct as arbitrary: s s' rule: rev_induct) force+
*)

subsubsection \<open> Stopped and Aborted Programs \<close>

definition
  \<open>computing_or_stopped c s \<equiv>
    c = Stop \<or> (\<exists>s' c'. (s, c) \<midarrow>Tau\<rightarrow> (s', c'))\<close>

lemma done_stuck:
  \<open>\<nexists>s'. (h, Stop)  \<midarrow>Tau\<rightarrow> s'\<close>
  by force

lemma blocked_atom_stuck:
  \<open>\<nexists>h'. g h h' \<Longrightarrow> \<nexists>s'. (h, Atomic g)  \<midarrow>Tau\<rightarrow> s'\<close>
  by force

lemma nondone_nonstuck:
  \<open>c \<noteq> Stop \<Longrightarrow> \<forall>x. \<exists>y. g x y \<Longrightarrow> atoms_guarantee g c \<Longrightarrow> \<exists>s'. (h, c) \<midarrow>Tau\<rightarrow> s'\<close>
  by (induct c arbitrary: h) (fastforce simp add: opsem_tau_iff)+

lemma opsem_same_commD:
  \<open>opsem a s s' \<Longrightarrow> snd s' = snd s \<Longrightarrow> (\<exists>s1 s2. a = Env s1 s2)\<close>
(* a = Env (fst s) (fst s') \<or>
    (\<exists>h h' hf. a = Env h h' \<and> h ## hf \<and> h' ## hf \<and> fst s = h + hf \<and> fst s' = h' + hf) *)
  by (induct rule: opsem.induct) force+

(*
lemma opsem_same_comm:
  \<open>opsem a (h, c) (h', c) \<longleftrightarrow>
    a = Env h h' \<or>
    (\<exists>ha ha' hf. a = Env ha ha' \<and> ha ## hf \<and> ha' ## hf \<and> h = ha + hf \<and> h' = ha' + hf)\<close>
  apply (cases a)
   apply (simp, induct c; simp add: opsem_tau_iff; fail)
  apply (force simp add: opsem_env_iff)
  done
*)

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

definition \<open>semantic_frame f \<equiv> \<lambda>h1 h2. (\<exists>h1a\<le>h1. f h1a) \<longrightarrow> (\<exists>h2a\<le>h2. f h2a)\<close>

definition \<open>frame_consistent f b \<equiv>
  \<forall>h1 h2. b h1 h2 \<longrightarrow>
    (\<forall>hf1. h1 ## hf1 \<longrightarrow> f hf1 \<longrightarrow>
      (\<exists>hf2. h2 ## hf2 \<and> f hf2 \<and> b (h1 + hf1) (h2 + hf2)))\<close>

inductive rgsat
  :: \<open>('h::perm_alg) comm \<Rightarrow> ('h \<Rightarrow> 'h \<Rightarrow> bool) \<Rightarrow> ('h \<Rightarrow> 'h \<Rightarrow> bool) \<Rightarrow> ('h \<Rightarrow> bool) \<Rightarrow> ('h \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where
  rgsat_done:
  \<open>\<lceil> p \<rceil>\<^bsub>r\<^esub> \<le> q \<Longrightarrow> rgsat Stop r g p q\<close>
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
    stable (r \<squnion> g) f \<Longrightarrow>
    rgsat c r g (p \<^emph> f) (q \<^emph> f)\<close>
inductive_cases rgsep_doneE[elim]: \<open>rgsat Stop r g p q\<close>
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

(*
lemma rgsat_frame:
  assumes
    \<open>rgsat c r g p q\<close>
    \<comment> \<open>atom_frame_pred f c\<close>
    and extra:
    \<open>\<forall>p. \<forall>g'\<le>g. (\<lceil> p \<^emph> f \<rceil>\<^bsub>r \<squnion> g'\<^esub> \<le> \<lceil> p \<rceil>\<^bsub>r \<squnion> g'\<^esub> \<^emph> \<lceil> f \<rceil>\<^bsub>r \<squnion> g'\<^esub>)\<close>
    and \<open>stable (r \<squnion> g) f\<close>
  shows
    \<open>rgsat c r g (p \<^emph> f) (q \<^emph> f)\<close>
  using assms
proof (induct arbitrary: f rule: rgsat.induct)
  case (rgsat_done p r q g)
  moreover have \<open>\<And>p. \<lceil> p \<^emph> f \<rceil>\<^bsub>r\<^esub> \<le> \<lceil> p \<rceil>\<^bsub>r\<^esub> \<^emph> f\<close>
    using rgsat_done.prems(1,2)
    by (metis (no_types, lifting) Stabilisation.stable_def sup.order_iff sup_bot.right_neutral
        sup_ge1 wsstable_swstable_absorb)
  ultimately show ?case
    apply (intro rgsat.rgsat_done)
    apply (meson order.trans sepconj_monoL)
    done
next
  case (rgsat_iter c r g p' q' p i q f)
  then show ?case
    apply (rule_tac rgsat.rgsat_iter[where p'=\<open>p' \<^emph> f\<close> and q'=\<open>q' \<^emph> f\<close> and i=\<open>i \<^emph> f\<close>])
       apply (drule meta_spec[of _ f], drule meta_mp)
         apply blast
        apply blast
       apply (metis sepconj_monoL)
      apply (metis sepconj_monoL)
     apply (metis sepconj_monoL)
    apply (rule_tac b=\<open>\<lceil> i \<rceil>\<^bsub>r\<^esub> \<^emph> \<lceil> f \<rceil>\<^bsub>r\<^esub>\<close> in order.trans)
     apply (metis sup.order_iff sup_bot.right_neutral)
    apply (rule sepconj_mono, blast)
    apply (meson inf_sup_ord(3) stableD2 wsstable_rely_le_antimono)
    done
next
  case (rgsat_ndet s1 r g1 p q1 s2 g2 q2 g q)
  then show ?case
    apply (simp add: sup_fun_def)
    apply (intro rgsat.rgsat_ndet[where
          ?g1.0=g1 and ?g2.0=g2 and ?q1.0=\<open>q1 \<^emph> \<lceil> f \<rceil>\<^bsub>r \<squnion> g1\<^esub>\<close> and ?q2.0=\<open>q2 \<^emph> \<lceil> f \<rceil>\<^bsub>r \<squnion> g2\<^esub>\<close>])
    subgoal
      apply (rule rgsat_weaken[OF _ order.refl _ order.refl order.refl])
       apply (rule rgsat_ndet.hyps(2))
        apply (simp; fail)
       apply (meson le_less rgsat_ndet.prems(2) stable_antimono sup.mono)
      apply (metis sepconj_monoR wsstable_stronger)
      done
    subgoal
      apply (rule rgsat_weaken[OF _ order.refl _ order.refl order.refl])
       apply (rule rgsat_ndet.hyps(4))
        apply (simp; fail)
       apply (meson le_less rgsat_ndet.prems(2) stable_antimono sup.mono)
      apply (metis sepconj_monoR wsstable_stronger)
      done
       apply blast
      apply blast
     apply (rule_tac sepconj_mono, blast)
     apply (simp add: stable_iff2)
     apply (rule wsstable_rely_le_antimono[of _ \<open>\<lambda>a b. r a b \<or> g a b\<close>]; blast)
    apply (rule_tac sepconj_mono, blast)
    apply (simp add: stable_iff2)
    apply (rule wsstable_rely_le_antimono[of _ \<open>\<lambda>a b. r a b \<or> g a b\<close>]; blast)
    done
next
  case (rgsat_parallel s1 r g2 g1 p1 q1 s2 p2 q2 g p q)
  then show ?case
    apply -
      (* We choose to move the frame to c1. *)
    apply (rule rgsat.rgsat_parallel[where
          g=g and ?g1.0=g1 and ?g2.0=g2 and
            ?p1.0=\<open>p1 \<^emph> f\<close> and
            ?q1.0=\<open>q1 \<^emph> f\<close> and
            ?p2.0=\<open>p2\<close> and
            ?q2.0=\<open>q2\<close>])
    subgoal
      apply (drule meta_spec[of _ f], drule meta_mp)
       apply (metis (no_types, lifting) le_sup_iff order.trans sup_assoc)
      apply (drule meta_mp)
       apply (metis (mono_tags, lifting) stable_antimono sup.right_idem sup_ge1 sup_mono)
      apply blast
      done
        apply blast
       apply blast
      apply blast
     apply (metis sepconj_middle_monotone_rhsR2)
    apply (metis sepconj_middle_monotone_lhsR2)
    done
next
  case (rgsat_atom p b q g p' fa q' r f)
  then show ?case
    apply (rule_tac rgsat.rgsat_atom[where f=\<open>fa \<^emph> f\<close>])
       apply assumption
      apply assumption
     apply (metis sepconj_assoc sepconj_monoL)
    apply (simp add: sepconj_mono wsstable_stronger sepconj_assoc[symmetric]; fail)
    done
qed
*)

lemma backwards_frame:
  \<open>rgsat c r g p q \<Longrightarrow> rel_add_preserve (r\<^sup>*\<^sup>*) \<Longrightarrow> rgsat c r g (p \<^emph> \<lfloor> f \<rfloor>\<^bsub>r \<squnion> g\<^esub>) (q \<^emph> f)\<close>
  oops

lemma backwards_done:
  \<open>rgsat Stop r g (\<lfloor> p \<rfloor>\<^bsub>r\<^esub>) p\<close>
  by (rule rgsat_weaken[OF rgsat_done _ _ order.refl order.refl, where p'=\<open>\<lfloor> p \<rfloor>\<^bsub>r\<^esub>\<close> and q'=p])
    (clarsimp simp add: wsstable_def swstable_def le_fun_def)+

(*
lemma opsem_frame_strong:
  \<open>opsem_rtrancl as s s' \<Longrightarrow>
    list_all (case_act True r) as \<Longrightarrow>
    frame_compatible_rel r \<Longrightarrow>
    all_atom_comm (\<lambda>b. b \<le> semantic_frame f) (snd s) \<Longrightarrow>
    r \<le> semantic_frame f \<Longrightarrow>
    (\<exists>ha\<le>fst s. f ha) \<Longrightarrow>
    (\<exists>ha'\<le>fst s'. f ha')\<close>
proof (induct rule: opsem_rtrancl.induct)
  case (step s a s' as s'')

  have a_cases: \<open>case_act True r a\<close>
    using step(4) by simp

  have \<open>(\<exists>ha\<le>fst s'. f ha) \<and> all_atom_comm (\<lambda>b. b \<le> semantic_frame f) (snd s')\<close>
    using step(1,5-) a_cases
    proof (induct rule: opsem.induct)
      case (env_framed ha hf ha' h h' t)
      then show ?case
        by (fastforce simp add: frame_compatible_rel_def semantic_frame_def)
    qed (force simp add: semantic_frame_def)+
  then show ?case
    using step
    by (clarsimp split: act.splits)
qed fast

fun extend_act :: \<open>('h::plus) act \<Rightarrow> 'h \<Rightarrow> 'h \<Rightarrow> 'h act\<close> where
  \<open>extend_act Tau _ _ = Tau\<close>
| \<open>extend_act (Env a b) ra rb = Env (a + ra) (b + rb)\<close>

lemma opsem_frame:
  \<open>opsem a s s' \<Longrightarrow>
    all_atom_comm frame_compatible_rel (snd s) \<Longrightarrow>
    (\<exists>hr. f hr \<and> fst s' ## hr) \<Longrightarrow>
    f hf \<Longrightarrow>
    fst s ## hf \<Longrightarrow>
    (\<exists>hf'. f hf' \<and> fst s' ## hf' \<and> opsem (extend_act a hf hf') (fst s + hf, snd s) (fst s' + hf', snd s'))\<close>
  apply (induct arbitrary: hf rule: opsem.inducts)
             apply (fastforce simp add: semantic_frame_def)+
    apply (force simp add: frame_compatible_rel_def opsem_tau_iff)
   apply (force simp add: opsem_env_iff)
  apply (clarsimp simp add: opsem_env_iff)
  apply (rename_tac hb hr)
  apply (rule_tac x=hr in exI)
  apply simp
  apply (rule disjI2)
  apply (rule_tac x=hf in exI)
  apply (metis disjoint_add_leftL disjoint_add_swap disjoint_symm_iff partial_add_commute partial_add_left_commute)
  done

lemma opsem_rtrancl_frame:
  \<open>opsem_rtrancl as s s' \<Longrightarrow>
     list_all (case_act True (semantic_frame f)) as \<Longrightarrow>
     all_atom_comm (\<lambda>b. b \<le> semantic_frame f) (snd s) \<Longrightarrow>
     (\<exists>ha\<le>fst s. f ha) \<Longrightarrow> (\<exists>ha'\<le>fst s'. f ha')\<close>
  apply (induct rule: opsem_rtrancl.inducts)
   apply clarsimp
  apply clarsimp
  oops
  apply (frule opsem_frame, force, force, force)
  apply (metis fst_conv opsem_preserves_all_atom_comm snd_conv)
  done
*)

lemma implies_semantic_frame_sepconj:
  fixes f1 :: \<open>'a :: multiunit_sep_alg \<Rightarrow> bool\<close>
  assumes
    \<open>r \<le> semantic_frame f1\<close>
    \<open>r \<le> semantic_frame f2\<close>
    \<open>\<forall>h1 h2. f1 h1 \<longrightarrow> f2 h2 \<longrightarrow> h1 ## h2\<close>
    \<open>\<forall>h1 h2 h. f1 h1 \<longrightarrow> f2 h2 \<longrightarrow> h1 \<le> h \<longrightarrow> h2 \<le> h \<longrightarrow> h1 + h2 \<le> h\<close>
  shows
    \<open>r \<le> semantic_frame (f1 \<^emph> f2)\<close>
  using assms
  apply (clarsimp simp add: semantic_frame_def sepconj_def le_fun_def)
  apply (rename_tac h1' h2' h1 h2)
  apply (drule_tac x=h1' and y=h2' in spec2, drule mp, assumption)
  apply (drule_tac x=h1' and y=h2' in spec2, drule mp, assumption)
  apply (drule mp, rule_tac x=h1 in exI, metis order.trans partial_le_plus)
  apply (drule mp, rule_tac x=h2 in exI, metis order.trans partial_le_plus2)
  apply clarsimp
  apply (rename_tac h1a h2a)
  apply (rule_tac x=\<open>h1a + h2a\<close> in exI)
  apply blast
  done

inductive safe
  :: \<open>('s::perm_alg) act list \<Rightarrow> 's comm \<Rightarrow> 's \<Rightarrow>
        ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where
  safe_base[intro!]: \<open>safe [] c s r g q\<close>
| safe_tau[intro!]:
  \<open>\<comment> \<open> a stop command establishes the postcondition \<close>
    (c = Stop \<longrightarrow> q s) \<Longrightarrow>
    \<comment> \<open> under every frame, the command does not fail \<close>
    (\<forall>sf. s ## sf \<longrightarrow> computing_or_stopped c (s + sf)) \<Longrightarrow>
    \<comment> \<open> the command does not fail + respects the guarantee \<close>
    (s, c) \<midarrow>Tau\<rightarrow> (s', c') \<Longrightarrow>
    g s s' \<Longrightarrow>
    \<comment> \<open> the subsequent execution is safe \<close>
    safe as c' s' r g q \<Longrightarrow>
    safe (Tau # as) c s r g q\<close>
| safe_env[intro!]:
  \<open>\<comment> \<open> a stop command establishes the postcondition \<close>
    (c = Stop \<longrightarrow> q s) \<Longrightarrow>
    \<comment> \<open> the command does not fail + respects the guarantee \<close>
    (s, c) \<midarrow>Env s1 s2\<rightarrow> (s', c') \<Longrightarrow>
    \<comment> \<open> under every frame, the command does not fail \<close>
    (\<forall>sf. s ## sf \<longrightarrow> computing_or_stopped c (s + sf)) \<Longrightarrow>
    \<comment> \<open> the command respects the rely \<close>
    r s s' \<Longrightarrow>
    safe as c' s' r g q \<Longrightarrow>
    safe (Env s1 s2 # as) c s r g q\<close>

inductive_cases safe_NilE[elim!]: \<open>safe [] c s r g q\<close>
inductive_cases safe_tau_ConsE[elim!]: \<open>safe (Tau # as) c s r g q\<close>
inductive_cases safe_env_ConsE[elim!]: \<open>safe (Env x y # as) c s r g q\<close>

lemma safe_iff:
  \<open>safe [] c s r g q \<longleftrightarrow> True\<close>
  \<open>safe (Tau # as) c s r g q \<longleftrightarrow> (\<exists>c' s'.
    \<comment> \<open> a stop command establishes the postcondition \<close>
    (c = Stop \<longrightarrow> q s) \<and>
    \<comment> \<open> under every frame, the command does not fail \<close>
    (\<forall>sf. s ## sf \<longrightarrow> computing_or_stopped c (s + sf)) \<and>
    \<comment> \<open> the command does not fail + respects the guarantee \<close>
    (s, c) \<midarrow>Tau\<rightarrow> (s', c') \<and>
    g s s' \<and>
    \<comment> \<open> the subsequent execution is safe \<close>
    safe as c' s' r g q)\<close>
  \<open>safe (Env s1 s2 # as) c s r g q \<longleftrightarrow> (\<exists>s' c'.
    \<comment> \<open> a stop command establishes the postcondition \<close>
    (c = Stop \<longrightarrow> q s) \<and>
    \<comment> \<open> the command does not fail + respects the guarantee \<close>
    (s, c) \<midarrow>Env s1 s2\<rightarrow> (s', c') \<and>
    \<comment> \<open> under every frame, the command does not fail \<close>
    (\<forall>sf. s ## sf \<longrightarrow> computing_or_stopped c (s + sf)) \<and>
    \<comment> \<open> the command respects the rely \<close>
    r s s' \<and>
    safe as c' s' r g q)\<close>
  by fastforce+

declare safe_iff(1)[simp]

lemma opsem_tau_frame:
  \<open>opsem a s s' \<Longrightarrow>
    a = Tau \<Longrightarrow>
    s = (r, c) \<Longrightarrow>
    s' = (r', c') \<Longrightarrow>
    all_atom_comm (frame_consistent f) c \<Longrightarrow>
    f rf \<Longrightarrow>
    r ## rf \<Longrightarrow>
    (\<exists>rf'. r' ## rf' \<and> f rf' \<and> opsem Tau (r + rf, c) (r' + rf', c'))\<close>
  by (induct arbitrary: r c r' c' rule: opsem.inducts)
    (fastforce simp add: opsem_tau_iff frame_consistent_def)+

lemma opsem_tau_guarantee:
  \<open>opsem a s s' \<Longrightarrow>
    a = Tau \<Longrightarrow>
    s = (h, c) \<Longrightarrow>
    s' = (h', c') \<Longrightarrow>
    reflp g \<Longrightarrow>
    all_atom_comm ((\<ge>) g) c \<Longrightarrow>
    g h h'\<close>
  by (induct arbitrary: h c h' c' rule: opsem.inducts)
    (force simp add: reflpD)+

lemma opsem_env_same_comm:
  assumes
    \<open>opsem (Env x y) (h, c) (h', c')\<close>
    \<open>case_act True r (Env x y)\<close>
  shows
    \<open>c' = c\<close>
proof -
  {
    fix a s s'
    have \<open>opsem a s s' \<Longrightarrow> \<exists>x y. a = Env x y \<Longrightarrow> case_act True r a \<Longrightarrow> snd s' = snd s\<close>
      by (induct arbitrary: h c h' c' rule: opsem.inducts)
        (force simp add: reflpD)+
  }
  then show ?thesis
    using assms
    by auto
qed

lemma opsem_preserves_all_atom_comm:
  assumes
    \<open>opsem a (h, c) (h', c')\<close>
    \<open>all_atom_comm p c\<close>
  shows \<open>all_atom_comm p c'\<close>
proof -
  { fix s s'
    have \<open>opsem a s s' \<Longrightarrow> all_atom_comm p (snd s) \<Longrightarrow> all_atom_comm p (snd s')\<close>
      by (induct arbitrary: h' rule: opsem.inducts) force+
  }
  then show ?thesis
    using assms
    by force
qed

lemmas rev_opsem_preserves_all_atom_comm = opsem_preserves_all_atom_comm[rotated]

lemma safe_frame:
  \<open>safe as c h r g q \<Longrightarrow>
    all_atom_comm (frame_consistent f) c \<Longrightarrow>
    all_atom_comm ((\<ge>) g) c \<Longrightarrow>
    reflp g \<Longrightarrow>
    frame_consistent f r \<Longrightarrow>
    h ## hf \<Longrightarrow>
    f hf \<Longrightarrow>
    safe as c (h + hf) r g (q \<^emph> f)\<close>
  apply (induct arbitrary: hf rule: safe.induct)
    apply force

   apply (frule opsem_tau_frame, blast, blast, blast, blast, assumption, assumption)
   apply clarsimp
   apply (rule safe_tau)
       apply blast
      apply (simp add: disjoint_add_swap2 partial_add_assoc2; fail)
     apply assumption
    apply (drule opsem_tau_guarantee[where s=\<open>(_ + _, _)\<close>]; force)
   apply (force dest: opsem_preserves_all_atom_comm)

  apply (simp add: frame_consistent_def le_fun_def)
  apply (drule spec2, drule mp, assumption)
  apply (drule spec, drule mp[where P=\<open>_ ## _\<close>], assumption, drule mp, assumption)
  apply clarsimp
  apply (frule opsem_env_same_comm, force)
  apply (rule safe_env)
      apply (fastforce simp add: sepconj_def)
     apply blast
    apply (simp add: disjoint_add_swap2 partial_add_assoc2; fail)
   apply blast
  apply blast

  done

lemma safe_frame2:
  \<open>safe as c h r g q \<Longrightarrow>
    all_atom_comm (frame_consistent f) c \<Longrightarrow>
    all_atom_comm ((\<ge>) g) c \<Longrightarrow>
    frame_consistent f r \<Longrightarrow>
    reflp g \<Longrightarrow>
    h ## hf \<Longrightarrow>
    f hf \<Longrightarrow>
    safe as c (h + hf) r g (q \<^emph> \<lceil> f \<rceil>\<^bsub>r \<squnion> g\<^esub>)\<close>
  apply (induct arbitrary: hf rule: safe.induct)
    apply (rule safe_base)

  subgoal
    apply (frule opsem_tau_frame, blast, blast, blast, blast, assumption, assumption)
    apply clarsimp
    apply (rule safe_tau)
        apply force
       apply (simp add: disjoint_add_swap2 partial_add_assoc2; fail)
      apply assumption
     apply (drule opsem_tau_guarantee[where s=\<open>(_ + _, _)\<close>]; force)
    apply (force dest: opsem_preserves_all_atom_comm)
    done

  apply (frule opsem_env_same_comm, force)
  apply (simp add: frame_consistent_def le_fun_def)
  apply (drule spec2, drule mp, assumption)
  apply (drule spec, drule mp[where P=\<open>_ ## _\<close>], assumption, drule mp, assumption)
  apply clarsimp
  apply (rule safe_env)
      apply (force simp add: sepconj_def)
     apply blast
    apply (simp add: disjoint_add_swap2 partial_add_assoc2; fail)
   apply blast
  apply blast

  done

lemma soundness:
  fixes p q :: \<open>'a::multiunit_sep_alg \<Rightarrow> bool\<close>
  assumes \<open>rgsat c r g p q\<close>
    and
    \<open>all_atom_comm ((\<ge>) g) c\<close>
    \<open>reflp g\<close>
    and \<open>p s\<close>
  shows \<open>safe as c s r g q\<close>
  using assms
proof (induct c r g p q arbitrary: as s rule: rgsat.inducts)
  case (rgsat_done p r q g)
  then show ?case
    apply (case_tac as)
     apply blast
    apply clarsimp
    try0
    sorry
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
      \<open>s = h1 + h2\<close>
      \<open>p h1\<close>
      \<open>f h2\<close>
    using rgsat_frame.prems
    by (clarsimp simp add: sepconj_def)
  then show ?case
    using rgsat_frame.hyps rgsat_frame.prems(1-2)
    by (fastforce intro: safe_frame)
qed

end