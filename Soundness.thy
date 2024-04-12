theory Soundness
  imports RGLogic "HOL-Library.FSet"
begin

(* TODO: move *)
declare member_rec[simp]

lemma Cons_neq_iff:
  \<open>a # as \<noteq> bs' \<longleftrightarrow> bs' = [] \<or> (\<exists>b bs. bs' = b # bs \<and> (a \<noteq> b \<or> as \<noteq> bs))\<close>
  by (induct bs' arbitrary: a as) force+


text \<open> list inclusion \<close>

inductive sublisteq :: \<open>'a list \<Rightarrow> 'a list \<Rightarrow> bool\<close> (infix \<open>\<le>\<^sub>l\<close> 50) where
  nil[intro, simp]: \<open>[] \<le>\<^sub>l ys\<close>
| same[intro]: \<open>xs \<le>\<^sub>l ys \<Longrightarrow> x # xs \<le>\<^sub>l x # ys\<close>

inductive_cases sublisteq_right_NilE[elim]: \<open>xs \<le>\<^sub>l []\<close>
inductive_cases sublisteq_right_ConsE[elim]: \<open>xs' \<le>\<^sub>l y # ys\<close>
inductive_cases sublisteq_left_ConsE[elim]: \<open>x # xs \<le>\<^sub>l ys'\<close>

lemma sublisteq_iff_append:
  \<open>xs \<le>\<^sub>l ys \<longleftrightarrow> (\<exists>zs. ys = xs @ zs)\<close>
  by (induct ys arbitrary: xs) 
    (force simp add: Cons_eq_append_conv)+

lemma sublisteq_Nil_iff[simp]:
  \<open>xs \<le>\<^sub>l [] \<longleftrightarrow> xs = []\<close>
  by blast

lemma Cons_sublisteq_iff:
  \<open>x # xs \<le>\<^sub>l ys' \<longleftrightarrow> (\<exists>ys. ys' = x # ys \<and> xs \<le>\<^sub>l ys)\<close>
  by blast

lemma sublisteq_Cons_iff:
  \<open>xs' \<le>\<^sub>l y # ys \<longleftrightarrow> xs' = [] \<or> (\<exists>xs. xs' = y # xs \<and> xs \<le>\<^sub>l ys)\<close>
  by blast

lemma sublisteq_ConsI1:
  \<open>xs' = [] \<Longrightarrow> xs' \<le>\<^sub>l y # ys\<close>
  by blast

lemma sublisteq_ConsI2:
  \<open>xs' = y # xs \<Longrightarrow> xs \<le>\<^sub>l ys \<Longrightarrow> xs' \<le>\<^sub>l y # ys\<close>
  by blast

lemma sublisteq_order:
  \<open>class.order (\<le>\<^sub>l) ((\<noteq>) \<sqinter> (\<le>\<^sub>l))\<close>
  by standard
    (force simp add: sublisteq_iff_append)+


text \<open> reverse list inclusion \<close>

inductive rev_sublisteq :: \<open>'a list \<Rightarrow> 'a list \<Rightarrow> bool\<close> (infix \<open>\<le>\<^sub>r\<close> 50) where
  same[intro, simp]: \<open>xs \<le>\<^sub>r xs\<close>
| cons[intro]: \<open>xs \<le>\<^sub>r ys \<Longrightarrow> xs \<le>\<^sub>r y # ys\<close>

inductive_cases rev_sublisteq_sameE[elim]: \<open>xs \<le>\<^sub>r xs\<close>
inductive_cases rev_sublisteq_left_NilE[elim]: \<open>[] \<le>\<^sub>r ys\<close>
inductive_cases rev_sublisteq_right_NilE[elim]: \<open>xs \<le>\<^sub>r []\<close>
inductive_cases rev_sublisteq_right_ConsE[elim]: \<open>xs' \<le>\<^sub>r y # ys\<close>
inductive_cases rev_sublisteq_left_ConsE[elim]: \<open>x # xs \<le>\<^sub>r ys'\<close>

lemma rev_sublisteq_impl_le_length:
  \<open>xs \<le>\<^sub>r ys \<Longrightarrow> length xs \<le> length ys\<close>
  by (induct rule: rev_sublisteq.inducts) simp+

lemma rev_sublisteq_Nil_iff[simp]:
  \<open>xs \<le>\<^sub>r [] \<longleftrightarrow> xs = []\<close>
  by blast

lemma Nil_rev_sublisteq_True[simp]:
  \<open>[] \<le>\<^sub>r ys\<close>
  by (induct ys; force)

lemma Cons_rev_sublisteq_Cons_iff:
  \<open>x # xs \<le>\<^sub>r y # ys \<longleftrightarrow> x # xs \<le>\<^sub>r ys \<or> x = y \<and> xs = ys\<close>
  by blast

(* beware, loops the simplifier *)
lemma Cons_rev_sublisteq_iff:
  \<open>x # xs \<le>\<^sub>r ys' \<longleftrightarrow> ys' = x # xs \<or> (\<exists>y ys. ys' = y # ys \<and> x # xs \<le>\<^sub>r ys)\<close>
  by (induct ys' arbitrary: x xs) blast+

lemma rev_sublisteq_Cons_iff:
  \<open>xs' \<le>\<^sub>r y # ys \<longleftrightarrow> xs' \<le>\<^sub>r ys \<or> xs' = y # ys\<close>
  by blast

lemma rev_sublisteq_iff_append:
  \<open>xs \<le>\<^sub>r ys \<longleftrightarrow> (\<exists>zs. ys = zs @ xs)\<close>
  by (induct ys arbitrary: xs)
    (force simp add: rev_sublisteq_Cons_iff Cons_eq_append_conv ex_disj_distrib)+

lemma rev_sublisteq_antisym:
  \<open>a \<le>\<^sub>r b \<Longrightarrow> b \<le>\<^sub>r a \<Longrightarrow> a = b\<close>
  by (metis impossible_Cons order_antisym rev_sublisteq.cases rev_sublisteq_impl_le_length)

lemma rev_sublisteq_trans[trans]:
  \<open>a \<le>\<^sub>r b \<Longrightarrow> b \<le>\<^sub>r c \<Longrightarrow> a \<le>\<^sub>r c\<close>
  by (metis append.assoc rev_sublisteq_iff_append)

lemma rev_sublisteq_order:
  \<open>class.order (\<le>\<^sub>r) ((\<noteq>) \<sqinter> (\<le>\<^sub>r))\<close>
  by standard
    (force simp add: rev_sublisteq_iff_append)+

lemma rev_sublisteq_less_induct[case_names less]:
  \<open>(\<And>xs. (\<And>xs'. xs' \<le>\<^sub>r xs \<Longrightarrow> xs' \<noteq> xs \<Longrightarrow> P xs') \<Longrightarrow> P xs) \<Longrightarrow> P zs\<close>
  apply (induct zs rule: length_induct)
  apply clarsimp
  apply (drule_tac x=xs in meta_spec)
  apply (force simp add: rev_sublisteq_iff_append)
  done

lemma rev_sublisteq_bounded_linearity:
  \<open>a \<le>\<^sub>r c \<Longrightarrow> b \<le>\<^sub>r c \<Longrightarrow> a \<le>\<^sub>r b \<or> b \<le>\<^sub>r a\<close>
  by (induct arbitrary: b rule: rev_sublisteq.inducts) blast+

lemma rev_sublisteq_list_strong_induct[case_names Nil ConsLess]:
  \<open>P [] \<Longrightarrow> (\<And>x xs. (\<And>xs'. xs' \<le>\<^sub>r xs \<Longrightarrow> P xs') \<Longrightarrow> P (x # xs)) \<Longrightarrow> P xs\<close>
  by (rule rev_sublisteq_less_induct,
      metis impossible_Cons neq_Nil_conv rev_sublisteq_Cons_iff rev_sublisteq_impl_le_length)

section \<open> Operational Semantics \<close>

subsection \<open> Actions \<close>

datatype 'a act = Tau | Loc 'a | Env 'a

lemma act_not_eq_iff[simp]:
  \<open>a \<noteq> Tau \<longleftrightarrow> (\<exists>x. a = Loc x) \<or> (\<exists>x. a = Env x)\<close>
  \<open>(\<forall>x. a \<noteq> Loc x) \<longleftrightarrow> a = Tau \<or> (\<exists>x. a = Env x)\<close>
  \<open>(\<forall>x. a \<noteq> Env x) \<longleftrightarrow> a = Tau \<or> (\<exists>x. a = Loc x)\<close>
  by (meson act.distinct act.exhaust)+

subsection \<open> Operational semantics steps \<close>

fun head_atoms :: \<open>'a comm \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) set\<close> where
  \<open>head_atoms (c1 ;; c2) = (let a1 = head_atoms c1
                             in if a1 = \<bottom> then head_atoms c2 else a1)\<close>
| \<open>head_atoms (c1 \<^bold>+ c2) = (head_atoms c1 \<squnion> head_atoms c2)\<close>
| \<open>head_atoms (c1 \<box> c2) = (head_atoms c1 \<squnion> head_atoms c2)\<close>
| \<open>head_atoms (c1 \<parallel> c2) = (head_atoms c1 \<squnion> head_atoms c2)\<close>
| \<open>head_atoms (Atomic b) = {b}\<close>
| \<open>head_atoms (DO c OD) = head_atoms c\<close>
| \<open>head_atoms Skip = {}\<close>
| \<open>head_atoms (\<mu> c) = head_atoms c\<close>
| \<open>head_atoms (FixVar x) = \<bottom>\<close>

inductive opstep
  :: \<open>('b::perm_alg \<times> 'b) act \<Rightarrow>
        ('a::perm_alg \<times> 'b) \<times> ('a \<times> 'b) comm \<Rightarrow>
        ('a \<times> 'b) \<times> ('a \<times> 'b) comm \<Rightarrow> bool\<close>
  where
  seq_left[intro!]: \<open>opstep a (h, c1) (h', c1') \<Longrightarrow> opstep a (h, c1 ;; c2) (h', c1' ;; c2)\<close>
| seq_right[intro!]: \<open>opstep Tau (h, Skip ;; c2) (h, c2)\<close>
| indet_left[intro]: \<open>opstep a (h, c1) s' \<Longrightarrow> opstep a (h, c1 \<^bold>+ c2) s'\<close>
| indet_right[intro]: \<open>opstep a (h, c2) s' \<Longrightarrow> opstep a (h, c1 \<^bold>+ c2) s'\<close>
| endet_tau_left[intro]: \<open>opstep Tau (h, c1) (h', c1') \<Longrightarrow> opstep Tau (h, c1 \<box> c2) (h', c1' \<box> c2)\<close>
| endet_tau_right[intro]: \<open>opstep Tau (h, c2) (h', c2') \<Longrightarrow> opstep Tau (h, c1 \<box> c2) (h', c1 \<box> c2')\<close>
| endet_skip_left[intro!]: \<open>opstep Tau (h, Skip \<box> c2) (h, c2)\<close>
| endet_skip_right[intro!]: \<open>opstep Tau (h, c1 \<box> Skip) (h, c1)\<close>
| endet_local_left[intro]: \<open>a \<noteq> Tau \<Longrightarrow> opstep a (h, c1) s' \<Longrightarrow> opstep a (h, c1 \<box> c2) s'\<close>
| endet_local_right[intro]: \<open>a \<noteq> Tau \<Longrightarrow> opstep a (h, c2) s' \<Longrightarrow> opstep a (h, c1 \<box> c2) s'\<close>
(* TODO
| par_left_tau[intro]: \<open>opstep Tau (h, Skip \<parallel> t) (h', t)\<close>
| par_right_tau[intro]: \<open>opstep a (h, s \<parallel> Skip) (h', s)\<close>
*)
| par_left[intro]: \<open>opstep a (h, s) (h', s') \<Longrightarrow> opstep a (h, s \<parallel> t) (h', s' \<parallel> t)\<close>
| par_right[intro]: \<open>opstep a (h, t) (h', t') \<Longrightarrow> opstep a (h, s \<parallel> t) (h', s \<parallel> t')\<close>
| par_skip[intro!]: \<open>opstep Tau (h, Skip \<parallel> Skip) (h, Skip)\<close>
| iter_step[intro]: \<open>opstep Tau (h, DO c OD) (h, c ;; DO c OD)\<close>
| iter_end[intro]: \<open>\<not> pre_state (\<Squnion>(head_atoms c)) h \<Longrightarrow> opstep Tau (h, DO c OD) (h, Skip)\<close>
| fixpt_skip[intro!]: \<open>c' = c[0 \<leftarrow> \<mu> c] \<Longrightarrow> opstep Tau (h, \<mu> c) (h, c')\<close>
| atomic[intro!]:
  \<open>a = Loc (snd h, snd h') \<Longrightarrow>
    c' = Skip \<Longrightarrow>
    b h h' \<Longrightarrow>
    opstep a (h, Atomic b) (h', c')\<close>

inductive_cases opstep_tauE[elim]: \<open>opstep Tau s s'\<close>
inductive_cases opstep_locE[elim]: \<open>opstep (Loc x) s s'\<close>
inductive_cases opstep_envE[elim]: \<open>opstep (Env x) s s'\<close>

inductive_cases opstep_skipE[elim!]: \<open>opstep a (h, Skip) s'\<close>
inductive_cases opstep_seqE[elim]: \<open>opstep a (h, c1 ;; c2) s'\<close>
inductive_cases opstep_indetE[elim]: \<open>opstep a (h, c1 \<^bold>+ c2) s'\<close>
inductive_cases opstep_endetE[elim]: \<open>opstep a (h, c1 \<box> c2) s'\<close>
inductive_cases opstep_parE[elim]: \<open>opstep a (h, c1 \<parallel> c2) s'\<close>
inductive_cases opstep_iterE[elim]: \<open>opstep a (h, DO c OD) s'\<close>
inductive_cases opstep_fixptE[elim]: \<open>opstep a (h, \<mu> c) s'\<close>
inductive_cases opstep_atomicE[elim!]: \<open>opstep a (h, Atomic b) s'\<close>

paragraph \<open> Pretty operational semantics \<close>

abbreviation(input) pretty_opstep :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _\<close> (\<open>_ \<midarrow>(_)\<rightarrow> _\<close> [60,0,60] 60) where
  \<open>hs \<midarrow>a\<rightarrow> ht \<equiv> opstep a hs ht\<close>


subsection \<open> Lemmas about opstep \<close>

named_theorems opstep_iff

lemma opstep_iff_standard[opstep_iff]:
  \<open>opstep a (h, Skip) s' \<longleftrightarrow> False\<close>
  \<open>opstep a (h, c1 ;; c2) s' \<longleftrightarrow>
    a = Tau \<and> c1 = Skip \<and> s' = (h, c2) \<or>
    (\<exists>h' c1'. opstep a (h,c1) (h',c1') \<and> s' = (h', c1' ;; c2))\<close>
  \<open>opstep a (h, c1 \<^bold>+ c2) s' \<longleftrightarrow>
    opstep a (h, c1) s' \<or> opstep a (h, c2) s'\<close>
  \<open>opstep a (h, c1 \<box> c2) s' \<longleftrightarrow>
    a \<noteq> Tau \<and> opstep a (h, c1) s' \<or>
    a \<noteq> Tau \<and> opstep a (h, c2) s' \<or>
    a = Tau \<and> (\<exists>h' c1'. s' = (h', c1' \<box> c2) \<and> opstep Tau (h, c1) (h', c1')) \<or>
    a = Tau \<and> (\<exists>h' c2'. s' = (h', c1 \<box> c2') \<and> opstep Tau (h, c2) (h', c2')) \<or>
    a = Tau \<and> c1 = Skip \<and> s' = (h, c2) \<or>
    a = Tau \<and> c2 = Skip \<and> s' = (h, c1)\<close>
  \<open>opstep a (h, c1 \<parallel> c2) s' \<longleftrightarrow>
    a = Tau \<and> c1 = Skip \<and> c2 = Skip \<and> s' = (h, Skip) \<or>
    (\<exists>h' c1'. opstep a (h,c1) (h',c1') \<and> s' = (h', c1' \<parallel> c2)) \<or>
    (\<exists>h' c2'. opstep a (h,c2) (h',c2') \<and> s' = (h', c1 \<parallel> c2'))\<close>
  \<open>opstep a (h, DO c OD) s' \<longleftrightarrow>
    a = Tau \<and> \<not> pre_state (\<Squnion>(head_atoms c)) h \<and> s' = (h, Skip) \<or>
    a = Tau \<and> s' = (h, c ;; DO c OD)\<close>
  \<open>opstep a (h, \<mu> c) s' \<longleftrightarrow> a = Tau \<and> s' = (h, c[0 \<leftarrow> \<mu> c])\<close>
  \<open>opstep a (h, Atomic b) s' \<longleftrightarrow>
    snd s' = Skip \<and>
    b h (fst s') \<and>
    a = Loc (snd h, snd (fst s'))\<close>
         apply blast
        apply blast
       apply blast
      apply (rule iffI, (erule opstep_endetE; force), force)
     apply blast
    apply blast
   apply blast
  apply (rule iffI)
   apply (erule opstep_atomicE; force)
  apply (metis atomic prod.collapse)
  done

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

lemma opstep_env_impossible:
  assumes \<open>s \<midarrow>Env x\<rightarrow> s'\<close>
  shows \<open>False\<close>
proof -
  { fix a
    have \<open>s \<midarrow>a\<rightarrow> s' \<Longrightarrow> a = Env x \<Longrightarrow> False\<close>
      by (induct arbitrary: x rule: opstep.inducts) force+
  }
  then show ?thesis
    using assms by force
qed

lemma opstep_act_cases:
  \<open>s \<midarrow>a\<rightarrow> s' \<Longrightarrow>
    (a = Tau \<Longrightarrow> s \<midarrow>Tau\<rightarrow> s' \<Longrightarrow> fst s' = fst s \<Longrightarrow> P) \<Longrightarrow>
    (\<And>x. a = Loc x \<Longrightarrow> s \<midarrow>Loc x\<rightarrow> s' \<Longrightarrow> P) \<Longrightarrow>
    P\<close>
  by (metis (full_types) act.exhaust opstep_tau_preserves_heap opstep_env_impossible)

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
    by (metis snd_conv)
qed

lemmas all_atom_comm_opstepD =
  all_atom_comm_opstep[rotated]

lemma opstep_locD':
  \<open>opstep a s s' \<Longrightarrow>
    s = (h, c) \<Longrightarrow>
    s' = (h', c') \<Longrightarrow>
    a = Loc (hy, hy') \<Longrightarrow>
    weak_framed_subresource_rel \<top> hy hy' (snd h) (snd h')\<close>
  by (induct arbitrary: hy hy' h c h' c' rule: opstep.inducts)
    blast+

lemma opstep_locD:
  \<open>opstep (Loc (hx, hx')) (h, c) (h', c') \<Longrightarrow>
    weak_framed_subresource_rel \<top> hx hx' (snd h) (snd h')\<close>
  by (metis opstep_locD')


subsubsection \<open> adding parallel \<close>

lemma opstep_parallel_leftD:
  \<open>s \<midarrow>a\<rightarrow> s' \<Longrightarrow> (fst s, snd s \<parallel> cy) \<midarrow>a\<rightarrow> (fst s', snd s' \<parallel> cy)\<close>
  by (simp add: par_left)

lemma opstep_parallel_rightD:
  \<open>s \<midarrow>a\<rightarrow> s' \<Longrightarrow> (fst s, cx \<parallel> snd s) \<midarrow>a\<rightarrow> (fst s', cx \<parallel> snd s')\<close>
  by (simp add: par_right)


subsubsection \<open> iteraction with all_atom_comm \<close>

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
    by (metis snd_conv)
qed

lemmas rev_opstep_preserves_all_atom_comm = opstep_preserves_all_atom_comm[rotated]


subsection \<open> Opstep rules for defined programs \<close>

lemma opstep_guard[intro!]:
  \<open>p h \<Longrightarrow>
    hsx' = hsx \<Longrightarrow>
    hsx = snd h \<Longrightarrow>
    h' = h \<Longrightarrow>
    opstep (Loc (hsx, hsx')) (h, Guard p) (h', Skip)\<close>
  by (force simp add: Guard_def opstep_iff less_eq_sepadd_def')

lemma opstep_IfThenElse_iff[opstep_iff]:
  \<open>opstep a (h, IfThenElse p ct cf) s' \<longleftrightarrow>
    a = Loc (snd h, snd h) \<and>
    (p h \<and> s' = (h, Skip ;; ct) \<or>
      \<not> p h \<and> s' = (h, Skip ;; cf))\<close>
  by (force simp add: IfThenElse_def opstep_iff weak_framed_subresource_rel_def
      framed_subresource_rel_def less_eq_sepadd_def')

lemma opstep_IfThenElse_true[intro]:
  \<open>p h \<Longrightarrow>
    xy = (snd h, snd h) \<Longrightarrow>
    c' = Skip ;; ct \<Longrightarrow>
    opstep (Loc xy) (h, IfThenElse p ct cf) (h, c')\<close>
  by (simp add: opstep_iff)

lemma opstep_IfThenElse_false[intro]:
  \<open>\<not> p h \<Longrightarrow>
    xy = (snd h, snd h) \<Longrightarrow>
    c' = Skip ;; cf \<Longrightarrow>
    opstep (Loc xy) (h, IfThenElse p ct cf) (h, c')\<close>
  by (simp add: opstep_iff)

lemma pre_state_pguard_eq[simp]:
  \<open>pre_state (pguard p) = p\<close>
  by (simp add: pguard_def pre_state_def)

lemma opstep_WhileLoop_iff[opstep_iff]:
  \<open>opstep a (h, WhileLoop p c) s' \<longleftrightarrow>
    a = Tau \<and> s' = (h,
      (Guard p ;; c \<box> Guard (- p)) ;;
        DO Guard p ;; c \<box> Guard (- p) OD)\<close>
  by (simp add: WhileLoop_def opstep_iff)


section \<open> Trace semantics \<close>

(* a rose tree *)
datatype 'a tree = Branch (branches: \<open>'a \<Rightarrow> 'a tree fset\<close>)

section \<open> Safe \<close>

inductive safe
  :: \<open>('s::perm_alg \<times> 's) act tree \<Rightarrow>
      ('l::perm_alg \<times> 's) comm \<Rightarrow>
      'l \<Rightarrow>
      's \<Rightarrow>
      ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
      ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
      ('l \<times> 's \<Rightarrow> bool) \<Rightarrow>
      ('l \<Rightarrow> bool) \<Rightarrow>
      bool\<close>
  where
  safeI[intro]:
  \<open>\<comment> \<open> if the command is Skip, the postcondition is established \<close>
    \<comment> \<open> TODO: This requires termination is represented as infinite stuttering past the end.
               We may want a different model. \<close>
    (c = Skip \<longrightarrow> q (hl, hs)) \<Longrightarrow>
    \<comment> \<open> Env steps are safe \<close>
    (\<And>a tt' hs'.
        tt' |\<in>| branches tt a \<Longrightarrow>
        a = Env (hs, hs') \<Longrightarrow>
        r hs hs'\<Longrightarrow>
        safe tt' c hl hs' r g q F) \<Longrightarrow>
    \<comment> \<open> Loc opsteps establish the guarantee \<close>
    (\<And>a tt' c' hlx hlx' hs'.
        tt' |\<in>| branches tt a \<Longrightarrow>
        a = Loc (hs, hs') \<Longrightarrow>
        ((hlx, hs), c) \<midarrow>a\<rightarrow> ((hlx', hs'), c') \<Longrightarrow>
        hl \<preceq> hlx \<Longrightarrow>
        g hs hs') \<Longrightarrow>
    \<comment> \<open> opsteps are safe \<close>
    (\<And>a tt' c' hl' hs'.
        tt' |\<in>| branches tt a \<Longrightarrow>
        a = Tau \<or> a = Loc (hs, hs') \<Longrightarrow>
        ((hl, hs), c) \<midarrow>a\<rightarrow> ((hl', hs'), c') \<Longrightarrow>
        safe tt' c' hl' hs' r g q F) \<Longrightarrow>
    \<comment> \<open> opsteps are frame closed \<close>
    (\<And>a tt' c' hlf hlhlf' hs'.
        tt' |\<in>| branches tt a \<Longrightarrow>
        a = Tau \<or> a = Loc (hs, hs') \<Longrightarrow>
        ((hl + hlf, hs), c) \<midarrow>a\<rightarrow> ((hlhlf', hs'), c') \<Longrightarrow>
        hl ## hlf \<Longrightarrow>
        F hlf \<Longrightarrow>
        (\<exists>hl'.
          hl' ## hlf \<and> hlhlf' = hl' + hlf \<and>
          (a = Tau \<longrightarrow> hl' = hl) \<and>
          safe tt' c' hl' hs' r g q F)) \<Longrightarrow>
    \<comment> \<open> conclude a step can be made \<close>
    safe tt c hl hs r g q F\<close>

subsection \<open> Proofs about safe \<close>

inductive_cases safeE[elim]: \<open>safe T c hl hs r g q F\<close>

lemma safe_iff:
  \<open>safe (Branch tf) c hl hs r g q F \<longleftrightarrow>
      (c = Skip \<longrightarrow> q (hl, hs)) \<and>
      (\<forall>a tt' hs'.
          tt' |\<in>| tf a \<longrightarrow>
          a = Env (hs, hs') \<longrightarrow>
          r hs hs' \<longrightarrow>
          safe tt' c hl hs' r g q F) \<and>
      \<comment> \<open> Loc opsteps establish the guarantee \<close>
      (\<forall>a tt' c' hlx hlx' hs'.
          tt' |\<in>| tf a \<longrightarrow>
          a = Loc (hs, hs') \<longrightarrow>
          ((hlx, hs), c) \<midarrow>a\<rightarrow> ((hlx', hs'), c') \<longrightarrow>
          hl \<preceq> hlx \<longrightarrow>
          g hs hs') \<and>
      \<comment> \<open> opsteps are safe \<close>
      (\<forall>a tt' c' hl' hs'.
          tt' |\<in>| tf a \<longrightarrow>
          a = Tau \<or> a = Loc (hs, hs') \<longrightarrow>
          ((hl, hs), c) \<midarrow>a\<rightarrow> ((hl', hs'), c') \<longrightarrow>
          safe tt' c' hl' hs' r g q F) \<and>
      \<comment> \<open> opsteps are frame closed \<close>
      (\<forall>a tt' c' hlf hlhlf' hs'.
          tt' |\<in>| tf a \<longrightarrow>
          a = Tau \<or> a = Loc (hs, hs') \<longrightarrow>
          ((hl + hlf, hs), c) \<midarrow>a\<rightarrow> ((hlhlf', hs'), c') \<longrightarrow>
          hl ## hlf \<longrightarrow>
          F hlf \<longrightarrow>
          (\<exists>hl'.
            hl' ## hlf \<and> hlhlf' = hl' + hlf \<and>
            (a = Tau \<longrightarrow> hl' = hl) \<and>
            safe tt' c' hl' hs' r g q F))\<close>
  apply (rule iffI)
   apply (erule safeE, clarsimp simp add: dom_def, metis)
  apply (rule safeI; simp; metis)
  done

lemma safe_nil_iff[simp]:
  \<open>safe (Branch (\<lambda>_. {||})) c hl hs r g q F \<longleftrightarrow> (c = Skip \<longrightarrow> q (hl, hs))\<close>
  by (simp add: safe_iff)

lemma safe_suc_iff:
  \<open>tf \<noteq> (\<lambda>_. {||}) \<Longrightarrow>
    safe (Branch tf) c hl hs r g q F \<longleftrightarrow>
      (c = Skip \<longrightarrow> q (hl, hs)) \<and>
      (\<forall>a tt' hs'.
          tt' |\<in>| tf a \<longrightarrow>
          a = Env (hs, hs') \<longrightarrow>
          r hs hs' \<longrightarrow>
          safe tt' c hl hs' r g q F) \<and>
      \<comment> \<open> Loc opsteps establish the guarantee \<close>
      (\<forall>a tt' c' hlx hlx' hs'.
          tt' |\<in>| tf a \<longrightarrow>
          a = Loc (hs, hs') \<longrightarrow>
          ((hlx, hs), c) \<midarrow>a\<rightarrow> ((hlx', hs'), c') \<longrightarrow>
          hl \<preceq> hlx \<longrightarrow>
          g hs hs') \<and>
      \<comment> \<open> opsteps are safe \<close>
      (\<forall>a tt' c' hl' hs'.
          tt' |\<in>| tf a \<longrightarrow>
          a = Tau \<or> a = Loc (hs, hs') \<longrightarrow>
          ((hl, hs), c) \<midarrow>a\<rightarrow> ((hl', hs'), c') \<longrightarrow>
          safe tt' c' hl' hs' r g q F) \<and>
      \<comment> \<open> opsteps are frame closed \<close>
      (\<forall>a tt' c' hlf hlhlf' hs'.
          tt' |\<in>| tf a \<longrightarrow>
          a = Tau \<or> a = Loc (hs, hs') \<longrightarrow>
          ((hl + hlf, hs), c) \<midarrow>a\<rightarrow> ((hlhlf', hs'), c') \<longrightarrow>
          hl ## hlf \<longrightarrow>
          F hlf \<longrightarrow>
          (\<exists>hl'.
            hl' ## hlf \<and> hlhlf' = hl' + hlf \<and>
            (a = Tau \<longrightarrow> hl' = hl) \<and>
            safe tt' c' hl' hs' r g q F))\<close>
  by (simp add: safe_iff dom_def)

lemma safeD:
  \<open>safe tt c hl hs r g q F \<Longrightarrow>
    c = Skip \<Longrightarrow>
    q (hl, hs)\<close>
  \<open>safe tt c hl hs r g q F \<Longrightarrow>
    tt' |\<in>| branches tt (Env (hs, hs')) \<Longrightarrow>
    r hs hs' \<Longrightarrow>
    safe tt' c hl hs' r g q F\<close>
  \<open>safe tt c hl hs r g q F \<Longrightarrow>
    tt' |\<in>| branches tt a \<Longrightarrow>
    a = Loc (hs, hs') \<Longrightarrow>
    ((hlx, hs), c) \<midarrow>a\<rightarrow> ((hl', hs'), c') \<Longrightarrow>
    hl \<preceq> hlx \<Longrightarrow>
    g hs hs'\<close>
  \<open>safe tt c hl hs r g q F \<Longrightarrow>
    tt' |\<in>| branches tt a \<Longrightarrow>
    a = Tau \<or> a = Loc (hs, hs') \<Longrightarrow>
    ((hl, hs), c) \<midarrow>a\<rightarrow> ((hl', hs'), c') \<Longrightarrow>
    safe tt' c' hl' hs' r g q F\<close>
  \<open>safe tt c hl hs r g q F \<Longrightarrow>
    tt' |\<in>| branches tt a \<Longrightarrow>
    a = Tau \<or> a = Loc (hs, hs') \<Longrightarrow>
    ((hl + hlf, hs), c) \<midarrow>a\<rightarrow> ((hlhlf', hs'), c') \<Longrightarrow>
    hl ## hlf \<Longrightarrow>
    F hlf \<Longrightarrow>
    (\<exists>hl'.
      hl' ## hlf \<and> hlhlf' = hl' + hlf \<and>
      (a = Tau \<longrightarrow> hl' = hl) \<and>
      safe tt' c' hl' hs' r g q F)\<close>
  by (erule safeE, force simp add: dom_def)+

lemma safe_frame_leftD:
  \<open>safe tt c hl hs r g q F \<Longrightarrow>
    tt' |\<in>| branches tt a \<Longrightarrow>
    a = Tau \<or> a = Loc (hs, hs') \<Longrightarrow>
    ((hlf + hl, hs), c) \<midarrow>a\<rightarrow> ((hlfhl', hs'), c') \<Longrightarrow>
    hlf ## hl \<Longrightarrow>
    F hlf \<Longrightarrow>
    (\<exists>hl'.
      hl' ## hlf \<and> hlfhl' = hlf + hl' \<and>
      (a = Tau \<longrightarrow> hl' = hl) \<and>
      safe tt' c' hl' hs' r g q F)\<close>
  apply (drule safeD(5)[where hlf=hlf and hlhlf'=hlfhl'], blast, blast)
     apply (simp add: disjoint_sym_iff[of _ hlf] partial_add_commute[of hlf]; fail)
    apply (simp add: disjoint_sym_iff[of _ hlf] partial_add_commute[of hlf]; fail)
   apply blast
  apply (force simp add: disjoint_sym_iff[of hlf] partial_add_commute[of _ hlf])
  done


subsubsection \<open> Monotonicity of safe \<close>

lemma safe_postpred_monoD:
  \<open>safe n c hl hs r g q F \<Longrightarrow> q \<le> q' \<Longrightarrow> safe n c hl hs r g q' F\<close>
  apply (induct rule: safe.induct)
  apply (rule safeI)
      apply (clarsimp simp add: le_fun_def; fail)+
  apply metis
  done

lemmas safe_postpred_mono = safe_postpred_monoD[rotated]

lemma safe_guarantee_monoD:
  \<open>safe as c hl hs r g q F \<Longrightarrow> g \<le> g' \<Longrightarrow> safe as c hl hs r g' q F\<close>
proof (induct rule: safe.induct)
  case (safeI T c q hl hs a r g)
  show ?case
    using safeI.hyps(1,2) safeI.prems
    apply -
    apply (rule safe.safeI)
        apply blast
       apply (simp add: safeI.hyps; fail)
      apply (frule safeI.hyps(4); blast)
     apply (frule safeI.hyps(6); blast)
    apply (frule safeI.hyps(7); blast)
    done
qed

lemmas safe_guarantee_mono = safe_guarantee_monoD[rotated]

lemma safe_rely_antimonoD:
  \<open>safe n c hl hs r g q F \<Longrightarrow> r' \<le> r \<Longrightarrow> safe n c hl hs r' g q F\<close>
  apply (induct rule: safe.induct)
  apply (rule safeI)
      apply blast
     apply (auto; fail)[1]
    apply metis
   apply metis
  apply metis
  done

lemmas safe_rely_antimono = safe_rely_antimonoD[rotated]

(* TODO: move *)
inductive subtree_eq :: \<open>'a tree \<Rightarrow> 'a tree \<Rightarrow> bool\<close> (infix \<open>\<le>\<^sub>\<TT>\<close> 50) where
  subtree_eqI:
  \<open>\<forall>x a. a |\<in>| t1 x \<longrightarrow> (\<exists>b. b |\<in>| t2 x \<and> a \<le>\<^sub>\<TT> b) \<Longrightarrow>
    Branch t1 \<le>\<^sub>\<TT> Branch t2\<close>

inductive_cases subtree_eqE[elim!]: \<open>Branch x \<le>\<^sub>\<TT> Branch y\<close>
inductive_cases subtree_eqE'[elim]: \<open>x \<le>\<^sub>\<TT> y\<close>

abbreviation(input) tree_supset_eq :: \<open>'a tree \<Rightarrow> 'a tree \<Rightarrow> bool\<close> (infix \<open>\<ge>\<^sub>\<TT>\<close> 50) where
  \<open>x \<ge>\<^sub>\<TT> y \<equiv> y \<le>\<^sub>\<TT> x\<close>

lemma subtree_eq_refl[iff]:
  \<open>x \<le>\<^sub>\<TT> x\<close>
  by (induct x) (blast intro: subtree_eqI dest: nth_mem)

lemma subtree_eq_trans[trans]:
  \<open>x \<le>\<^sub>\<TT> y \<Longrightarrow> y \<le>\<^sub>\<TT> z \<Longrightarrow> x \<le>\<^sub>\<TT> z\<close>
  by (induct arbitrary: z rule: subtree_eq.induct)
    (erule subtree_eqE', clarsimp, rule subtree_eqI, meson)
(*
lemma subtree_eq_antisym:
  \<open>x \<le>\<^sub>\<TT> y \<Longrightarrow> y \<le>\<^sub>\<TT> x \<Longrightarrow> x = y\<close>
  apply (induct rule: subtree_eq.induct)
  apply (clarsimp simp add: fun_eq_iff fset_eq_iff)
  apply (rule iffI)
   apply (drule spec2, drule mp, blast)
   apply clarsimp
   apply (drule spec2, drule mp, blast)
   apply clarsimp
  oops
  *)

interpretation tree: preorder \<open>(\<le>\<^sub>\<TT>)\<close> \<open>((\<le>\<^sub>\<TT>) \<sqinter> - (\<ge>\<^sub>\<TT>))\<close>
  apply standard
     apply (force simp add: le_fun_def)
    apply force
   apply (force intro: subtree_eq_trans)
  done

lemma subtree_eqD[dest]:
  \<open>t1 \<le>\<^sub>\<TT> t2 \<Longrightarrow> a |\<in>| branches t1 x \<Longrightarrow> \<exists>b. b |\<in>| branches t2 x \<and> a \<le>\<^sub>\<TT> b\<close>
  by fastforce

lemma safe_subtree_eq_antimono:
  assumes   
    \<open>safe tt c hl hs r g q F\<close>
    \<open>tt' \<le>\<^sub>\<TT> tt\<close>
  shows
    \<open>safe tt' c hl hs r g q F\<close>
  using assms
  apply (induct tt arbitrary: tt' c hl hs r g q F)
  apply (rule safeI)
      apply blast
     apply clarsimp
     apply (frule subtree_eqD, blast)
     apply clarsimp
     apply (frule safeD(2), force, force)
     apply (metis range_eqI)
    apply clarsimp
    apply (frule subtree_eqD, blast)
    apply clarsimp
    apply (frule safeD(3); force)
   apply clarsimp
   apply (frule subtree_eqD, blast)
   apply clarsimp
   apply (frule safeD(4), force, force, force)
   apply (metis range_eqI)
  apply clarsimp
  apply (frule subtree_eqD, blast)
  apply clarsimp
  apply (frule safeD(5), force, force, force, force, force)
  apply (metis range_eqI)
  done

(*
(* TODO: move *)
lemma ball_eq_iff:
  \<open>(\<forall>x\<in>X. x = z) \<longleftrightarrow> X = {} \<or> X = {z}\<close>
  by fastforce

(* TODO: move *)
definition trace_set_start_less_eq
  :: \<open>'a list set \<Rightarrow> 'a list set \<Rightarrow> bool\<close> (infix \<open>\<sqsubseteq>\<^sub>l\<close> 60)
  where
  \<open>A \<sqsubseteq>\<^sub>l B \<equiv> \<forall>a\<in>A. \<exists>b\<in>B. a \<le>\<^sub>l b\<close>

lemma trace_set_start_leq_mem_step:
  \<open>T' \<sqsubseteq>\<^sub>l T \<Longrightarrow> a # t \<in> T' \<Longrightarrow> \<exists>t. a # t \<in> T\<close>
  by (metis Cons_sublisteq_iff trace_set_start_less_eq_def)

lemma trace_set_start_leq_step_sets:
  \<open>T' \<sqsubseteq>\<^sub>l T \<Longrightarrow> a#t \<in> T' \<Longrightarrow> {t. a#t\<in>T'} \<sqsubseteq>\<^sub>l {t. a#t\<in>T}\<close>
  by (simp add: trace_set_start_less_eq_def, metis Cons_sublisteq_iff)

lemma safe_step_antimonoD:
  assumes
    \<open>safe T c hl hs r g q F\<close>
    \<open>T' \<sqsubseteq>\<^sub>l T\<close>
    \<open>good_trace_set n T'\<close>
  shows
    \<open>safe T' c hl hs r g q F\<close>
  using assms
  apply (induct n arbitrary: T T' c hl hs r g q F)
   apply (force simp add: good_trace_set_def ball_eq_iff)
  apply (rule safeI)
        apply blast
       apply blast
    (* subgoal *)
      apply (frule(1) good_trace_set_step)
      apply (frule(1) trace_set_start_leq_step_sets)
      apply (frule(1) trace_set_start_leq_mem_step)
      apply (subgoal_tac \<open>safe {t. a # t \<in> T} c hl hs r g q F\<close>)
       apply metis
      apply fast
    (* subgoal *)
     apply (frule(1) good_trace_set_step)
     apply (frule(1) trace_set_start_leq_step_sets)
     apply (frule(1) trace_set_start_leq_mem_step)
     apply (subgoal_tac \<open>safe {t. a # t \<in> T} c hl hs' r g q F\<close>)
      apply metis
     apply fast
    (* subgoal *)
    apply (meson safeD(5) trace_set_start_leq_mem_step; fail)
    (* subgoal *)
   apply (frule(1) good_trace_set_step)
   apply (frule(1) trace_set_start_leq_step_sets)
   apply (frule(1) trace_set_start_leq_mem_step)
   apply clarsimp
   apply (frule safeD(6), blast, blast, blast)
   apply (subgoal_tac \<open>safe {t. a # t \<in> T} c' hl' hs' r g q F\<close>)
    apply metis
   apply blast
    (* subgoal *)
  apply (frule(1) good_trace_set_step)
  apply (frule(1) trace_set_start_leq_step_sets)
  apply (frule(1) trace_set_start_leq_mem_step)
  apply clarsimp
  apply (frule safeD(7), blast, blast, blast, blast, blast)
  apply clarsimp
  apply (subgoal_tac \<open>safe {t. a # t \<in> T} c' hl' hs' r g q F\<close>)
   apply metis
  apply blast
  done
*)

lemma safe_frameset_antimonoD:
  \<open>safe n c hl hs r g q F \<Longrightarrow> F' \<le> F \<Longrightarrow> safe n c hl hs r g q F'\<close>
  apply (induct arbitrary: F' rule: safe.inducts)
  apply clarsimp
  apply (rule safeI)
      apply force
     apply force
    apply metis
   apply metis
  apply (simp add: le_fun_def)
  apply metis
  done


subsection \<open> Safety of Skip \<close>

lemma safe_skip':
  \<open>sswa r q (hl, hs) \<Longrightarrow> safe tt Skip hl hs r g (sswa r q) F\<close>
  apply (induct tt arbitrary: hl hs)
  apply (rule safeI)
      apply force
     apply (clarsimp simp add: image_def, metis sswa_step)
    apply force
   apply force
  apply force
  done

lemma safe_skip:
  \<open>p (hl, hs) \<Longrightarrow>
    sswa r p \<le> q \<Longrightarrow>
    safe T Skip hl hs r g q F\<close>
  by (rule safe_postpred_monoD[OF safe_skip'[where q=p]]; blast)


subsection \<open> Safety of frame \<close>

lemma safe_frame':
  \<open>safe tt c hl hs r g q F \<Longrightarrow>
    sswa (r \<squnion> g) f \<le> F \<times>\<^sub>P \<top> \<Longrightarrow>
    hl ## hlf \<Longrightarrow>
    sswa (r \<squnion> g) f (hlf, hs) \<Longrightarrow>
    safe tt c (hl + hlf) hs r g (q \<^emph>\<and> sswa (r \<squnion> g) f) (\<exists>\<^sub>L (sswa (r \<squnion> g) f) \<midarrow>\<^emph> F)\<close>
proof (induct arbitrary: hlf rule: safe.induct)
  case (safeI c q hl hs tt r g F)
  show ?case
    using safeI.prems safeI.hyps(1)
    apply -
    apply (rule safe.safeI)
      (* subgoal: skip *)
        apply (clarsimp simp add: sepconj_conj_def simp del: sup_apply top_apply)
        apply blast
      (* subgoal: rely step *)
       apply (rule safeI.hyps(3), blast, blast, blast, blast, blast)
       apply (rule sswa_step, rule sup2I1, blast, blast)
      (* subgoal: opstep guarantee *)
      apply (simp add: opstep_iff del: sup_apply top_apply)
      apply (metis partial_le_part_left safeI.hyps(4))
      (* subgoal: plain opstep *)
     apply (frule safeI.hyps(7), blast, blast, force, force)
     apply (erule opstep_act_cases, force)
     apply (clarsimp simp del: sup_apply top_apply)
     apply (frule safeI.hyps(4), force, force, metis partial_le_plus)
     apply (metis sswa_step sup2CI)
      (* subgoal: framed opstep *)
    apply (clarsimp simp add: partial_add_assoc2[of hl hlf] simp del: sup_apply top_apply)
    apply (frule safeI.hyps(7), blast, blast)
      apply (metis disjoint_add_swap_lr)
     apply (clarsimp simp add: le_fun_def sepimp_def simp del: sup_apply top_apply)
     apply (metis disjoint_preservation2 disjoint_sym_iff partial_add_commute partial_le_plus2
        tuple_ex_leftI)
    apply (rename_tac hlf2 hl'hlfhlf2 hs')
    apply (clarsimp simp del: sup_apply top_apply)
    apply (erule opstep_act_cases, force simp add: partial_add_assoc2)
    apply (clarsimp simp del: sup_apply top_apply)
    apply (frule safeI.hyps(7)[rotated 2])
        apply (metis disjoint_add_swap_lr)
       apply (metis disjoint_add_rightR disjoint_sym_iff partial_add_commute sepimp_def
        tuple_ex_leftI)
      apply assumption
     apply blast
    apply (clarsimp simp del: sup_apply top_apply)
    apply (frule safeI.hyps(4), force, force, metis disjoint_add_swap_lr partial_le_plus)
    apply (intro exI conjI)
      prefer 2
      apply (rule partial_add_assoc[symmetric])
        apply (metis disjoint_add_leftR disjoint_add_rightL)
       apply (metis disjoint_add_leftR)
      apply (metis disjoint_add_leftR disjoint_add_rightR)
     apply (metis disjoint_add_leftR disjoint_add_swap_rl)
    apply (meson disjoint_add_leftR disjoint_add_rightL sswa_step sup2CI; fail)
    done
qed

lemma safe_frame:
  \<open>safe n c hl hs r g q F \<Longrightarrow>
    hl ## hlf \<Longrightarrow>
    f (hlf, hs) \<Longrightarrow>
    sswa (r \<squnion> g) f \<le> F \<times>\<^sub>P \<top> \<Longrightarrow>
    sswa (r \<squnion> g) f \<le> f' \<Longrightarrow>
    F' \<le> \<exists>\<^sub>L (sswa (r \<squnion> g) f) \<midarrow>\<^emph> F \<Longrightarrow>
    safe n c (hl + hlf) hs r g (q \<^emph>\<and> f') F'\<close>
  apply (rule safe_postpred_monoD)
   apply (rule safe_frameset_antimonoD)
    apply (rule safe_frame'[where f=f]; blast)
   apply blast
  apply (blast dest: sepconj_conj_monoR)
  done


subsection \<open> Safety of Atomic \<close>

lemma frame_closed_relD:
  \<open>framecl b \<le> b \<Longrightarrow> b x y \<Longrightarrow> x ## z \<Longrightarrow> y ## z \<Longrightarrow> b (x + z) (y + z)\<close>
  by (simp add: framecl_frame_closed le_fun_def)

lemma frame_closed_relD2:
  \<open>framecl b \<le> b \<Longrightarrow>
    b x y \<Longrightarrow>
    weak_framed_subresource_rel \<top> x y xz yz \<Longrightarrow>
    b xz yz\<close>
  by (metis framecl_def predicate2D_conj weak_framed_subresource_rel_def)


lemma safe_atom':
  \<open>sp b (wssa r p) \<le> sswa r q \<Longrightarrow>
    \<forall>f. f \<le> F \<times>\<^sub>P \<top> \<longrightarrow> sp b (wssa r (p \<^emph>\<and> f)) \<le> sswa r (q \<^emph>\<and> f) \<Longrightarrow>
    b \<le> \<top> \<times>\<^sub>R g \<Longrightarrow>
    wssa r p (hl, hs) \<Longrightarrow>
    safe as (Atomic b) hl hs r g (sswa r q) F\<close>
  sorry
(*
proof (induct as arbitrary: hl hs)
  case (Cons a as)
  show ?case
    using Cons.prems
    apply (intro safe.safe_suc)
      (* subgoal: skip *)
         apply force
      (* subgoal: tau stuttering *)
        apply (metis Cons.hyps(1))
      (* subgoal: rely *)
       apply (rule Cons.hyps; force simp add: wssa_step)
      (* subgoal: opstep guarantee *)
      apply (clarsimp simp add: opstep_iff simp del: top_apply sup_apply)
      apply (metis (full_types) predicate2D rel_Times_iff)
      (* subgoal: plain opstep *)
     apply (clarsimp simp add: opstep_iff simp del: top_apply sup_apply)
     apply (rule safe_skip[where p=\<open>sswa r q\<close>])
      apply (metis sp_impliesD)
     apply force
      (* subgoal: framed opstep *)
    apply (drule_tac x=\<open>wssa r ((=) hlf \<times>\<^sub>P \<top>)\<close> in spec)
    apply (clarsimp simp add: opstep_iff sp_def[of b] imp_ex_conjL le_fun_def simp del: sup_apply)
    apply (rename_tac hl'hlf hs')
    apply (subgoal_tac \<open>(wssa r (p \<^emph>\<and> (=) hlf \<times>\<^sub>P \<top>)) (hl + hlf, hs)\<close>)
     prefer 2
     apply (rule predicate1D[OF wlp_rely_sepconj_conj_semidistrib])
     apply (rule sepconj_conjI; force)
    apply (subgoal_tac \<open>b (hl + hlf, hs) (hl'hlf, hs')\<close>)
     prefer 2
     apply (meson Cons.prems(4) frame_closed_relD2; fail)
    apply (subgoal_tac \<open>sswa r (q \<^emph>\<and> (=) hlf \<times>\<^sub>P \<top>) (hl'hlf, hs')\<close>)
     prefer 2
     apply blast
    apply (drule predicate1D[OF sp_rely_sepconj_conj_semidistrib])
    apply (clarsimp simp add: sepconj_conj_def)
    apply (fast intro: safe_skip')
    done
qed simp
*)

lemma safe_atom:
  \<open>sp b (wssa r p) \<le> sswa r q \<Longrightarrow>
    \<forall>f. f \<le> F \<times>\<^sub>P \<top> \<longrightarrow> sp b (wssa r (p \<^emph>\<and> f)) \<le> sswa r (q \<^emph>\<and> f) \<Longrightarrow>
    b \<le> \<top> \<times>\<^sub>R g \<Longrightarrow>
    wssa r p (hl, hs) \<Longrightarrow>
    sswa r q \<le> q' \<Longrightarrow>
    safe n (Atomic b) hl hs r g q' F\<close>
  by (meson safe_postpred_mono safe_atom')

(*
subsection \<open> Safety of Sequencing \<close>

lemma safe_seq_assoc_left:
  \<open>safe n c hl hs r g q F \<Longrightarrow>
    c = (c1 ;; c2 ;; c3) \<Longrightarrow>
    safe n ((c1 ;; c2) ;; c3) hl hs r g q F\<close>
  apply (induct arbitrary: c1 c2 c3 rule: safe.inducts)
   apply force
  apply (rule safe_suc)
       apply blast
      apply blast
     apply blast
    apply (simp add: opstep_iff, metis)
   apply (simp add: opstep_iff, metis)
  apply (simp add: opstep_iff, metis) (* slow *)
  done

lemma safe_seq_assoc_right:
  \<open>safe n c hl hs r g q F \<Longrightarrow>
    c = ((c1 ;; c2) ;; c3) \<Longrightarrow>
    safe n (c1 ;; c2 ;; c3) hl hs r g q F\<close>
  apply (induct arbitrary: c1 c2 c3 rule: safe.inducts)
   apply force
  apply (rule safe_suc)
       apply blast
      apply blast
     apply blast
    apply (simp add: opstep_iff, metis)
   apply (simp add: opstep_iff, metis)
  apply (simp add: opstep_iff)
  apply (elim disjE conjE exE, metis, metis, blast, metis)
  done

lemma safe_seq':
  \<open>safe as c1 hl hs r g q F \<Longrightarrow>
    (\<forall>as' hl' hs'. as' \<le>\<^sub>r as \<longrightarrow> q (hl', hs') \<longrightarrow> safe as' c2 hl' hs' r g q' F) \<Longrightarrow>
    safe as (c1 ;; c2) hl hs r g q' F\<close>
proof (induct arbitrary: c2 q' rule: safe.inducts)
  case (safe_suc c1 q hl hs a as r g F)

  have c2_safe_suc:
    \<open>\<And>as' hl' hs'. as' \<le>\<^sub>r as \<Longrightarrow> q (hl', hs') \<Longrightarrow> safe as' c2 hl' hs' r g q' F\<close>
    \<open>\<And>hl' hs'. q (hl', hs') \<Longrightarrow> safe (a # as) c2 hl' hs' r g q' F\<close>
    using safeI.prems
    by (simp add: rev_sublisteq_Cons_iff all_conj_distrib)+

  show ?case
    using safeI.hyps(1)
    apply -
    apply (rule safe.safe_suc)
      (* subgoal: skip *)
         apply force
      (* subgoal: tau stuttering *)
        apply (metis c2_safe_suc(1) safeI.hyps(2))
      (* subgoal: rely *)
       apply (rule safeI.hyps(4), assumption, assumption)
       apply (simp add: c2_safe_suc(1); fail)
      (* subgoal: opstep guarantee *)
      apply (clarsimp simp add: opstep_iff simp del: top_apply sup_apply)
      apply (frule(1) safeI.hyps(5), blast)
      apply blast
      (* subgoal: plain opstep *)
     apply (clarsimp simp add: opstep_iff simp del: sup_apply)
     apply (erule disjE[of _ \<open>Ex _\<close>])
      apply (simp add: c2_safe_suc(1); fail)
     apply (clarsimp simp del: sup_apply)
     apply (frule safeI.hyps(7), blast)
      prefer 2
      apply assumption
     apply (simp add: c2_safe_suc(1); fail)
      (* subgoal: framed opstep *)
    apply (clarsimp simp add: opstep_iff simp del: sup_apply)
    apply (erule disjE[of _ \<open>Ex _\<close>])
     apply (simp add: c2_safe_suc(1); fail)
    apply clarsimp
    apply (frule safeI.hyps(8), blast, blast, blast)
    apply (metis c2_safe_suc(1))
    done
qed force

lemma safe_seq:
  \<open>safe as c1 hl hs r g q F \<Longrightarrow>
    (\<forall>as' hl' hs'. as' \<le>\<^sub>r as \<longrightarrow> q (hl', hs') \<longrightarrow> safe as' c2 hl' hs' r g q' F) \<Longrightarrow>
    safe as (c1 ;; c2) hl hs r g q' F\<close>
  by (force intro: safe_seq' safe_step_antimonoD)


subsection \<open> Safety of Iter \<close>

lemma safe_iter:
  \<open>(\<And>as' hl' hs'. as' \<le>\<^sub>r as \<Longrightarrow> sswa r i (hl', hs') \<Longrightarrow> safe as' c hl' hs' r g (sswa r i) F) \<Longrightarrow>
    sswa r i (hl, hs) \<Longrightarrow>
    safe as (Iter c) hl hs r g (sswa r i) F\<close>
proof (induct as arbitrary: i hl hs rule: rev_sublisteq_list_strong_induct)
  case (ConsLess a as)

  have safe_c2:
    \<open>\<And>as' hl' hs'. as' \<le>\<^sub>r as \<Longrightarrow> sswa r i (hl', hs') \<Longrightarrow> safe as' c hl' hs' r g (sswa r i) F\<close>
    \<open>\<And>hl' hs'. sswa r i (hl', hs') \<Longrightarrow> safe (a # as) c hl' hs' r g (sswa r i) F\<close>
    using ConsLess.prems(1)
    by (simp add: rev_sublisteq_Cons_iff)+
  note safe_c2_sucD = safe_sucD[OF safe_c2(2)]

  show ?case
    using ConsLess.prems(2)
    apply -
    apply (rule safe.safe_suc)
      (* subgoal: skip *)
         apply blast
      (* subgoal: tau stuttering *)
        apply (simp add: ConsLess.hyps ConsLess.prems(1) rev_sublisteq_Cons_iff; fail)
      (* subgoal: rely *)
       apply (rule ConsLess.hyps)
         apply blast
        apply (fast intro: safe_c2(1))
       apply (metis sswa_step)
      (* subgoal: opstep guarantee *)
      apply (simp add: opstep_iff del: top_apply sup_apply; fail)
      (* subgoal: plain opstep *)
     apply (simp add: opstep_iff)
     apply (erule disjE[of \<open>_ \<and> _\<close>])
      apply (simp add: rely_rel_wlp_impl_sp safe_skip'; fail)
     apply clarsimp
     apply (rule safe_seq')
      apply (rule safe_c2(1), fast, fast)
     apply (meson ConsLess.hyps rev_sublisteq_trans safe_c2(1); fail)
      (* subgoal: locally framed opstep *)
    apply (clarsimp simp add: le_Suc_eq all_conj_distrib opstep_iff)
    apply (erule disjE[of \<open>_ \<and> _\<close>])
     apply (simp add: rely_rel_wlp_impl_sp safe_skip'; fail)
    apply clarsimp
    apply (rule safe_seq')
     apply (rule safe_c2(1), fast, fast)
    apply (meson ConsLess.hyps rev_sublisteq_trans safe_c2(1); fail)
    done
qed force


subsubsection \<open> Safety of internal nondeterminism \<close>

lemma safe_indet:
  \<open>safe as c1 hl hs r g q F \<Longrightarrow>
    safe as c2 hl hs r g q F \<Longrightarrow>
    safe as (c1 \<^bold>+ c2) hl hs r g q F\<close>
proof (induct as arbitrary: c1 c2 hl hs)
  case (Cons a as)

  have safeSuc:
    \<open>safe (a # as) c1 hl hs r g q F\<close>
    \<open>safe (a # as) c2 hl hs r g q F\<close>
    using Cons.prems
    by simp+
  note safe_suc1 = safe_sucD[OF safeSuc(1)]
  note safe_suc2 = safe_sucD[OF safeSuc(2)]

  show ?case
    apply -
    apply (rule safe_suc)
         apply blast
      (* subgoal: tau stuttering *)
        apply (simp add: Cons.hyps safe_suc1(2) safe_suc2(2); fail)
      (* subgoal: rely *)
       apply (metis Cons.hyps safe_suc1(3) safe_suc2(3))
      (* subgoal: opstep guarantee *)
      apply (simp add: opstep_iff del: sup_apply)
      apply (metis safe_suc1(4) safe_suc2(4))
      (* subgoal: plain opstep *)
     apply (clarsimp simp add: opstep_iff simp del: sup_apply)
     apply (metis safe_suc1(5) safe_suc2(5))
      (* subgoal: local frame opstep *)
    apply (clarsimp simp add: opstep_iff simp del: sup_apply)
    apply (elim disjE[of \<open>opstep _ _ _\<close>])
     apply (erule opstep_act_cases; metis safe_suc1(6))
    apply (erule opstep_act_cases; metis safe_suc2(6))
    done
qed blast
*)


subsubsection \<open> Safety of external nondeterminism \<close>

definition \<open>tree_term_rel \<equiv> {(t, Branch f)|t f. \<exists>x. t |\<in>| f x}\<^sup>+\<close>

function endet_tracetree' :: \<open>'a act tree \<Rightarrow> 'a act tree \<Rightarrow> 'a act tree\<close> where
  \<open>endet_tracetree' (Branch ta) (Branch tb) = Branch (\<lambda>a.
    case a of
      Env x \<Rightarrow>
        ((\<lambda>x. endet_tracetree' x (Branch tb)) |`| ta (Env x)) |\<union>|
        (endet_tracetree' (Branch ta) |`| tb (Env x))
    | Loc x \<Rightarrow> ta (Loc x) |\<union>| tb (Loc x)
    | Tau \<Rightarrow>
        ((\<lambda>x. endet_tracetree' x (Branch tb)) |`| ta Tau) |\<union>|
        (endet_tracetree' (Branch ta) |`| tb Tau)
  )\<close>
  by pat_completeness auto
termination
  apply (relation \<open>tree_term_rel \<times> UNIV \<union> UNIV \<times> tree_term_rel\<close>)
  subgoal
    sorry
     apply (clarsimp simp add: tree_term_rel_def)
  oops
  

inductive_cases endet_traces'_loc3E[elim]:
  \<open>endet_traces' ta tb (Loc xy # t')\<close>
inductive_cases endet_traces'_env3E[elim]:
  \<open>endet_traces' ta tb (Env xy # t')\<close>
inductive_cases endet_traces'_tau3E[elim]:
  \<open>endet_traces' ta tb (Tau # t')\<close>

definition
  \<open>endet_traces A B \<equiv> {t|t ta tb. ta \<in> A \<and> tb \<in> B \<and> endet_traces' ta tb t}\<close>

lemma endet_traces'_full_dom:
  \<open>Ex (endet_traces' ta tb)\<close>
  apply (induct ta arbitrary: tb)
   apply (induct_tac tb)
    apply blast
   apply (case_tac a; blast)
  apply (case_tac a; blast)
  done

lemma safe_endet:
  \<open>safe Ta c1 hl hs r g q F \<Longrightarrow>
    safe Tb c2 hl hs r g q F \<Longrightarrow>
    safe (endet_tracetree Ta Tb) (c1 \<box> c2) hl hs r g q F\<close>
proof (induct arbitrary: Tb c2 rule: safe.inducts)
  case (safeI n T c q hl hs r g F)
  note safe_b = safeD[OF safeI.prems]
  show ?case
    using safeI.hyps(1) safe_b(1) safeI.prems
    apply -
    apply clarsimp
    apply (rule safe.safeI)
          apply (rule good_trace_set_endet_traces, blast, blast)
         apply blast
        apply (clarsimp simp add: endet_traces_def)
        apply (erule endet_traces'_tau3E)
         apply clarsimp
         apply (frule safeI.hyps(4), blast, blast)
         apply (simp add: endet_traces_Tau3_eq)
    sorry
qed
(*
  case (ConsLess a as)

  have safeSuc:
    \<open>safe (a # as) c1 hl hs r g q F\<close>
    \<open>safe (a # as) c2 hl hs r g q F\<close>
    using ConsLess.prems
    by simp+
  note safe_suc1 = safe_sucD[OF safeSuc(1)]
  note safe_suc2 = safe_sucD[OF safeSuc(2)]

  show ?case
    apply -
    apply (rule safe_suc)
         apply blast
      (* subgoal: tau stuttering *)
        apply (simp add: ConsLess.hyps safe_suc1(2) safe_suc2(2); fail)
      (* subgoal: rely *)
       apply (simp add: ConsLess.hyps safe_suc1(3) safe_suc2(3); fail)
      (* subgoal: opstep guarantee *)
      apply (simp add: opstep_iff del: sup_apply)
      apply (metis safe_suc1(4) safe_suc2(4))
      (* subgoal: plain opstep *)
     apply (clarsimp simp add: opstep_iff simp del: sup_apply)
     apply (elim disjE[of \<open>_ \<and> _\<close>] conjE exE)
          apply (frule safe_suc1(5), blast, blast)
         apply (frule safe_suc2(5), blast, blast)
        apply (frule opstep_tau_preserves_heap)
        apply clarsimp
        apply (rule ConsLess.hyps)
          apply blast
         apply (simp add: safe_suc1(5); fail)
        apply (simp add: safe_suc2(2); fail)
       apply (frule opstep_tau_preserves_heap)
       apply clarsimp
       apply (rule ConsLess.hyps)
         apply blast
        apply (simp add: safe_suc1(2); fail)
       apply (simp add: safe_suc2(5); fail)
      apply (fastforce dest: safe_suc2(2))
     apply (fastforce dest: safe_suc1(2))
      (* subgoal: local frame opstep *)
    apply (clarsimp simp add: opstep_iff simp del: sup_apply)
    apply (elim disjE[of \<open>_ \<and> _\<close>] conjE exE)
         apply (erule opstep_act_cases; metis safe_suc1(6))
        apply (erule opstep_act_cases; metis safe_suc2(6))
      (* subsubgoal: left tau passthrough *)
       apply (frule safe_suc1(6), blast, blast, blast)
       apply (clarsimp simp del: sup_apply)
       apply (frule opstep_tau_preserves_heap)
       apply (clarsimp simp del: sup_apply)
       apply (rule ConsLess.hyps)
         apply blast
        apply blast
       apply (metis safe_suc2(2))
      (* subsubgoal: right tau passthrough *)
      apply (frule safe_suc2(6), blast, blast, blast)
      apply clarsimp
      apply (frule opstep_tau_preserves_heap)
      apply (clarsimp simp del: sup_apply)
      apply (rule ConsLess.hyps)
        apply blast
       apply (metis safe_suc1(2))
      apply blast
      (* subsubgoal: right skip tau *)
     apply (erule disjE)
      apply (clarsimp simp del: sup_apply)
      apply (metis safe_suc2(2))
     apply blast
      (* subsubgoal: left skip tau *)
    apply (erule disjE)
     apply (clarsimp simp del: sup_apply)
     apply (metis safe_suc1(2))
    apply blast
    done
qed simp
*)


subsection \<open> Safety of parallel \<close>

inductive merge_tr :: \<open>'a act list \<Rightarrow> 'a act list \<Rightarrow> 'a act list \<Rightarrow> bool\<close> where
  merge_tr_empty[intro!]: \<open>merge_tr [] [] []\<close>
| merge_tr_stepL[intro!]: \<open>merge_tr as as1 as2 \<Longrightarrow> merge_tr (Loc x # as) (Loc x # as1) (Env x # as2)\<close>
| merge_tr_stepR[intro!]: \<open>merge_tr as as1 as2 \<Longrightarrow> merge_tr (Loc x # as) (Env x # as1) (Loc x # as2)\<close>
| merge_tr_env[intro!]: \<open>merge_tr as as1 as2 \<Longrightarrow> merge_tr (Env x # as) (Env x # as1) (Env x # as2)\<close>
| merge_tr_tauL[intro]: \<open>merge_tr as as1 as2 \<Longrightarrow> merge_tr (Tau # as) (Tau # as1) as2\<close>
| merge_tr_tauR[intro]: \<open>merge_tr as as1 as2 \<Longrightarrow> merge_tr (Tau # as) as1 (Tau # as2)\<close>

inductive_cases merge_tr_Nil1E[elim!]: \<open>merge_tr [] as1 as2\<close>
inductive_cases merge_tr_Nil2E[elim!]: \<open>merge_tr as [] as2\<close>
inductive_cases merge_tr_Nil3E[elim!]: \<open>merge_tr as as1 []\<close>

inductive_cases merge_tr_Cons1E[elim]: \<open>merge_tr (a # as) as1' as2'\<close>
inductive_cases merge_tr_Cons2E[elim]: \<open>merge_tr as' (a # as1) as2'\<close>
inductive_cases merge_tr_Cons3E[elim]: \<open>merge_tr as' as1' (a # as2)\<close>

lemma merge_tr_Cons1_simps:
  \<open>merge_tr (Loc x # asx) as1 as2 \<longleftrightarrow>
    (\<exists>as1x as2x.
      merge_tr asx as1x as2x \<and>
      (as1 = Loc x # as1x \<and> as2 = Env x # as2x \<or>
        as1 = Env x # as1x \<and> as2 = Loc x # as2x))\<close>
  \<open>merge_tr (Env x # asx) as1 as2 \<longleftrightarrow>
    (\<exists>as1x as2x. as1 = Env x # as1x \<and> as2 = Env x # as2x \<and> merge_tr asx as1x as2x)\<close>
  \<open>merge_tr (Tau # asx) as1 as2 \<longleftrightarrow>
    (\<exists>as1x. as1 = Tau # as1x \<and> merge_tr asx as1x as2) \<or>
    (\<exists>as2x. as2 = Tau # as2x \<and> merge_tr asx as1 as2x)\<close>
  by auto

lemma merge_tr_Cons1_iff:
  \<open>merge_tr (a # asx) as1 as2 \<longleftrightarrow>
    (\<forall>x. a = Loc x \<longrightarrow>
      (\<exists>as1x as2x.
        merge_tr asx as1x as2x \<and>
        (as1 = Loc x # as1x \<and> as2 = Env x # as2x \<or>
          as1 = Env x # as1x \<and> as2 = Loc x # as2x))) \<and>
    (\<forall>x. a = Env x \<longrightarrow>
      (\<exists>as1x as2x. as1 = Env x # as1x \<and> as2 = Env x # as2x \<and> merge_tr asx as1x as2x)) \<and>
    (a = Tau \<longrightarrow>
      (\<exists>as1x. as1 = Tau # as1x \<and> merge_tr asx as1x as2) \<or>
      (\<exists>as2x. as2 = Tau # as2x \<and> merge_tr asx as1 as2x))\<close>
  by (cases a; clarsimp simp add: merge_tr_Cons1_simps)

(* TODO: weaken the frame sets *)
lemma safe_parallel':
  \<open>safe as1 c1 hl1 hs (r \<squnion> g2) g1 (sswa (r \<squnion> g2) q1) \<top> \<Longrightarrow>
    safe as2 c2 hl2 hs (r \<squnion> g1) g2 (sswa (r \<squnion> g1) q2) \<top> \<Longrightarrow>
    hl1 ## hl2 \<Longrightarrow>
    merge_tr as as1 as2 \<Longrightarrow>
    safe as (c1 \<parallel> c2) (hl1 + hl2) hs r (g1 \<squnion> g2)
      (sswa (r \<squnion> g2) q1 \<^emph>\<and> (sswa (r \<squnion> g1) q2)) \<top>\<close>
proof (induct as arbitrary: as1 as2 c1 c2 hl1 hl2 hs)
  case (Cons a as)

(*
  note safe_suc1 = safe_sucD[OF Cons.prems(1)]
  note safe_suc2 = safe_sucD[OF Cons.prems(2)]
*)

  show ?case
    using Cons.prems
    apply -
    apply (rule safe_suc)
      (* subgoal: skip *)
         apply blast
      (* subgoal: tau stuttering *)
    subgoal
      apply (clarsimp simp add: merge_tr_Cons1_simps simp del: sup_apply top_apply)
      apply (elim disjE exE conjE)
       apply (rule Cons.hyps[rotated 2], blast, blast)
        apply (metis safe_sucD(2))
       apply blast
      apply (rule Cons.hyps[rotated 2], blast, blast)
       apply blast
      apply (metis safe_sucD(2))
      done
      (* subgoal: rely safety *)
    subgoal
      apply (clarsimp simp add: merge_tr_Cons1_simps simp del: sup_apply top_apply)
      apply (rule Cons.hyps[rotated 2], blast, blast, blast, blast)
      done
        (* subgoal: local step guarantee *)
    subgoal
      apply (clarsimp simp add: opstep_iff merge_tr_Cons1_simps simp del: sup_apply top_apply)
      apply (elim disjE conjE exE)
         apply (clarsimp simp del: sup_apply top_apply)
         apply (metis partial_le_part_left safe_sucD(4))
        apply (clarsimp simp del: sup_apply top_apply)
      subgoal sorry
      subgoal sorry
      apply (clarsimp simp del: sup_apply top_apply)
      apply (metis partial_le_part_right safe_sucD(4))
      done
      (* subgoal: plain opstep safe *)
    subgoal
      apply (simp add: opstep_iff del: sup_apply top_apply)
      apply (elim disjE[of \<open>_ \<and> _\<close>] disjE[of \<open>Ex _\<close>] conjE exE)
        (* subgoal: tau *)
        apply (clarsimp simp add: merge_tr_Cons1_simps simp del: sup_apply top_apply)
        apply (rule safe_skip[of \<open>sswa (r \<squnion> g2) q1 \<^emph>\<and> sswa (r \<squnion> g1) q2\<close>])
         apply (rule sepconj_conjI[rotated 2], blast, blast)
          apply (erule disjE)
           apply (clarsimp simp del: sup_apply top_apply)
           apply blast
          apply (clarsimp simp del: sup_apply top_apply)
      subgoal sorry
         apply (erule disjE)
          apply (clarsimp simp del: sup_apply top_apply)
      subgoal sorry
         apply (clarsimp simp del: sup_apply top_apply)
         apply blast
       apply (rule sp_rely_sepconj_conj_semidistrib_mono)
        apply (clarsimp simp add: sp_comp_rel simp del: sup_apply top_apply; fail)
       apply (clarsimp simp add: sp_comp_rel simp del: sup_apply top_apply; fail)
        (* subgoal: left *)
       apply (clarsimp simp del: sup_apply top_apply)
       apply (erule opstep_act_cases)
        apply (clarsimp simp add: merge_tr_Cons1_simps simp del: sup_apply top_apply)
        apply (erule disjE)
         apply (clarsimp simp del: sup_apply top_apply)
         apply (drule safe_sucD(6), blast, blast, blast, blast)
         apply (clarsimp simp del: sup_apply top_apply)
         apply (rule Cons.hyps, blast, blast, blast, blast)
        apply (clarsimp simp del: sup_apply top_apply)
      subgoal sorry
       apply (clarsimp simp add: merge_tr_Cons1_simps simp del: sup_apply top_apply)
       apply (elim disjE conjE exE)
        apply (clarsimp simp del: sup_apply top_apply)
        apply (frule safe_sucD(4)[OF _ _ partial_le_plus], blast, blast, blast)
        apply (frule safe_sucD(6), blast, blast, blast, blast)
        apply (clarsimp simp del: sup_apply top_apply)
        apply (rule Cons.hyps[rotated 2], blast, blast, blast, blast)
       apply (clarsimp simp del: sup_apply top_apply)
      subgoal sorry
        (* subgoal: right *)
       apply (clarsimp simp del: sup_apply top_apply)
       apply (erule opstep_act_cases)
        apply (clarsimp simp add: merge_tr_Cons1_simps simp del: sup_apply top_apply)
        apply (erule disjE)
        apply (clarsimp simp del: sup_apply top_apply)
      subgoal sorry
       apply (clarsimp simp del: sup_apply top_apply)
       apply (drule safe_suc_frame_leftD, blast, blast, blast, blast)
       apply (clarsimp simp del: sup_apply top_apply)
       apply (rule Cons.hyps, blast, blast, blast, blast)
      apply (clarsimp simp add: merge_tr_Cons1_simps simp del: sup_apply top_apply)
      apply (erule disjE)
       apply (clarsimp simp del: sup_apply top_apply)
      subgoal sorry
      apply (clarsimp simp del: sup_apply top_apply)
      apply (frule safe_sucD(4)[of \<open>Loc _\<close>, OF _ _ partial_le_plus2], blast, blast, blast)
      apply (frule safe_suc_frame_leftD[of \<open>Loc _\<close>], blast, blast, blast, blast)
      apply (clarsimp simp del: sup_apply top_apply)
      apply (rule Cons.hyps[rotated 2], metis disjoint_sym, blast, blast, blast)
      done
      (* subgoal: framed opstep safe *)
    subgoal
      sorry
(*
      apply (simp add: opstep_iff del: sup_apply top_apply)
      apply (elim disjE conjE exE)
        (* subgoal: tau *)
        apply (clarsimp simp del: sup_apply top_apply)
        apply (insert safe_suc1(1) safe_suc2(1))
        apply (clarsimp simp del: sup_apply top_apply)
        apply (rule safe_skip[of \<open>sswa (r \<squnion> g2) q1 \<^emph>\<and> sswa (r \<squnion> g1) q2\<close>])
         apply (clarsimp simp add: sepconj_conj_def[of \<open>sp _ _\<close>] simp del: sup_apply top_apply)
         apply blast
        apply (rule sp_rely_sepconj_conj_semidistrib_mono)
         apply (simp add: sp_comp_rel; fail)
        apply (simp add: sp_comp_rel; fail)
        (* subgoal: left *)
       apply (simp add: partial_add_assoc2[of hl1] disjoint_sym_iff del: sup_apply top_apply)
       apply (frule safe_suc1(5))
         apply (metis disjoint_add_swap_lr disjoint_sym_iff)
        apply force
       apply (clarsimp simp del: sup_apply top_apply)
       apply (rule_tac x=\<open>_ + _\<close> in exI)
       apply (intro conjI)
          apply (rule disjoint_add_swap_rl[rotated], fast)
          apply (metis disjoint_add_leftR disjoint_sym_iff)
         apply (metis disjoint_add_leftR disjoint_sym partial_add_assoc3)
        apply blast
       apply (erule opstep_act_cases)
        apply (metis Suc.hyps fst_conv le_disj_eq_absorb snd_conv)
       apply clarsimp
       apply (rule Suc.hyps)
         apply blast
        apply (metis act.distinct(1) disjoint_add_swap_lr disjoint_sym partial_le_plus snd_conv
          sup2I1 sup_commute safe_suc1(3) safe_suc2(2))
       apply (metis disjoint_add_rightR partial_add_commute)
        (* subgoal right *)
      apply (simp add: partial_add_commute[of hl1] partial_add_assoc2[of hl2] disjoint_sym_iff
          del: sup_apply top_apply)
      apply (frule safe_suc2(5))
        apply (metis disjoint_add_swap_lr disjoint_sym_iff)
       apply force
      apply (clarsimp simp del: sup_apply top_apply)
      apply (rule_tac x=\<open>_ + _\<close> in exI)
      apply (intro conjI)
         apply (rule disjoint_add_swap_rl[rotated], fast)
         apply (metis disjoint_add_leftR disjoint_sym_iff)
        apply (metis disjoint_add_leftR disjoint_sym partial_add_assoc3)
       apply blast
      apply (simp add: partial_add_commute[of _ hl1] disjoint_sym_iff del: sup_apply top_apply)
      apply (subst partial_add_commute, metis disjoint_add_leftL disjoint_sym)
      apply (erule opstep_act_cases)
       apply (metis Suc.hyps fst_conv le_disj_eq_absorb snd_conv)
      apply clarsimp
      apply (rule Suc.hyps)
        apply (metis act.distinct(1) disjoint_add_right_commute2 partial_le_plus safe_suc1(2)
          safe_suc2(3) snd_conv sup2I1 sup_commute)
       apply blast
      apply (meson disjoint_add_rightL disjoint_sym)
      done
*)
    done
qed simp

lemma safe_parallel:
  \<open>safe n c1 hl1 hs (r \<squnion> g2) g1 (sswa (r \<squnion> g2) q1) \<top> \<Longrightarrow>
    safe n c2 hl2 hs (r \<squnion> g1) g2 (sswa (r \<squnion> g1) q2) \<top> \<Longrightarrow>
    hl1 ## hl2 \<Longrightarrow>
    sswa (r \<squnion> g2) q1 \<^emph>\<and> sswa (r \<squnion> g1) q2 \<le> q \<Longrightarrow>
    g1 \<squnion> g2 \<le> g \<Longrightarrow>
    safe n (c1 \<parallel> c2) (hl1 + hl2) hs r g q \<top>\<close>
  sorry
(*
  by (meson safe_guarantee_monoD safe_parallel' safe_postpred_mono)
*)

subsection \<open> Safety of conj \<close>

lemma safe_conj':
  \<open>safe as c hl hs r g q1 F1 \<Longrightarrow>
    safe as c hl hs r g q2 F2 \<Longrightarrow>
    \<forall>a b c. F1 c \<longrightarrow> F2 c \<longrightarrow> a ## c \<longrightarrow> b ## c \<longrightarrow> a + c = b + c \<longrightarrow> a = b \<Longrightarrow>
    safe as c hl hs r g (q1 \<sqinter> q2) (F1 \<sqinter> F2)\<close>
proof (induct as arbitrary: c hl hs r g q1 q2)
  case (Cons a as)

  show ?case
    using Cons.prems
    apply -
    apply (intro safe_suc conjI impI allI)
      (* subgoal: skip *)
         apply blast
      (* subgoal: tau stuttering *)
        apply (rule Cons.hyps; blast)
      (* subgoal: guarantee step *)
       apply (rule Cons.hyps; blast)
      (* subgoal: guarantee step *)
      apply (meson safe_sucD; fail)
      (* subgoal: plain opstep *)
     apply (rule Cons.hyps)
       apply fastforce
      apply force
     apply force
      (* subgoal: frame opstep *)
    apply (clarsimp simp del: inf_apply)
    apply (frule safe_sucD(6)[where q=q1], blast, blast, blast, blast)
    apply (frule safe_sucD(6)[where q=q2], blast, blast, blast, blast)
    apply (clarsimp simp del: inf_apply)
    apply (subgoal_tac \<open>hl'a = hl'\<close>)
     prefer 2
     apply presburger
    apply (erule opstep_act_cases)
     apply (clarsimp simp del: inf_apply)
     apply (meson Cons.hyps; fail)
    apply (clarsimp simp del: inf_apply)
    apply (drule(1) Cons.hyps, metis)
    apply blast
    done
qed force

lemma safe_conj:
  \<open>safe n c hl hs r g q1 F1 \<Longrightarrow>
    safe n c hl hs r g q2 F2 \<Longrightarrow>
    F \<le> F1 \<Longrightarrow>
    F \<le> F2 \<Longrightarrow>
    \<forall>a b c. F1 c \<longrightarrow> F2 c \<longrightarrow> a ## c \<longrightarrow> b ## c \<longrightarrow> a + c = b + c \<longrightarrow> a = b \<Longrightarrow>
    safe n c hl hs r g (q1 \<sqinter> q2) F\<close>
  apply (rule safe_frameset_antimonoD)
   apply (rule safe_conj', assumption, assumption, assumption)
  apply blast
  done


section \<open> Soundness \<close>

lemma soundness:
  assumes \<open>rgsat c r g p q\<close>
    and \<open>p (hl, hs)\<close>
  shows \<open>safe as c hl hs r g q \<top>\<close>
  using assms
proof (induct c r g p q arbitrary: as hl hs rule: rgsat.inducts)
  case (rgsat_skip p r q g as h)
  then show ?case
    by (simp add: safe_skip)
next
  case (rgsat_seq c1 r g p1 p2 c2 p3)
  then show ?case
    using safe_seq[of as c1 hl hs r g p2 \<top> c2 p3]
    by blast
next
  case (rgsat_indet c1 r g1 p q1 c2 g2 q2 g q)
  then show ?case
    using safe_indet[of as c1 hl hs r g q \<top> c2]
    by (meson safe_guarantee_mono safe_postpred_mono)
next
  case (rgsat_endet c1 r g1 p q1 c2 g2 q2 g q)
  then show ?case
    using safe_endet[of as c1 hl hs r g q \<top> c2]
    by (meson safe_guarantee_mono safe_postpred_mono)
next
  case (rgsat_par s1 r g2 g1 p1 q1 s2 p2 q2 g p q)
  then show ?case
    apply -
    apply (clarsimp simp add: sepconj_conj_def[of p1 p2] le_fun_def[of p]
        simp del: sup_apply top_apply)
    apply (drule spec2, drule mp, blast)
    apply (clarsimp simp del: sup_apply top_apply)
    apply (rule safe_parallel[where ?q1.0=q1 and ?q2.0=q2])
        apply (rule safe_postpred_mono[rotated], assumption, blast)
       apply (rule safe_postpred_mono[rotated], assumption, blast)
      apply blast
     apply blast
    apply (meson le_sup_iff; fail)
    done
next
  case (rgsat_iter c r g i p q)
  then show ?case
    using safe_postpred_mono[OF _ safe_iter[of as r i c g]]
    by (simp add: sp_mono2 sswa_trivial)
next
  case (rgsat_atom p r p' q' q b g n)
  then show ?case
    by (intro safe_atom; blast)
next
  case (rgsat_frame c r g p q f f' n)
  then show ?case
    apply (clarsimp simp add: sepconj_conj_def[of p] simp del: sup_apply top_apply)
    apply (rule safe_frame[where f=f], blast, blast, blast, force, blast, simp)
    done
next
  case (rgsat_disj c r' g' p' q' p q r g)
  then show ?case
    by (metis safe_postpred_mono sup.cobounded2 sup1E sup_ge1)
next
  case (rgsat_conj c r g p1 q1 p2 q2 n hl)
  then show ?case
    by (intro safe_conj, blast, blast; force)
next
  case (rgsat_weaken c r' g' p' q' p q r g)
  moreover have \<open>p' (hl, hs)\<close>
    using rgsat_weaken.hyps(3) rgsat_weaken.prems
    by (metis rev_predicate1D)
  ultimately show ?case
    by (meson safe_guarantee_mono safe_postpred_monoD safe_rely_antimonoD)
qed

end
