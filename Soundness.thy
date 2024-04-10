theory Soundness
  imports RGLogic
begin

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

definition trace_rely :: \<open>('a\<times>'b) act list \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)\<close> where
  \<open>trace_rely as \<equiv>
    foldr (\<lambda>a. (\<squnion>) (case a of Env (x,y) \<Rightarrow> rel_step x y | _ \<Rightarrow> \<bottom>)) as \<bottom>\<close>

lemma trace_rely_simps[simp]:
  \<open>trace_rely [] = \<bottom>\<close>
  \<open>trace_rely (Env (x,y) # as) = (rel_step x y \<squnion> trace_rely as)\<close>
  \<open>trace_rely (Loc xy # as) = (trace_rely as)\<close>
  \<open>trace_rely (Tau # as) = (trace_rely as)\<close>
  by (simp add: trace_rely_def fun_eq_iff split: act.splits)+

definition trace_guar :: \<open>('a\<times>'b) act list \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)\<close> where
  \<open>trace_guar as \<equiv>
    foldr (\<lambda>a. (\<squnion>) (case a of Loc (x,y) \<Rightarrow> rel_step x y | _ \<Rightarrow> \<bottom>)) as \<bottom>\<close>

lemma trace_guar_simps[simp]:
  \<open>trace_guar [] = \<bottom>\<close>
  \<open>trace_guar (Loc (x,y) # as) = (rel_step x y \<squnion> trace_guar as)\<close>
  \<open>trace_guar (Env xy # as) = (trace_guar as)\<close>
  \<open>trace_guar (Tau # as) = (trace_guar as)\<close>
  by (simp add: trace_guar_def fun_eq_iff split: act.splits)+

lemma trace_rely_rev_sublisteq_mono:
  \<open>as \<le>\<^sub>r as' \<Longrightarrow> trace_rely as \<le> trace_rely as'\<close>
  by (induct rule: rev_sublisteq.inducts)
    (force simp add: trace_rely_def)+

lemma trace_rely_sublisteq_mono:
  \<open>as \<le>\<^sub>l as' \<Longrightarrow> trace_rely as \<le> trace_rely as'\<close>
  by (induct rule: sublisteq.inducts)
    (force simp add: trace_rely_def)+


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

inductive lopstep
  :: \<open>('b \<times> 'b) act \<Rightarrow>
        ('a \<times> 'b) \<times> ('a \<times> 'b) comm \<Rightarrow>
        ('a \<times> 'b) \<times> ('a \<times> 'b) comm \<Rightarrow> bool\<close>
  where
  seq_left[intro!]: \<open>lopstep a (h, c1) (h', c1') \<Longrightarrow> lopstep a (h, c1 ;; c2) (h', c1' ;; c2)\<close>
| seq_right[intro!]: \<open>lopstep Tau (h, Skip ;; c2) (h, c2)\<close>
| indet_left[intro]: \<open>lopstep a (h, c1) s' \<Longrightarrow> lopstep a (h, c1 \<^bold>+ c2) s'\<close>
| indet_right[intro]: \<open>lopstep a (h, c2) s' \<Longrightarrow> lopstep a (h, c1 \<^bold>+ c2) s'\<close>
| endet_tau_left[intro]: \<open>lopstep Tau (h, c1) (h', c1') \<Longrightarrow> lopstep Tau (h, c1 \<box> c2) (h', c1' \<box> c2)\<close>
| endet_tau_right[intro]: \<open>lopstep Tau (h, c2) (h', c2') \<Longrightarrow> lopstep Tau (h, c1 \<box> c2) (h', c1 \<box> c2')\<close>
| endet_skip_left[intro!]: \<open>lopstep Tau (h, Skip \<box> c2) (h, c2)\<close>
| endet_skip_right[intro!]: \<open>lopstep Tau (h, c1 \<box> Skip) (h, c1)\<close>
| endet_local_left[intro]: \<open>a \<noteq> Tau \<Longrightarrow> lopstep a (h, c1) s' \<Longrightarrow> lopstep a (h, c1 \<box> c2) s'\<close>
| endet_local_right[intro]: \<open>a \<noteq> Tau \<Longrightarrow> lopstep a (h, c2) s' \<Longrightarrow> lopstep a (h, c1 \<box> c2) s'\<close>
(* TODO
| par_left_tau[intro]: \<open>lopstep Tau (h, Skip \<parallel> t) (h', t)\<close>
| par_right_tau[intro]: \<open>lopstep a (h, s \<parallel> Skip) (h', s)\<close>
*)
| par_left[intro]: \<open>lopstep a (h, s) (h', s') \<Longrightarrow> lopstep a (h, s \<parallel> t) (h', s' \<parallel> t)\<close>
| par_right[intro]: \<open>lopstep a (h, t) (h', t') \<Longrightarrow> lopstep a (h, s \<parallel> t) (h', s \<parallel> t')\<close>
| par_skip[intro!]: \<open>lopstep Tau (h, Skip \<parallel> Skip) (h, Skip)\<close>
| iter_step[intro]: \<open>lopstep Tau (h, DO c OD) (h, c ;; DO c OD)\<close>
| iter_end[intro]: \<open>\<not> pre_state (\<Squnion>(head_atoms c)) h \<Longrightarrow> lopstep Tau (h, DO c OD) (h, Skip)\<close>
| fixpt_skip[intro!]: \<open>c' = c[0 \<leftarrow> \<mu> c] \<Longrightarrow> lopstep Tau (h, \<mu> c) (h, c')\<close>
| atomic[intro!]:
  \<open>a = Loc (snd h, snd h') \<Longrightarrow>
    c' = Skip \<Longrightarrow>
    b h h' \<Longrightarrow>
    lopstep a (h, Atomic b) (h', c')\<close>

inductive_cases lopstep_tauE[elim]: \<open>lopstep Tau s s'\<close>
inductive_cases lopstep_locE[elim]: \<open>lopstep (Loc x) s s'\<close>
inductive_cases lopstep_envE[elim]: \<open>lopstep (Env x) s s'\<close>

inductive_cases lopstep_skipE[elim!]: \<open>lopstep a (h, Skip) s'\<close>
inductive_cases lopstep_seqE[elim]: \<open>lopstep a (h, c1 ;; c2) s'\<close>
inductive_cases lopstep_indetE[elim]: \<open>lopstep a (h, c1 \<^bold>+ c2) s'\<close>
inductive_cases lopstep_endetE[elim]: \<open>lopstep a (h, c1 \<box> c2) s'\<close>
inductive_cases lopstep_parE[elim]: \<open>lopstep a (h, c1 \<parallel> c2) s'\<close>
inductive_cases lopstep_iterE[elim]: \<open>lopstep a (h, DO c OD) s'\<close>
inductive_cases lopstep_fixptE[elim]: \<open>lopstep a (h, \<mu> c) s'\<close>
inductive_cases lopstep_atomicE[elim!]: \<open>lopstep a (h, Atomic b) s'\<close>

paragraph \<open> Pretty operational semantics \<close>

definition \<open>opstep a s s' \<equiv>
  lopstep a s s' \<or>
    fst (fst s) = fst (fst s') \<and>
    a = Env (snd (fst s), snd (fst s')) \<and>
    snd s = snd s'\<close>

abbreviation(input) pretty_opstep :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _\<close> (\<open>_ \<midarrow>(_)\<rightarrow> _\<close> [60,0,60] 60) where
  \<open>hs \<midarrow>a\<rightarrow> ht \<equiv> opstep a hs ht\<close>


subsection \<open> Lemmas about lopstep \<close>

named_theorems lopstep_iff

lemma lopstep_iff_standard[lopstep_iff]:
  \<open>lopstep a (h, Skip) s' \<longleftrightarrow> False\<close>
  \<open>lopstep a (h, c1 ;; c2) s' \<longleftrightarrow>
    a = Tau \<and> c1 = Skip \<and> s' = (h, c2) \<or>
    (\<exists>h' c1'. lopstep a (h,c1) (h',c1') \<and> s' = (h', c1' ;; c2))\<close>
  \<open>lopstep a (h, c1 \<^bold>+ c2) s' \<longleftrightarrow>
    lopstep a (h, c1) s' \<or> lopstep a (h, c2) s'\<close>
  \<open>lopstep a (h, c1 \<box> c2) s' \<longleftrightarrow>
    a \<noteq> Tau \<and> lopstep a (h, c1) s' \<or>
    a \<noteq> Tau \<and> lopstep a (h, c2) s' \<or>
    a = Tau \<and> (\<exists>h' c1'. s' = (h', c1' \<box> c2) \<and> lopstep Tau (h, c1) (h', c1')) \<or>
    a = Tau \<and> (\<exists>h' c2'. s' = (h', c1 \<box> c2') \<and> lopstep Tau (h, c2) (h', c2')) \<or>
    a = Tau \<and> c1 = Skip \<and> s' = (h, c2) \<or>
    a = Tau \<and> c2 = Skip \<and> s' = (h, c1)\<close>
  \<open>lopstep a (h, c1 \<parallel> c2) s' \<longleftrightarrow>
    a = Tau \<and> c1 = Skip \<and> c2 = Skip \<and> s' = (h, Skip) \<or>
    (\<exists>h' c1'. lopstep a (h,c1) (h',c1') \<and> s' = (h', c1' \<parallel> c2)) \<or>
    (\<exists>h' c2'. lopstep a (h,c2) (h',c2') \<and> s' = (h', c1 \<parallel> c2'))\<close>
  \<open>lopstep a (h, DO c OD) s' \<longleftrightarrow>
    a = Tau \<and> \<not> pre_state (\<Squnion>(head_atoms c)) h \<and> s' = (h, Skip) \<or>
    a = Tau \<and> s' = (h, c ;; DO c OD)\<close>
  \<open>lopstep a (h, \<mu> c) s' \<longleftrightarrow>
    a = Tau \<and> s' = (h, c[0 \<leftarrow> \<mu> c])\<close>
  \<open>lopstep a (h, Atomic b) s' \<longleftrightarrow>
    snd s' = Skip \<and> b h (fst s') \<and> a = Loc (snd h, snd (fst s'))\<close>
         apply -
         apply fastforce
        apply fastforce
       apply fastforce
      apply (rule iffI, (erule lopstep_endetE; force), blast)
     apply (rule iffI, (erule lopstep_parE; force), blast)
    apply fastforce
   apply fastforce
  apply (rule iffI, (erule lopstep_atomicE; force), (cases s', force))
  done

lemma lopstep_tau_stepD:
  assumes \<open>lopstep Tau s s'\<close>
  shows \<open>fst s' = fst s\<close>
proof -
  { fix a
    have \<open>lopstep a s s' \<Longrightarrow> a = Tau \<Longrightarrow> fst s' = fst s\<close>
      by (induct rule: lopstep.inducts) force+
  }
  then show ?thesis
    using assms opstep_def by blast
qed

lemma opstep_tau_stepD:
  \<open>s \<midarrow>Tau\<rightarrow> s' \<Longrightarrow> fst s' = fst s\<close>
  by (force dest: lopstep_tau_stepD simp add: opstep_def)


lemma lopstep_loc_stepD:
  assumes \<open>lopstep (Loc x) s s'\<close>
  shows \<open>x = (snd (fst s), snd (fst s'))\<close>
proof -
  { fix a
    have \<open>lopstep a s s' \<Longrightarrow> a = Loc x \<Longrightarrow> x = (snd (fst s), snd (fst s'))\<close>
      by (induct arbitrary: x rule: lopstep.inducts) force+
  }
  then show ?thesis
    using assms opstep_def by blast
qed

lemma opstep_loc_stepD:
  \<open>s \<midarrow>Loc x\<rightarrow> s' \<Longrightarrow> x = (snd (fst s), snd (fst s'))\<close>
  by (force dest: lopstep_loc_stepD simp add: opstep_def)


lemma lopstep_env_iff[simp]:
  \<open>lopstep (Env x) s s' \<longleftrightarrow> False\<close>
proof -
  { fix a
    have \<open>lopstep a s s' \<Longrightarrow> a = Env x \<Longrightarrow> False\<close>
      by (induct arbitrary: x rule: lopstep.inducts) fastforce+
  }
  then show ?thesis by force
qed

lemma opstep_env_stepD:
  assumes \<open>s \<midarrow>Env x\<rightarrow> s'\<close>
  shows \<open>fst (fst s) = fst (fst s') \<and> x = (snd (fst s), snd (fst s')) \<and> snd s = snd s'\<close>
  using assms
  by (simp add: opstep_def)


lemma opstep_act_cases:
  \<open>s \<midarrow>a\<rightarrow> s' \<Longrightarrow>
    (a = Tau \<Longrightarrow> s \<midarrow>Tau\<rightarrow> s' \<Longrightarrow> fst s' = fst s \<Longrightarrow> P) \<Longrightarrow>
    (a = Loc (snd (fst s), snd (fst s')) \<Longrightarrow> s \<midarrow>Loc (snd (fst s), snd (fst s'))\<rightarrow> s' \<Longrightarrow> P) \<Longrightarrow>
    (a = Env (snd (fst s), snd (fst s')) \<Longrightarrow>
      fst (fst s) = fst (fst s') \<Longrightarrow>
      snd s = snd s' \<Longrightarrow>
      s \<midarrow>Env (snd (fst s), snd (fst s'))\<rightarrow> s' \<Longrightarrow> P) \<Longrightarrow>
    P\<close>
  by (cases a, metis opstep_tau_stepD, metis opstep_loc_stepD, metis opstep_env_stepD)

lemma all_atom_comm_lopstep:
  assumes
    \<open>lopstep a (h, c) (h', c')\<close>
    \<open>all_atom_comm p c\<close>
  shows
    \<open>all_atom_comm p c'\<close>
proof -
  { fix s s'
    assume \<open>lopstep a s s'\<close>
      and \<open>all_atom_comm p (snd s)\<close>
    then have \<open>all_atom_comm p (snd s')\<close>
      by (induct rule: lopstep.inducts) force+
  }
  then show ?thesis
    using assms
    by (metis snd_conv)
qed

lemmas all_atom_comm_lopstepD =
  all_atom_comm_lopstep[rotated]

lemma lopstep_locD':
  \<open>lopstep a s s' \<Longrightarrow>
    s = (h, c) \<Longrightarrow>
    s' = (h', c') \<Longrightarrow>
    a = Loc (hy, hy') \<Longrightarrow>
    weak_framed_subresource_rel \<top> hy hy' (snd h) (snd h')\<close>
  by (induct arbitrary: hy hy' h c h' c' rule: lopstep.inducts)
    blast+

lemma lopstep_locD:
  \<open>lopstep (Loc (hx, hx')) (h, c) (h', c') \<Longrightarrow>
    weak_framed_subresource_rel \<top> hx hx' (snd h) (snd h')\<close>
  by (metis lopstep_locD')


subsubsection \<open> adding parallel \<close>

lemma lopstep_parallel_leftD:
  \<open>s \<midarrow>a\<rightarrow> s' \<Longrightarrow> (fst s, snd s \<parallel> cy) \<midarrow>a\<rightarrow> (fst s', snd s' \<parallel> cy)\<close>
  by (fastforce simp add: opstep_def)

lemma lopstep_parallel_rightD:
  \<open>s \<midarrow>a\<rightarrow> s' \<Longrightarrow> (fst s, cx \<parallel> snd s) \<midarrow>a\<rightarrow> (fst s', cx \<parallel> snd s')\<close>
  by (fastforce simp add: opstep_def)


subsubsection \<open> iteraction with all_atom_comm \<close>

lemma lopstep_preserves_all_atom_comm:
  assumes
    \<open>lopstep a (h, c) (h', c')\<close>
    \<open>all_atom_comm p c\<close>
  shows \<open>all_atom_comm p c'\<close>
proof -
  { fix s s'
    have \<open>lopstep a s s' \<Longrightarrow> all_atom_comm p (snd s) \<Longrightarrow> all_atom_comm p (snd s')\<close>
      by (induct arbitrary: h' rule: lopstep.inducts) force+
  }
  then show ?thesis
    using assms
    by (metis snd_conv)
qed

lemmas rev_lopstep_preserves_all_atom_comm = lopstep_preserves_all_atom_comm[rotated]


subsection \<open> Opstep rules for defined programs \<close>

lemma lopstep_guard[intro!]:
  \<open>p h \<Longrightarrow>
    hsx' = hsx \<Longrightarrow>
    hsx = snd h \<Longrightarrow>
    h' = h \<Longrightarrow>
    lopstep (Loc (hsx, hsx')) (h, Guard p) (h', Skip)\<close>
  by (force simp add: Guard_def lopstep_iff less_eq_sepadd_def')

lemma lopstep_IfThenElse_iff[lopstep_iff]:
  \<open>lopstep a (h, IfThenElse p ct cf) s' \<longleftrightarrow>
    a = Loc (snd h, snd h) \<and>
    (p h \<and> s' = (h, Skip ;; ct) \<or>
      \<not> p h \<and> s' = (h, Skip ;; cf))\<close>
  by (force simp add: IfThenElse_def lopstep_iff weak_framed_subresource_rel_def
      framed_subresource_rel_def less_eq_sepadd_def')

lemma lopstep_IfThenElse_true[intro]:
  \<open>p h \<Longrightarrow>
    xy = (snd h, snd h) \<Longrightarrow>
    c' = Skip ;; ct \<Longrightarrow>
    lopstep (Loc xy) (h, IfThenElse p ct cf) (h, c')\<close>
  by (simp add: lopstep_iff)

lemma lopstep_IfThenElse_false[intro]:
  \<open>\<not> p h \<Longrightarrow>
    xy = (snd h, snd h) \<Longrightarrow>
    c' = Skip ;; cf \<Longrightarrow>
    lopstep (Loc xy) (h, IfThenElse p ct cf) (h, c')\<close>
  by (simp add: lopstep_iff)

lemma pre_state_pguard_eq[simp]:
  \<open>pre_state (pguard p) = p\<close>
  by (simp add: pguard_def pre_state_def)

lemma lopstep_WhileLoop_iff[lopstep_iff]:
  \<open>lopstep a (h, WhileLoop p c) s' \<longleftrightarrow>
    a = Tau \<and> s' = (h,
      (Guard p ;; c \<box> Guard (- p)) ;;
        DO Guard p ;; c \<box> Guard (- p) OD)\<close>
  by (simp add: WhileLoop_def lopstep_iff)


section \<open> Safe \<close>


inductive safe
  :: \<open>('s \<times> 's) act list set \<Rightarrow>
      ('l::perm_alg \<times> 's::perm_alg) comm \<Rightarrow>
      'l \<Rightarrow>
      's \<Rightarrow>
      ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
      ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
      ('l \<times> 's \<Rightarrow> bool) \<Rightarrow>
      ('l \<Rightarrow> bool) \<Rightarrow>
      bool\<close>
  where
  safe_nil[intro]: \<open>safe {[]} c hl hs r g q F\<close>
| safe_suc[intro]:
  \<open>[] \<notin> T \<Longrightarrow>
    (\<forall>t1\<in>T. \<forall>t2\<in>T. length t1 = length t2) \<Longrightarrow>
    \<comment> \<open> if the command is Skip, the postcondition is established \<close>
    \<comment> \<open> TODO: This requires termination is represented as infinite stuttering past the end.
               We may want a different model. \<close>
    (c = Skip \<longrightarrow> q (hl, hs)) \<Longrightarrow>
    \<comment> \<open> opsteps are safe \<close>
    (\<And>a c' hl' hs'.
      ((hl, hs), c) \<midarrow>a\<rightarrow> ((hl', hs'), c') \<Longrightarrow>
      safe {t. a#t \<in> T} c' hl' hs' r g q F) \<Longrightarrow>
    \<comment> \<open> lopsteps are frame closed \<close>
    (\<And>a c' hlf hlhlf' hs'.
      lopstep a ((hl + hlf, hs), c) ((hlhlf', hs'), c') \<Longrightarrow>
      hl ## hlf \<Longrightarrow>
      F hlf \<Longrightarrow>
      (\<exists>hl'.
        hl' ## hlf \<and> hlhlf' = hl' + hlf \<and>
        (a = Tau \<longrightarrow> hl' = hl) \<and>
        safe {t. a#t \<in> T} c' hl' hs' r g q F)) \<Longrightarrow>
    \<comment> \<open> conclude a step can be made \<close>
    safe T c hl hs r g q F\<close>

subsection \<open> Proofs about safe \<close>

inductive_cases safeE[elim]: \<open>safe T c hl hs q F\<close>

lemma safe_nil_iff[simp]:
  \<open>safe {[]} c hl hs q F \<longleftrightarrow> True\<close>
  by force

lemma safe_suc_iff:
  \<open>[] \<notin> T \<Longrightarrow>
    \<forall>t1\<in>T. \<forall>t2\<in>T. length t1 = length t2 \<Longrightarrow>
    safe T c hl hs q F \<longleftrightarrow>
    (c = Skip \<longrightarrow> q (hl, hs)) \<and>
    (\<forall>a c' hx'.
      ((hl, hs), c) \<midarrow>a\<rightarrow> (hx', c') \<longrightarrow>
      safe {t. a # t \<in> T} c' (fst hx') (snd hx') q F) \<and>
    (\<forall>a c' hlf hx'.
      lopstep a ((hl + hlf, hs), c) (hx', c') \<longrightarrow>
      hl ## hlf \<longrightarrow>
      F hlf \<longrightarrow>
      (\<exists>hl'.
        hl' ## hlf \<and> fst hx' = hl' + hlf \<and>
        (a = Tau \<longrightarrow> hl' = hl) \<and>
        safe {t. a # t \<in> T} c' hl' (snd hx') q F))\<close>
  apply (rule iffI)
   apply (erule safeE, blast)
   apply (metis prod.collapse)
  apply (rule safe_suc; force)
  done

(*
lemma safe_suc_env_iff:
  \<open>safe (Env (x, hs') # as) c hl hs q F \<longleftrightarrow>
    (c = Skip \<longrightarrow> q (hl, hs)) \<and>
    (x = hs \<longrightarrow> safe as c hl hs' q F)\<close>
  by (simp add: safe_suc_iff opstep_def)
*)

lemma safe_sucD[consumes 3]:
  \<open>safe T c hl hs q F \<Longrightarrow>
    [] \<notin> T \<Longrightarrow> \<forall>t1\<in>T. \<forall>t2\<in>T. length t1 = length t2 \<Longrightarrow>
    c = Skip \<Longrightarrow> q (hl, hs)\<close>
  \<open>safe T c hl hs q F \<Longrightarrow>
    [] \<notin> T \<Longrightarrow> \<forall>t1\<in>T. \<forall>t2\<in>T. length t1 = length t2 \<Longrightarrow>
    ((hl, hs), c) \<midarrow>a\<rightarrow> ((hl', hs'), c') \<Longrightarrow>
    safe {t. a#t\<in>T} c' hl' hs' q F\<close>
  \<open>safe T c hl hs q F \<Longrightarrow>
    [] \<notin> T \<Longrightarrow> \<forall>t1\<in>T. \<forall>t2\<in>T. length t1 = length t2 \<Longrightarrow>
    lopstep a ((hl + hlf, hs), c) ((hlhlf', hs'), c') \<Longrightarrow>
    hl ## hlf \<Longrightarrow>
    F hlf \<Longrightarrow>
    (\<exists>hl'.
      hl' ## hlf \<and> hlhlf' = hl' + hlf \<and>
      (a = Tau \<longrightarrow> hl' = hl) \<and>
      safe {t. a#t\<in>T} c' hl' hs' q F)\<close>
  by (erule safeE, blast, presburger)+
  

lemma safe_suc_frame_leftD:
  \<open>safe T c hl hs q F \<Longrightarrow>
    [] \<notin> T \<Longrightarrow> \<forall>t1\<in>T. \<forall>t2\<in>T. length t1 = length t2 \<Longrightarrow>
    lopstep a ((hlf + hl, hs), c) ((hlfhl', hs'), c') \<Longrightarrow>
    hlf ## hl \<Longrightarrow>
    F hlf \<Longrightarrow>
    (\<exists>hl'.
      hl' ## hlf \<and> hlfhl' = hlf + hl' \<and>
      (a = Tau \<longrightarrow> hl' = hl) \<and>
      safe {t. a#t\<in>T} c' hl' hs' q F)\<close>
  apply (drule safe_sucD(3))
       apply blast
      apply blast
     apply (simp add: disjoint_sym_iff[of _ hlf] partial_add_commute[of hlf]; fail)
    apply (simp add: disjoint_sym_iff[of _ hlf] partial_add_commute[of hlf]; fail)
   apply blast
  apply (force simp add: disjoint_sym_iff[of hlf] partial_add_commute[of _ hlf])
  done


subsubsection \<open> Monotonicity of safe \<close>

lemma safe_postpred_monoD:
  \<open>safe n c hl hs q F \<Longrightarrow> q \<le> q' \<Longrightarrow> safe n c hl hs q' F\<close>
  apply (induct rule: safe.induct)
   apply blast
  apply (rule safe_suc)
      apply blast
     apply blast
    apply (clarsimp simp add: le_fun_def; fail)+
  apply metis
  done

lemmas safe_postpred_mono = safe_postpred_monoD[rotated]

(*
lemma safe_step_antimonoD:
  \<open>safe as c hl hs q F \<Longrightarrow> as' \<le>\<^sub>l as \<Longrightarrow> safe as' c hl hs q F\<close>
proof (rotate_tac, induct arbitrary: c hl hs q rule: sublisteq.inducts)
  case (same xs ys x)
  then show ?case
    apply -
    apply (rule safe_suc)
      apply blast
     apply (metis safe_sucD(2))
    apply (frule(1) safe_sucD; blast)
    done
qed blast
*)

lemma safe_frameset_antimonoD:
  \<open>safe n c hl hs q F \<Longrightarrow> F' \<le> F \<Longrightarrow> safe n c hl hs q F'\<close>
  apply (induct arbitrary: F' rule: safe.inducts)
   apply force
  apply clarsimp
  apply (rule safe_suc)
      apply blast
     apply blast
    apply force
   apply force
  apply (simp add: le_fun_def, metis)
  done


subsection \<open> Safety of Skip \<close>

lemma safe_skip':
  \<open>trace_rely as \<le> r \<Longrightarrow> sswa r q (hl, hs) \<Longrightarrow> safe as Skip hl hs (sswa r q) F\<close>
  apply (induct as arbitrary: hl hs q)
  apply force
  apply (rule safe_suc)
    apply force
   apply (simp add: opstep_def, erule disjE)
    apply blast
   apply (clarsimp, metis rel_step_def rev_predicate2D sswa_step)
  apply force
  done

lemma safe_skip:
  \<open>p (hl, hs) \<Longrightarrow> sswa (trace_rely as) p \<le> q \<Longrightarrow> safe as Skip hl hs q F\<close>
  apply (rule safe_postpred_monoD[OF safe_skip'[where q=p]])
    apply blast
   apply (metis (mono_tags, lifting) rel_Times_iff rtranclp.rtrancl_refl sp_def)
  apply blast
  done


subsection \<open> Safety of frame \<close>

lemma safe_frame':
  \<open>safe as c hl hs q F \<Longrightarrow>
    hl ## hlf \<Longrightarrow>
    trace_rely as \<le> r \<Longrightarrow>
    trace_guar as \<le> g \<Longrightarrow>
    sswa (r \<squnion> g) f \<le> F \<times>\<^sub>P \<top> \<Longrightarrow>
    sswa (r \<squnion> g) f (hlf, hs) \<Longrightarrow>
    safe as c (hl + hlf) hs (q \<^emph>\<and> sswa (r \<squnion> g) f) (F \<midarrow>\<^emph> F)\<close>
proof (induct arbitrary: hlf rule: safe.induct)
  case (safe_suc c q hl hs a as F)
  show ?case
    using safe_suc.prems
    apply -
    apply (rule safe.safe_suc)
      (* subgoal: skip *)
         apply (clarsimp simp add: sepconj_conj_def simp del: sup_apply top_apply)
         apply (drule mp[OF safe_suc.hyps(1)])
         apply blast
      (* subgoal: step *)
    sorry
(*
      apply (rule safe_suc.hyps(2))
      apply (rule sswa_step[of _ hs], rule sup2I1)
       apply (simp, blast)
      apply blast
      (* subgoal: plain lopstep *)
     apply (frule safe_suc.hyps(6), blast, force)
     apply (erule lopstep_act_cases, force)
     apply (clarsimp simp del: sup_apply top_apply)
     apply (rename_tac hl')
     apply (subgoal_tac \<open>sswa (r \<squnion> g) f (hlf, hs')\<close>)
      prefer 2
      apply (metis (no_types, opaque_lifting) predicate2D rel_step_def sswa_step sup2I2)
     apply blast
      (* subgoal: framed lopstep *)
    apply (clarsimp simp add: partial_add_assoc2[of hl hlf] simp del: sup_apply top_apply)
    apply (frule safe_suc.hyps(6))
      apply (metis disjoint_add_swap_lr)
     apply (simp add: le_fun_def sepimp_def)
     apply (metis (mono_tags) disjoint_add_leftR disjoint_sym_iff partial_add_commute)
    apply (rename_tac hlf2 hl'hlfhlf2 hs')
    apply (clarsimp simp del: sup_apply top_apply)
    apply (erule lopstep_act_cases, force simp add: partial_add_assoc2)
    apply (clarsimp simp del: sup_apply top_apply)
    apply (intro exI conjI)
      prefer 2
      apply (rule partial_add_assoc[symmetric])
        apply (metis disjoint_add_leftR disjoint_add_rightL)
       apply (metis disjoint_add_leftR)
      apply (metis disjoint_add_leftR disjoint_add_rightR)
     apply (metis disjoint_add_leftR disjoint_add_swap_rl)
    apply (subgoal_tac \<open>sswa (r \<squnion> g) f (hlf, hs')\<close>)
     prefer 2
     apply (metis (no_types, opaque_lifting) predicate2D rel_step_def sswa_step sup2I2)
    apply (metis disjoint_add_leftR disjoint_add_rightL)
    done
*)
qed simp

lemma safe_frame:
  \<open>safe as c hl hs q F \<Longrightarrow>
    hl ## hlf \<Longrightarrow>
    f (hlf, hs) \<Longrightarrow>
    sswa (trace_rely as \<squnion> trace_guar as) f \<le> F \<times>\<^sub>P \<top> \<Longrightarrow>
    sswa (trace_rely as \<squnion> trace_guar as) f \<le> f' \<Longrightarrow>
    F' \<le> F \<midarrow>\<^emph> F \<Longrightarrow>
    safe as c (hl + hlf) hs (q \<^emph>\<and> f') F'\<close>
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
    trace_rely as \<le> r \<Longrightarrow>
    trace_guar as \<le> g \<Longrightarrow>
    \<forall>f. f \<le> F \<times>\<^sub>P \<top> \<longrightarrow> sp b (wssa r (p \<^emph>\<and> f)) \<le> sswa r (q \<^emph>\<and> f) \<Longrightarrow>
    b \<le> \<top> \<times>\<^sub>R g \<Longrightarrow>
    wssa r p (hl, hs) \<Longrightarrow>
    safe as (Atomic b) hl hs (sswa r q) F\<close>
proof (induct as arbitrary: hl hs)
  case (Cons a as)
  show ?case
    using Cons.prems
    apply (intro safe.safe_suc)
      (* subgoal: skip *)
       apply force
      (* subgoal: rely *)
    sorry
(*
      apply (rule Cons.hyps)
           apply blast
          apply (metis le_supE trace_rely_simps(2))
         apply (simp; fail)
        apply force
       apply force
      apply (clarsimp simp add: le_fun_def all_conj_distrib)
      apply (metis wssa_step)
      (* subgoal: plain lopstep *)
     apply (clarsimp simp add: lopstep_iff simp del: top_apply sup_apply)
     apply (rule safe_skip[where p=\<open>sswa r q\<close>])
      apply (metis sp_impliesD)
     apply (metis sswa_idem sswa_rel_mono)
      (* subgoal: framed lopstep *)
    apply (drule_tac x=\<open>wssa r ((=) hlf \<times>\<^sub>P \<top>)\<close> in spec)
    apply (clarsimp simp add: lopstep_iff sp_def[of b] imp_ex_conjL le_fun_def simp del: sup_apply)
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
    apply (metis (no_types, opaque_lifting) Cons.prems(2) safe_skip' trace_rely_simps(3))
    done
*)
qed simp

lemma safe_atom:
  \<open>sp b (wssa (trace_rely as) p) \<le> sswa (trace_rely as) q \<Longrightarrow>
    \<forall>f. f \<le> F \<times>\<^sub>P \<top> \<longrightarrow> sp b (wssa (trace_rely as) (p \<^emph>\<and> f)) \<le> sswa (trace_rely as) (q \<^emph>\<and> f) \<Longrightarrow>
    b \<le> \<top> \<times>\<^sub>R (trace_guar as) \<Longrightarrow>
    wssa (trace_rely as) p (hl, hs) \<Longrightarrow>
    sswa (trace_rely as) q \<le> q' \<Longrightarrow>
    safe as (Atomic b) hl hs q' F\<close>
  by (meson order.refl safe_atom' safe_postpred_mono)


subsection \<open> Safety of Sequencing \<close>

lemma safe_seq_assoc_left:
  \<open>safe n c hl hs q F \<Longrightarrow>
    c = (c1 ;; c2 ;; c3) \<Longrightarrow>
    safe n ((c1 ;; c2) ;; c3) hl hs q F\<close>
  apply (induct arbitrary: c1 c2 c3 rule: safe.inducts)
   apply force
  apply (rule safe_suc)
    apply blast
   apply (simp add: opstep_def lopstep_iff, metis)
  apply (simp add: lopstep_iff, metis)
  done

lemma safe_seq_assoc_right:
  \<open>safe n c hl hs q F \<Longrightarrow>
    c = ((c1 ;; c2) ;; c3) \<Longrightarrow>
    safe n (c1 ;; c2 ;; c3) hl hs q F\<close>
  apply (induct arbitrary: c1 c2 c3 rule: safe.inducts)
   apply force
  apply (rule safe_suc)
    apply blast
   apply (simp add: opstep_def lopstep_iff, metis)
  apply (simp add: lopstep_iff, metis)
  done

lemma safe_seq':
  \<open>safe as c1 hl hs q F \<Longrightarrow>
    (\<forall>as' hl' hs'. as' \<le>\<^sub>r as \<longrightarrow> q (hl', hs') \<longrightarrow> safe as' c2 hl' hs' q' F) \<Longrightarrow>
    safe as (c1 ;; c2) hl hs q' F\<close>
proof (induct arbitrary: c2 q' rule: safe.inducts)
  case (safe_suc c1 q hl hs a as F)

  have c2_safe_suc:
    \<open>\<And>as' hl' hs'. as' \<le>\<^sub>r as \<Longrightarrow> q (hl', hs') \<Longrightarrow> safe as' c2 hl' hs' q' F\<close>
    \<open>\<And>hl' hs'. q (hl', hs') \<Longrightarrow> safe (a # as) c2 hl' hs' q' F\<close>
    using safe_suc.prems
    by (simp add: rev_sublisteq_Cons_iff all_conj_distrib)+

  show ?case
    using safe_suc.hyps(1)
    apply -
    apply (rule safe.safe_suc)
      (* subgoal: skip *)
      apply force
    sorry
(*
      (* subgoal: rely *)
      apply (rule safe_suc.hyps(3), force)
      apply (simp add: c2_safe_suc(1); fail)
      (* subgoal: plain lopstep *)
     apply (clarsimp simp add: lopstep_iff simp del: sup_apply)
     apply (erule disjE[of _ \<open>Ex _\<close>])
      apply (simp add: c2_safe_suc(1); fail)
     apply (clarsimp simp del: sup_apply)
     apply (frule safe_suc.hyps(5))
      prefer 2
      apply assumption
     apply (simp add: c2_safe_suc(1); fail)
      (* subgoal: framed lopstep *)
    apply (clarsimp simp add: lopstep_iff simp del: sup_apply)
    apply (erule disjE[of _ \<open>Ex _\<close>])
     apply (simp add: c2_safe_suc(1); fail)
    apply clarsimp
    apply (frule safe_suc.hyps(6), blast, blast)
    apply (metis c2_safe_suc(1))
    done
*)
qed force

lemma safe_seq:
  \<open>safe as c1 hl hs q F \<Longrightarrow>
    (\<forall>as' hl' hs'. as' \<le>\<^sub>r as \<longrightarrow> q (hl', hs') \<longrightarrow> safe as' c2 hl' hs' q' F) \<Longrightarrow>
    safe as (c1 ;; c2) hl hs q' F\<close>
  by (force intro: safe_seq' safe_step_antimonoD)


subsection \<open> Safety of Iter \<close>

lemma safe_iter:
  \<open>(\<And>as' hl' hs'. as' \<le>\<^sub>r as \<Longrightarrow> sswa r i (hl', hs') \<Longrightarrow> safe as' c hl' hs' (sswa r i) F) \<Longrightarrow>
    trace_rely as \<le> r \<Longrightarrow>
    sswa r i (hl, hs) \<Longrightarrow>
    safe as (Iter c) hl hs (sswa r i) F\<close>
proof (induct as arbitrary: i hl hs rule: rev_sublisteq_list_strong_induct)
  case (ConsLess a as)

  have safe_c2:
    \<open>\<And>as' hl' hs'. as' \<le>\<^sub>r as \<Longrightarrow> sswa r i (hl', hs') \<Longrightarrow> safe as' c hl' hs' (sswa r i) F\<close>
    \<open>\<And>hl' hs'. sswa r i (hl', hs') \<Longrightarrow> safe (a # as) c hl' hs' (sswa r i) F\<close>
    using ConsLess.prems(1)
    by (simp add: rev_sublisteq_Cons_iff)+
  note safe_c2_sucD = safe_sucD[OF safe_c2(2)]

  show ?case
    using ConsLess.prems(2-)
    apply -
    apply (rule safe.safe_suc)
      (* subgoal: skip *)
      apply blast
    sorry
(*
      (* subgoal: rely *)
      apply (rule ConsLess.hyps)
         apply blast
        apply (fast intro: safe_c2(1))
       apply force
      apply (clarsimp simp del: sup_apply)
      apply (metis predicate2D_conj rel_step_apply sswa_step)
      (* subgoal: plain lopstep *)
     apply (simp add: lopstep_iff)
     apply (erule disjE[of \<open>_ \<and> _\<close>])
      apply (simp add: rely_rel_wlp_impl_sp safe_skip'; fail)
     apply clarsimp
     apply (rule safe_seq')
      apply (rule safe_c2(1), fast, fast)
     apply clarsimp
     apply (rule ConsLess.hyps)
        apply blast
       apply (metis rev_sublisteq_trans safe_c2(1))
      apply (metis order.trans trace_rely_rev_sublisteq_mono)
     apply blast
      (* subgoal: locally framed lopstep *)
    apply (clarsimp simp add: le_Suc_eq all_conj_distrib lopstep_iff)
    apply (erule disjE[of \<open>_ \<and> _\<close>])
     apply (simp add: rely_rel_wlp_impl_sp safe_skip'; fail)
    apply clarsimp
    apply (rule safe_seq')
     apply (rule safe_c2(1), fast, fast)
    apply clarsimp
    apply (rule ConsLess.hyps)
       apply blast
      apply (metis rev_sublisteq_trans safe_c2(1))
     apply (metis order.trans trace_rely_rev_sublisteq_mono)
    apply blast
    done
*)
qed force


subsubsection \<open> Safety of internal nondeterminism \<close>

lemma safe_indet:
  \<open>safe as c1 hl hs q F \<Longrightarrow>
    safe as c2 hl hs q F \<Longrightarrow>
    safe as (c1 \<^bold>+ c2) hl hs q F\<close>
proof (induct as arbitrary: c1 c2 hl hs)
  case (Cons a as)

  have safeSuc:
    \<open>safe (a # as) c1 hl hs q F\<close>
    \<open>safe (a # as) c2 hl hs q F\<close>
    using Cons.prems
    by simp+
  note safe_suc1 = safe_sucD[OF safeSuc(1)]
  note safe_suc2 = safe_sucD[OF safeSuc(2)]

  show ?case
    apply -
    apply (rule safe_suc)
      apply blast
    sorry (*
      (* subgoal: rely *)
        apply (simp add: Cons.hyps safe_suc1(2) safe_suc2(2); fail)
      (* subgoal: plain lopstep *)
     apply (clarsimp simp add: lopstep_iff simp del: sup_apply)
     apply (metis safe_suc1(3) safe_suc2(3))
      (* subgoal: local frame lopstep *)
    apply (clarsimp simp add: lopstep_iff simp del: sup_apply)
    apply (elim disjE[of \<open>lopstep _ _ _\<close>])
     apply (erule lopstep_act_cases; metis safe_suc1(4))
    apply (erule lopstep_act_cases; metis safe_suc2(4))
    done
*)
qed blast


subsubsection \<open> Safety of external nondeterminism \<close>

inductive endet_merge :: \<open>'a act list \<Rightarrow> 'a act list \<Rightarrow> 'a act list \<Rightarrow> bool\<close> where
  endet_merge_empty[intro!]: \<open>endet_merge [] [] []\<close>
| endet_merge_stepL[intro!]: \<open>as1 = as \<Longrightarrow> endet_merge (Loc x # as) (Loc x # as1) as2\<close>
| endet_merge_stepR[intro!]: \<open>as2 = as \<Longrightarrow> endet_merge (Loc x # as) as1 (Loc x # as2)\<close>
| endet_merge_tauL[intro]: \<open>endet_merge as as1 as2 \<Longrightarrow> endet_merge (Tau # as) (Tau # as1) as2\<close>
| endet_merge_tauR[intro]: \<open>endet_merge as as1 as2 \<Longrightarrow> endet_merge (Tau # as) as1 (Tau # as2)\<close>

inductive_cases endet_merge_Nil1E[elim!]: \<open>endet_merge [] as1 as2\<close>
inductive_cases endet_merge_Nil2E[elim!]: \<open>endet_merge as [] as2\<close>
inductive_cases endet_merge_Nil3E[elim!]: \<open>endet_merge as as1 []\<close>

inductive_cases endet_merge_Cons1E[elim]: \<open>endet_merge (a # as) as1' as2'\<close>
inductive_cases endet_merge_Cons2E[elim]: \<open>endet_merge as' (a # as1) as2'\<close>
inductive_cases endet_merge_Cons3E[elim]: \<open>endet_merge as' as1' (a # as2)\<close>

lemma endet_merge_Cons1_simps:
  \<open>endet_merge (Loc x # asx) as1 as2 \<longleftrightarrow>
    as1 = Loc x # asx \<or> as2 = Loc x # asx\<close>
  \<open>endet_merge (Env x # asx) as1 as2 \<longleftrightarrow> False\<close>
  \<open>endet_merge (Tau # asx) as1 as2 \<longleftrightarrow>
    (\<exists>as1x. as1 = Tau # as1x \<and> endet_merge asx as1x as2) \<or>
    (\<exists>as2x. as2 = Tau # as2x \<and> endet_merge asx as1 as2x)\<close>
  by auto

lemma safe_endet:
  \<open>safe as1 c1 hl hs q F \<Longrightarrow>
    safe as2 c2 hl hs q F \<Longrightarrow>
    endet_merge as as1 as2 \<Longrightarrow>
    safe as (c1 \<box> c2) hl hs q F\<close>
proof (induct as arbitrary: as1 as2 c1 c2 hl hs rule: rev_sublisteq_list_strong_induct)
  case (ConsLess a as)
  show ?case
    using ConsLess.prems
    apply -
    apply (rule safe.safe_suc)
      apply blast
     apply (clarsimp simp add: opstep_def, erule disjE)
      (* subgoal: plain lopstep *)
      apply (clarsimp simp add: lopstep_iff simp del: sup_apply)
      apply (elim disjE conjE exE; simp add: safe_suc_env_iff)
           apply (simp add: endet_merge_Cons1_simps)
           apply (erule disjE)
            apply (meson opstep_def safe_sucD(2); fail)
    subgoal sorry
          apply (simp add: endet_merge_Cons1_simps)
          apply (erule disjE)
    subgoal sorry
          apply (meson opstep_def safe_sucD(2); fail)
         apply (frule lopstep_tau_stepD)
         apply (clarsimp simp add: endet_merge_Cons1_simps)
         apply (erule disjE)
          apply clarsimp
          apply (erule safe_sucE)
          apply (meson ConsLess.hyps opstep_def rev_sublisteq.same; fail)
          apply clarsimp
         apply (erule safe_sucE)
    subgoal sorry
        apply clarsimp
    subgoal sorry
    subgoal sorry
    oops
           apply (metis safe_sucE)
       apply (rule ConsLess.hyps)
         apply blast
        apply (simp add: safe_suc1(2); fail)
       apply (simp add: safe_suc2(5); fail)
      apply (fastforce dest: safe_suc2(2))
    apply (fastforce dest: safe_suc1(2))

      (* subgoal: rely *)
          apply (clarsimp simp add: safe_suc_env_iff)
          apply (rule ConsLess.hyps; blast)
         apply force
        apply force
       apply force
      apply force
      (* subgoal: local frame lopstep *)
    apply (clarsimp simp add: lopstep_iff simp del: sup_apply)
    apply (elim disjE[of \<open>_ \<and> _\<close>] conjE exE)
         apply (erule lopstep_act_cases; metis safe_suc1(6))
        apply (erule lopstep_act_cases; metis safe_suc2(6))
      (* subsubgoal: left tau passthrough *)
       apply (frule safe_suc1(6), blast, blast, blast)
       apply (clarsimp simp del: sup_apply)
       apply (frule lopstep_tau_stepD)
       apply (clarsimp simp del: sup_apply)
       apply (rule ConsLess.hyps)
         apply blast
        apply blast
       apply (metis safe_suc2(2))
      (* subsubgoal: right tau passthrough *)
      apply (frule safe_suc2(6), blast, blast, blast)
      apply clarsimp
      apply (frule lopstep_tau_stepD)
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
      apply (clarsimp simp add: lopstep_iff merge_tr_Cons1_simps simp del: sup_apply top_apply)
      apply (elim disjE conjE exE)
         apply (clarsimp simp del: sup_apply top_apply)
         apply (metis partial_le_part_left safe_sucD(4))
        apply (clarsimp simp del: sup_apply top_apply)
      subgoal sorry
      subgoal sorry
      apply (clarsimp simp del: sup_apply top_apply)
      apply (metis partial_le_part_right safe_sucD(4))
      done
      (* subgoal: plain lopstep safe *)
    subgoal
      apply (simp add: lopstep_iff del: sup_apply top_apply)
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
       apply (erule lopstep_act_cases)
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
       apply (erule lopstep_act_cases)
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
      (* subgoal: framed lopstep safe *)
    subgoal
      sorry
(*
      apply (simp add: lopstep_iff del: sup_apply top_apply)
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
       apply (erule lopstep_act_cases)
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
      apply (erule lopstep_act_cases)
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
    safe n (c1 \<parallel> c2) (hl1 + hl2) hs q \<top>\<close>
  sorry
(*
  by (meson safe_guarantee_monoD safe_parallel' safe_postpred_mono)
*)

subsection \<open> Safety of conj \<close>

lemma safe_conj':
  \<open>safe as c hl hs q1 F1 \<Longrightarrow>
    safe as c hl hs q2 F2 \<Longrightarrow>
    \<forall>a b c. F1 c \<longrightarrow> F2 c \<longrightarrow> a ## c \<longrightarrow> b ## c \<longrightarrow> a + c = b + c \<longrightarrow> a = b \<Longrightarrow>
    safe as c hl hs r g (q1 \<sqinter> q2) (F1 \<sqinter> F2)\<close>
proof (induct as arbitrary: c hl hs q1 q2)
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
      (* subgoal: plain lopstep *)
     apply (rule Cons.hyps)
       apply fastforce
      apply force
     apply force
      (* subgoal: frame lopstep *)
    apply (clarsimp simp del: inf_apply)
    apply (frule safe_sucD(6)[where q=q1], blast, blast, blast, blast)
    apply (frule safe_sucD(6)[where q=q2], blast, blast, blast, blast)
    apply (clarsimp simp del: inf_apply)
    apply (subgoal_tac \<open>hl'a = hl'\<close>)
     prefer 2
     apply presburger
    apply (erule lopstep_act_cases)
     apply (clarsimp simp del: inf_apply)
     apply (meson Cons.hyps; fail)
    apply (clarsimp simp del: inf_apply)
    apply (drule(1) Cons.hyps, metis)
    apply blast
    done
qed force

lemma safe_conj:
  \<open>safe n c hl hs q1 F1 \<Longrightarrow>
    safe n c hl hs q2 F2 \<Longrightarrow>
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
  shows \<open>safe as c hl hs q \<top>\<close>
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
    using safe_indet[of as c1 hl hs q \<top> c2]
    by (meson safe_guarantee_mono safe_postpred_mono)
next
  case (rgsat_endet c1 r g1 p q1 c2 g2 q2 g q)
  then show ?case
    using safe_endet[of as c1 hl hs q \<top> c2]
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
