theory System1
  imports Lang
begin

section \<open>Hoare Logic (Original)\<close>

definition logic_prog ::
  \<open>'l set \<Rightarrow> ('v state \<Rightarrow> bool) list \<Rightarrow> ('v state \<Rightarrow> bool) \<Rightarrow> 'v comm \<Rightarrow> ('v state \<Rightarrow> bool) \<Rightarrow> bool\<close>
  (\<open>_, _ \<turnstile>\<^sub>c \<lbrace> _ \<rbrace> _ \<lbrace> _ \<rbrace>\<close> [80,80,80,80,80] 80)
  where
    \<open>L, I \<turnstile>\<^sub>c \<lbrace> P \<rbrace> c \<lbrace> Q \<rbrace> \<equiv> (
      \<exists>G T. \<exists>s e.
        cfg c T s e \<and>
        L = transition_labels T \<and>
        (\<forall>(l,c',l')\<in>T. case c' of
          CRam cr' \<Rightarrow> ram_comm_forward cr' (G l) \<le> G l'
        | CAcquire r \<Rightarrow> r < length I \<and> I ! r \<^emph> G l \<le> G l'
        | CRelease r \<Rightarrow> r < length I \<and> G l \<le> I ! r \<^emph> G l'
        ) \<and>
        P = G s \<and>
        G e \<le> Q
    )\<close>

lemma logic_prog_seq:
  assumes
    \<open>L1 \<inter> L2 = {}\<close>
    \<open>L1, I \<turnstile>\<^sub>c \<lbrace> P \<rbrace> c1 \<lbrace> Q \<rbrace>\<close>
    \<open>L2, I \<turnstile>\<^sub>c \<lbrace> Q \<rbrace> c2 \<lbrace> R \<rbrace>\<close>
  shows
    \<open>\<exists>L12. L1 \<subseteq> L12 \<and> L2 \<subseteq> L12 \<and> L12, I \<turnstile>\<^sub>c \<lbrace> P \<rbrace> c1 ;; c2 \<lbrace> R \<rbrace>\<close>
proof -
  obtain T1 T2 G1 G2 s1 e1 s2 e2
    where unfolded_triples:
      \<open>cfg c1 T1 s1 e1\<close>
      \<open>cfg c2 T2 s2 e2\<close>
      \<open>L1 = transition_labels T1\<close>
      \<open>L2 = transition_labels T2\<close>
      \<open>\<forall>x\<in>T1. case x of (l, CRam cr', l') \<Rightarrow> ram_comm_forward cr' (G1 l) \<le> G1 l'
              | (l, CAcquire r, l') \<Rightarrow> r < length I \<and> I ! r \<^emph> G1 l \<le> G1 l'
              | (l, CRelease r, l') \<Rightarrow> r < length I \<and> G1 l \<le> I ! r \<^emph> G1 l'\<close>
      \<open>\<forall>x\<in>T2.
          case x of (l, CRam cr', l') \<Rightarrow> ram_comm_forward cr' (G2 l) \<le> G2 l'
          | (l, CAcquire r, l') \<Rightarrow> r < length I \<and> I ! r \<^emph> G2 l \<le> G2 l'
          | (l, CRelease r, l') \<Rightarrow> r < length I \<and> G2 l \<le> I ! r \<^emph> G2 l'\<close>
      \<open>G1 e1 \<le> G2 s2\<close>
      \<open>P = G1 s1\<close>
      \<open>G2 e2 \<le> R\<close>
      \<open>Q = G2 s2\<close>
    using assms
    by (clarsimp simp add: logic_prog_def)

  have T2_separate_T1:
    \<open>\<And>l. l \<in> transition_labels T2 \<Longrightarrow> l \<notin> transition_labels T1\<close>
    using assms unfolded_triples by auto

  show ?thesis
    using unfolded_triples T2_separate_T1
    apply (clarsimp simp add: logic_prog_def cfg_simps)
    apply (rule exI[where x=\<open>transition_labels (insert (e1, CRam CSkip, s2) (T1 \<union> T2))\<close>], clarsimp)
    apply (rule conjI, blast)
    apply (rule conjI, blast)

    apply (rule_tac x=\<open>\<lambda>l. if l \<in> transition_labels T1 then G1 l else G2 l\<close> in exI)
    apply (rule_tac x=\<open>insert (e1, CRam CSkip, s2) (T1 \<union> T2)\<close> in exI)
    apply (rule_tac x=s1 in exI)
    apply (rule_tac x=e2 in exI)
    apply (simp add: cfg_transition_labels_include_start cfg_transition_labels_include_end ram_comm_forward_simps)
    apply (intro conjI impI)
     apply blast
    apply (clarsimp, force dest: transition_labels_include_startend)
    done
qed

lemma logic_prog_ndet:
  assumes
    \<open>L1 \<inter> L2 = {}\<close>
    \<open>s \<notin> L1\<close> \<open>s \<notin> L2\<close>
    \<open>e \<notin> L1\<close> \<open>e \<notin> L2\<close>
    \<open>s \<noteq> e\<close>
    \<open>L1, I \<turnstile>\<^sub>c \<lbrace> P1 \<rbrace> c1 \<lbrace> Q1 \<rbrace>\<close>
    \<open>L2, I \<turnstile>\<^sub>c \<lbrace> P2 \<rbrace> c2 \<lbrace> Q2 \<rbrace>\<close>
  shows
    \<open>\<exists>L12. L1 \<subseteq> L12 \<and> L2 \<subseteq> L12 \<and> L12, I \<turnstile>\<^sub>c \<lbrace> P1 \<^bold>\<and> P2 \<rbrace> c1 \<box> c2 \<lbrace> Q1 \<^bold>\<or> Q2 \<rbrace>\<close>
proof -
  obtain T1 T2 G1 G2 s1 e1 s2 e2
    where unfolded_triples:
      \<open>cfg c1 T1 s1 e1\<close>
      \<open>cfg c2 T2 s2 e2\<close>
      \<open>L1 = transition_labels T1\<close>
      \<open>L2 = transition_labels T2\<close>
      \<open>\<forall>x\<in>T1. case x of (l, CRam cr', l') \<Rightarrow> ram_comm_forward cr' (G1 l) \<le> G1 l'
              | (l, CAcquire r, l') \<Rightarrow> r < length I \<and> I ! r \<^emph> G1 l \<le> G1 l'
              | (l, CRelease r, l') \<Rightarrow> r < length I \<and> G1 l \<le> I ! r \<^emph> G1 l'\<close>
      \<open>\<forall>x\<in>T2.
          case x of (l, CRam cr', l') \<Rightarrow> ram_comm_forward cr' (G2 l) \<le> G2 l'
          | (l, CAcquire r, l') \<Rightarrow> r < length I \<and> I ! r \<^emph> G2 l \<le> G2 l'
          | (l, CRelease r, l') \<Rightarrow> r < length I \<and> G2 l \<le> I ! r \<^emph> G2 l'\<close>
      \<open>G1 e1 \<le> Q1\<close>
      \<open>P1 = G1 s1\<close>
      \<open>G2 e2 \<le> Q2\<close>
      \<open>P2 = G2 s2\<close>
    using assms
    by (clarsimp simp add: logic_prog_def)

  let ?T = \<open>insert (s, CRam CSkip, s1) (insert (s, CRam CSkip, s2)
           (insert (e1, CRam CSkip, e) (insert (e2, CRam CSkip, e) (T1 \<union> T2))))\<close>
  let ?G = \<open>\<lambda>l. if l = s then P1 \<^bold>\<and> P2
                else if l = e then Q1 \<^bold>\<or> Q2
                else if l \<in> transition_labels T1 then G1 l
                else G2 l\<close>

  have transition_labels_not_in:
    \<open>e1 \<in> transition_labels T1\<close>
    \<open>e2 \<in> transition_labels T2\<close>
    \<open>s1 \<in> transition_labels T1\<close>
    \<open>s2 \<in> transition_labels T2\<close>
    \<open>s \<notin> transition_labels T1\<close>
    \<open>s \<notin> transition_labels T2\<close>
    \<open>e \<notin> transition_labels T1\<close>
    \<open>e \<notin> transition_labels T2\<close>
    using assms unfolded_triples
    by (force dest: cfg_transition_labels_include_start cfg_transition_labels_include_end
        simp add: disjoint_iff)+

  have transition_labels_not_in_general:
    \<open>\<And>l. l \<in> transition_labels T1 \<Longrightarrow> l \<notin> transition_labels T2\<close>
    \<open>\<And>l. l \<in> transition_labels T2 \<Longrightarrow> l \<notin> transition_labels T1\<close>
    using assms unfolded_triples by blast+

  have transition_labels_not_eq:
    \<open>\<And>l. l \<in> transition_labels T1 \<Longrightarrow> l \<noteq> s\<close> \<open>\<And>l. l \<in> transition_labels T2 \<Longrightarrow> l \<noteq> s\<close>
    \<open>\<And>l. l \<in> transition_labels T1 \<Longrightarrow> l \<noteq> e\<close> \<open>\<And>l. l \<in> transition_labels T2 \<Longrightarrow> l \<noteq> e\<close>
    \<open>e \<noteq> s\<close>
    using assms transition_labels_not_in by force+

  show ?thesis
    using unfolded_triples
    apply (clarsimp simp add: logic_prog_def cfg_simps)
    apply (rule exI[where x=\<open>transition_labels ?T\<close>], simp)
    apply (rule conjI, blast)
    apply (rule conjI, blast)

    apply (rule_tac x=\<open>?G\<close> in exI)
    apply (rule_tac x=\<open>?T\<close> in exI)
    apply (rule_tac x=s in exI)
    apply (rule_tac x=e in exI)
    apply (simp only: assms HOL.simp_thms)
    apply (intro conjI)
        apply (rule_tac x=T1 in exI)
        apply (rule_tac x=T2 in exI)
        apply (metis assms(1-5) unfolded_triples(1-4))
       apply simp

    apply (intro conjI ballI)

      apply (simp add: transition_labels_not_in ram_comm_forward_simps)
      apply (elim disjE; force simp add:
        transition_labels_include_startend transition_labels_not_in
        transition_labels_not_eq transition_labels_not_in_general
        ram_comm_forward_simps pred_conj_def pred_disj_def)

     apply force
    apply (force simp add: transition_labels_not_eq)
    done
qed

lemma logic_prog_conj:
  assumes
    \<open>L1, I \<turnstile>\<^sub>c \<lbrace> P1 \<rbrace> c \<lbrace> Q1 \<rbrace>\<close>
    \<open>L2, I \<turnstile>\<^sub>c \<lbrace> P2 \<rbrace> c \<lbrace> Q2 \<rbrace>\<close>
    \<open>L1 \<inter> L2 = {}\<close>
  and invariant_precision:
    \<open>\<And>i P Q. i < length I \<Longrightarrow> I ! i \<^emph> (P \<^bold>\<and> Q) = (I ! i \<^emph> P) \<^bold>\<and> (I ! i \<^emph> Q)\<close>
  shows
    \<open>L1, I \<turnstile>\<^sub>c \<lbrace> P1 \<^bold>\<and> P2 \<rbrace> c \<lbrace> Q1 \<^bold>\<and> Q2 \<rbrace>\<close>
proof -
  obtain G1 G2 T1 T2 s1 s2 e1 e2
    where unfolded_triples:
      \<open>transition_labels T1 \<inter> transition_labels T2 = {}\<close>
      \<open>cfg c T1 s1 e1\<close>
      \<open>cfg c T2 s2 e2\<close>
      \<open>L1 = transition_labels T1\<close>
      \<open>L2 = transition_labels T2\<close>
      \<open>\<forall>x\<in>T1. case x of
          (l, CRam cr', l') \<Rightarrow> ram_comm_forward cr' (G1 l) \<le> G1 l'
        | (l, CAcquire r, l') \<Rightarrow> r < length I \<and> I ! r \<^emph> G1 l \<le> G1 l'
        | (l, CRelease r, l') \<Rightarrow> r < length I \<and> G1 l \<le> I ! r \<^emph> G1 l'\<close>
      \<open>\<forall>x\<in>T2. case x of
          (l, CRam cr', l') \<Rightarrow> ram_comm_forward cr' (G2 l) \<le> G2 l'
        | (l, CAcquire r, l') \<Rightarrow> r < length I \<and> I ! r \<^emph> G2 l \<le> G2 l'
        | (l, CRelease r, l') \<Rightarrow> r < length I \<and> G2 l \<le> I ! r \<^emph> G2 l'\<close>
      \<open>G1 e1 \<le> Q1\<close>
      \<open>P1 = G1 s1\<close>
      \<open>G2 e2 \<le> Q2\<close>
      \<open>P2 = G2 s2\<close>
    using assms
    by (clarsimp simp add: logic_prog_def cfg_simps)

  obtain f
    where cfg_isomorphism:
    \<open>bij_betw (\<lambda>(la, c, lb). (f la, c, f lb)) T1 T2\<close>
    \<open>bij_betw f (transition_labels T1) (transition_labels T2)\<close>
    \<open>f s1 = s2\<close>
    \<open>f e1 = e2\<close>
    using unfolded_triples(2-3)
    by (force simp add: cfg_iso_def dest: cfg_same_label_bij)

  show ?thesis
    using unfolded_triples cfg_isomorphism
    apply (clarsimp simp add: logic_prog_def cfg_simps)
    apply (rule_tac x=\<open>\<lambda>l. G1 l \<^bold>\<and> G2 (f l)\<close> in exI)
    apply (rule_tac x=T1 in exI)
    apply (rule_tac x=s1 in exI)
    apply (rule_tac x=e1 in exI)
    apply (intro conjI)
        apply simp
       apply simp
      apply (intro ballI impI)
      apply (drule bspec)
       apply blast
      apply clarsimp
      apply (rename_tac lx cc ly)
      apply (drule_tac x=\<open>(f lx, cc, f ly)\<close> in bspec)
       apply (force dest: bij_betwE)
      apply (clarsimp split: comm.splits)
        apply (force simp add: pred_conj_simp dest!: predicate1D[OF ram_comm_forward_conj])
      (* Here is the first application of precision *)
       apply (subst (asm) invariant_precision, blast)
       apply (force simp add: pred_conj_simp)
      (* and the second is here *)
      apply (subst invariant_precision, blast)
      apply (force simp add: pred_conj_simp)
     apply blast
    apply (simp add: le_fun_def pred_conj_simp)
    done
qed


lemma logic_prog_disj:
  assumes
    \<open>L1, I \<turnstile>\<^sub>c \<lbrace> P1 \<rbrace> c \<lbrace> Q1 \<rbrace>\<close>
    \<open>L2, I \<turnstile>\<^sub>c \<lbrace> P2 \<rbrace> c \<lbrace> Q2 \<rbrace>\<close>
    \<open>L1 \<inter> L2 = {}\<close>
  shows
    \<open>L1, I \<turnstile>\<^sub>c \<lbrace> P1 \<^bold>\<or> P2 \<rbrace> c \<lbrace> Q1 \<^bold>\<or> Q2 \<rbrace>\<close>
proof -

  obtain G1 G2 T1 T2 s1 s2 e1 e2
    where unfolded_triples:
      \<open>transition_labels T1 \<inter> transition_labels T2 = {}\<close>
      \<open>cfg c T1 s1 e1\<close>
      \<open>cfg c T2 s2 e2\<close>
      \<open>L1 = transition_labels T1\<close>
      \<open>L2 = transition_labels T2\<close>
      \<open>\<forall>x\<in>T1. case x of
          (l, CRam cr', l') \<Rightarrow> ram_comm_forward cr' (G1 l) \<le> G1 l'
        | (l, CAcquire r, l') \<Rightarrow> r < length I \<and> I ! r \<^emph> G1 l \<le> G1 l'
        | (l, CRelease r, l') \<Rightarrow> r < length I \<and> G1 l \<le> I ! r \<^emph> G1 l'\<close>
      \<open>\<forall>x\<in>T2. case x of
          (l, CRam cr', l') \<Rightarrow> ram_comm_forward cr' (G2 l) \<le> G2 l'
        | (l, CAcquire r, l') \<Rightarrow> r < length I \<and> I ! r \<^emph> G2 l \<le> G2 l'
        | (l, CRelease r, l') \<Rightarrow> r < length I \<and> G2 l \<le> I ! r \<^emph> G2 l'\<close>
      \<open>G1 e1 \<le> Q1\<close>
      \<open>P1 = G1 s1\<close>
      \<open>G2 e2 \<le> Q2\<close>
      \<open>P2 = G2 s2\<close>
    using assms
    by (clarsimp simp add: logic_prog_def cfg_simps)

  obtain f
    where cfg_isomorphism:
    \<open>bij_betw (\<lambda>(la, c, lb). (f la, c, f lb)) T1 T2\<close>
    \<open>bij_betw f (transition_labels T1) (transition_labels T2)\<close>
    \<open>f s1 = s2\<close>
    \<open>f e1 = e2\<close>
    using unfolded_triples(2-3)
    by (force simp add: cfg_iso_def dest: cfg_same_label_bij)

  show ?thesis
    using unfolded_triples cfg_isomorphism
    apply (clarsimp simp add: logic_prog_def cfg_simps)
    apply (rule_tac x=\<open>\<lambda>l. G1 l \<^bold>\<or> G2 (f l)\<close> in exI)
    apply (rule_tac x=T1 in exI)
    apply (rule_tac x=s1 in exI)
    apply (rule_tac x=e1 in exI)
    apply (intro conjI)
        apply simp
       apply simp
      apply (intro ballI impI)
      apply (drule bspec)
       apply blast
      apply clarsimp
      apply (rename_tac lx cc ly)
      apply (drule_tac x=\<open>(f lx, cc, f ly)\<close> in bspec)
       apply (force dest: bij_betwE)
      apply (force simp add: ram_comm_forward_disj pred_disj_simp sepconj_pdisj_distrib_left
        split: comm.splits)
     apply force
    apply (force simp add: pred_disj_simp)
    done
qed


lemma logic_prog2_frame:
  assumes \<open>L, I \<turnstile>\<^sub>c \<lbrace> Q \<rbrace> c \<lbrace> R \<rbrace>\<close>
  and no_write_to_R: \<open>\<forall>s. R s \<longrightarrow> dom (the_varenv (fst s)) \<inter> c_write_vars c = {}\<close>
shows \<open>L, I \<turnstile>\<^sub>c \<lbrace> P \<^emph> Q \<rbrace> c \<lbrace> P \<^emph> R \<rbrace>\<close>
proof -
  obtain G T s e
    where unfolded_triples:
      \<open>cfg c T s e\<close>
      \<open>L = transition_labels T\<close>
      \<open>\<forall>x\<in>T. case x of
          (l, CRam cr', l') \<Rightarrow> ram_comm_forward cr' (G l) \<le> G l'
        | (l, CAcquire r, l') \<Rightarrow> r < length I \<and> I ! r \<^emph> G l \<le> G l'
        | (l, CRelease r, l') \<Rightarrow> r < length I \<and> G l \<le> I ! r \<^emph> G l'\<close>
      \<open>Q = G s\<close>
      \<open>G e \<le> R\<close>
    using assms
    by (force simp add: logic_prog_def)

  have 
    \<open>\<forall>x\<in>T. case x of
      (l, CRam cr', l') \<Rightarrow> ram_comm_forward cr' (P \<^emph> G l) \<le> P \<^emph> G l'
    | (l, CAcquire r, l') \<Rightarrow> r < length I \<and> I ! r \<^emph> P \<^emph> G l \<le> P \<^emph> G l'
    | (l, CRelease r, l') \<Rightarrow> r < length I \<and> P \<^emph> G l \<le> I ! r \<^emph> P \<^emph> G l'\<close>
    using unfolded_triples(3)
    apply clarsimp
    apply (rename_tac l1 cr l2)
    apply (drule_tac x=\<open>(l1,cr,l2)\<close> in bspec, assumption)
    apply (case_tac cr; clarsimp)
      apply (rename_tac cr' v h r)
      defer
      apply (force dest: predicate1D[OF sepconj_middle_monotone_left])
     apply (force dest: predicate1D[OF sepconj_middle_monotone_right])
    sorry
  then show ?thesis
    using unfolded_triples
    apply (simp add: logic_prog_def)
    apply (rule_tac x=\<open>\<lambda>l. P \<^emph> G l\<close> in exI)
    apply (rule_tac x=T in exI)
    apply (rule_tac x=s in exI)
    apply (rule_tac x=e in exI)
    apply (simp add: sepconj_right_mono)
    sorry
qed


end