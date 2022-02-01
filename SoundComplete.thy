theory SoundComplete
  imports System1 System2
begin

lemma csl2_network_soundness:
  assumes invariant_sepconj_distrib_conj:
    \<open>\<And>i. i < length I \<Longrightarrow>
      (\<forall>P Q::'a varenv \<times> heap \<times> resources \<Rightarrow> bool. I ! i \<^emph> (P \<^bold>\<and> Q)  = (I ! i \<^emph> P) \<^bold>\<and> (I ! i \<^emph> Q))\<close>
    and new_conditions:
    \<open>\<forall>(l,cr,l')\<in>T. case cr of
        CRam cr' \<Rightarrow> ram_comm_forward cr' (G l) \<le> G l'
      | CAcquire r \<Rightarrow> r < length I \<and> altsepconj (I ! r) (G l) \<le> G l'
      | CRelease r \<Rightarrow> r < length I \<and> G l \<le> altsepconj (I ! r) (G l')
      \<close>
  shows \<open>
    (\<forall>(l,cr,l')\<in>T. case cr of
      CRam cr' \<Rightarrow> ram_comm_forward cr' (G l) \<le> G l'
    | CAcquire r \<Rightarrow> r < length I \<and> I ! r \<^emph> G l \<le> G l'
    | CRelease r \<Rightarrow> r < length I \<and> G l \<le> I ! r \<^emph> G l'
    )\<close>
  using new_conditions
    invariant_sepconj_distrib_conj[
      THEN sepconj_distrib_conj_imp_sepconj_eq_strong_sepcoimp, where Q=\<open>G l\<close> for l]
  apply -
  apply clarsimp
  apply (rename_tac l1 cr l2)
  apply (drule bspec, blast)
  apply clarsimp
  apply (case_tac cr; simp add: altsepconj_def)
  done

lemma csl2_network_completeness:
  assumes invariant_sepconj_distrib_conj:
    \<open>\<And>i. i < length I \<Longrightarrow>
      (\<forall>P Q::'a varenv \<times> heap \<times> resources \<Rightarrow> bool. I ! i \<^emph> (P \<^bold>\<and> Q)  = (I ! i \<^emph> P) \<^bold>\<and> (I ! i \<^emph> Q))\<close>
    and old_conditions:
    \<open>\<forall>(l,c',l')\<in>T. case c' of
      CRam cr' \<Rightarrow> ram_comm_forward cr' (G l) \<le> G l'
    | CAcquire r \<Rightarrow> r < length I \<and> I ! r \<^emph> G l \<le> G l'
    | CRelease r \<Rightarrow> r < length I \<and> G l \<le> I ! r \<^emph> G l'
    \<close>
  shows
    \<open>\<forall>(l,c',l')\<in>T. case c' of
       CRam cr' \<Rightarrow> ram_comm_forward cr' (G l) \<le> G l'
     | CAcquire r \<Rightarrow> r < length I \<and> altsepconj (I ! r) (G l) \<le> G l'
     | CRelease r \<Rightarrow> r < length I \<and> G l \<le> altsepconj (I ! r) (G l')
     \<close>
  using old_conditions
    invariant_sepconj_distrib_conj[
      THEN sepconj_distrib_conj_imp_sepconj_eq_strong_sepcoimp, where Q=\<open>G l\<close> for l]
  apply -
  apply clarsimp
  apply (rename_tac l1 cr l2)
  apply (drule bspec, blast)
  apply clarsimp
  apply (case_tac cr; force simp add: altsepconj_def)
  done


lemma csl2_soundness:
  assumes invariant_sepconj_distrib_conj:
    \<open>\<And>i. i < length I \<Longrightarrow>
      (\<forall>P Q::'a varenv \<times> heap \<times> resources \<Rightarrow> bool. I ! i \<^emph> (P \<^bold>\<and> Q)  = (I ! i \<^emph> P) \<^bold>\<and> (I ! i \<^emph> Q))\<close>
    and new_triple: \<open>L, I 2\<turnstile>\<^sub>c \<lbrace> P \<rbrace> c \<lbrace> Q \<rbrace>\<close>
  shows \<open>L, I \<turnstile>\<^sub>c \<lbrace> P \<rbrace> c \<lbrace> Q \<rbrace>\<close>
proof -
  obtain G T s e
    where new_triple_facts:
      \<open>cfg c T s e\<close>
      \<open>L = transition_labels T\<close>
      \<open>(\<forall>(l, c', l')\<in>T.
           case c' of CRam cr' \<Rightarrow> ram_comm_forward cr' (G l) \<le> G l'
        | CAcquire r \<Rightarrow> r < length I \<and> altsepconj (I ! r) (G l) \<le> G l'
        | CRelease r \<Rightarrow> r < length I \<and> G l \<le> altsepconj (I ! r) (G l'))\<close>
      \<open>P = G s\<close>
      \<open>G e \<le> Q\<close>
    using new_triple
    by (clarsimp simp add: logic_prog2_def)
  moreover then have
    \<open>\<forall>(l, c', l')\<in>T.
       case c' of CRam cr' \<Rightarrow> ram_comm_forward cr' (G l) \<le> G l'
    | CAcquire r \<Rightarrow> r < length I \<and> I ! r \<^emph> G l \<le> G l'
    | CRelease r \<Rightarrow> r < length I \<and> G l \<le> I ! r \<^emph> G l'\<close>
    using csl2_network_soundness[where G=G and I=I and T=T] invariant_sepconj_distrib_conj
    by fastforce
  ultimately show ?thesis
    apply (clarsimp simp add: logic_prog_def)
    apply (rule_tac x=G in exI, rule_tac x=T in exI)
    apply (fastforce simp add: split_def)
    done
qed

lemma csl2_completeness:
  assumes invariant_sepconj_distrib_conj:
    \<open>\<And>i. i < length I \<Longrightarrow>
      (\<forall>P Q::'a varenv \<times> heap \<times> resources \<Rightarrow> bool. I ! i \<^emph> (P \<^bold>\<and> Q)  = (I ! i \<^emph> P) \<^bold>\<and> (I ! i \<^emph> Q))\<close>
    and old_triple: \<open>L, I \<turnstile>\<^sub>c \<lbrace> P \<rbrace> c \<lbrace> Q \<rbrace>\<close>
  shows \<open>L, I 2\<turnstile>\<^sub>c \<lbrace> P \<rbrace> c \<lbrace> Q \<rbrace>\<close>
proof -

  obtain G T s e
    where new_triple_facts:
      \<open>cfg c T s e\<close>
      \<open>L = transition_labels T\<close>
      \<open>(\<forall>(l, c', l')\<in>T.
           case c' of CRam cr' \<Rightarrow> ram_comm_forward cr' (G l) \<le> G l'
        | CAcquire r \<Rightarrow> r < length I \<and> I ! r \<^emph> G l \<le> G l'
        | CRelease r \<Rightarrow> r < length I \<and> G l \<le> I ! r \<^emph> G l')\<close>
      \<open>P = G s\<close>
      \<open>G e \<le> Q\<close>
    using old_triple
    by (clarsimp simp add: logic_prog_def)
  moreover then have
    \<open>\<forall>(l, c', l')\<in>T.
       case c' of CRam cr' \<Rightarrow> ram_comm_forward cr' (G l) \<le> G l'
    | CAcquire r \<Rightarrow> r < length I \<and> altsepconj (I ! r) (G l) \<le> G l'
    | CRelease r \<Rightarrow> r < length I \<and> G l \<le> altsepconj (I ! r) (G l')\<close>
    using csl2_network_completeness[where G=G and I=I and T=T] invariant_sepconj_distrib_conj
    by fastforce
  ultimately show ?thesis
    apply (clarsimp simp add: logic_prog2_def)
    apply (rule_tac x=G in exI, rule_tac x=T in exI)
    apply (fastforce simp add: split_def)
    done
qed

end