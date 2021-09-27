theory SepLogic
  imports Main
begin


definition pred_false :: \<open>'a \<Rightarrow> bool\<close> (\<open>\<^bold>F\<close>) where
  \<open>\<^bold>F \<equiv> \<lambda>x. False\<close>

definition pred_true :: \<open>'a \<Rightarrow> bool\<close> (\<open>\<^bold>T\<close>) where
  \<open>\<^bold>T \<equiv> \<lambda>x. True\<close>

definition pred_neg :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> (\<open>\<^bold>\<not> _\<close> [89] 90) where
  \<open>\<^bold>\<not> p \<equiv> \<lambda>x. \<not> p x\<close>

definition pred_conj :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> (infixl \<open>\<^bold>\<and>\<close> 86) where
  \<open>p \<^bold>\<and> q \<equiv> \<lambda>x. p x \<and> q x\<close>

definition pred_disj :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> (infixl \<open>\<^bold>\<or>\<close> 84) where
  \<open>p \<^bold>\<or> q \<equiv> \<lambda>x. p x \<or> q x\<close>

definition pred_impl :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> (infixr \<open>\<^bold>\<longrightarrow>\<close> 82) where
  \<open>p \<^bold>\<longrightarrow> q \<equiv> \<lambda>x. p x \<longrightarrow> q x\<close>


class seplogic = plus + zero + order_bot +
  fixes disjoint :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (infix \<open>\<currency>\<close> 70)
  assumes disjoint_nonrefl: \<open>a \<noteq> 0 \<Longrightarrow> a \<currency> a = False\<close>
  assumes disjoint_symm: \<open>a \<currency> b = b \<currency> a\<close>
  assumes disjoint_empty[simp]: \<open>0 \<currency> a\<close>
  assumes le_iff_sepadd: \<open>a \<le> b \<longleftrightarrow> (\<exists>c. a \<currency> c \<and> b = a + c)\<close>
  (* partial commutative monoid *)
  assumes partial_add_assoc:
    "a \<currency> b \<Longrightarrow> b \<currency> c \<Longrightarrow> a \<currency> c \<Longrightarrow> (a + b) + c = a + (b + c)"
  assumes partial_add_commute: \<open>a \<currency> b \<Longrightarrow> a + b = b + a\<close>
  assumes partial_add_0[simp]: "0 + a = a"
begin

lemma disjoint_empty_right[simp]: \<open>h \<currency> 0\<close>
  using disjoint_symm by fastforce

lemma sep_add_0_right[simp]: "a + 0 = a"
  by (metis disjoint_empty partial_add_0 partial_add_commute)

lemma zero_le: \<open>0 \<le> h\<close>
  by (simp add: le_iff_sepadd)

lemma bot_eq_zero: \<open>bot = 0\<close>
  by (simp add: antisym zero_le)

definition sepconj :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> (infix \<open>\<star>\<close> 88) where
  \<open>P \<star> Q \<equiv> \<lambda>h. \<exists>h1 h2. h1 \<currency> h2 \<and> h = h1 + h2 \<and> P h1 \<and> Q h2\<close>

definition sepimp :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> (infixr \<open>\<midarrow>\<star>\<close> 86) where
  \<open>P \<midarrow>\<star> Q \<equiv> \<lambda>h. \<forall>h1. h \<currency> h1 \<longrightarrow> P h1 \<longrightarrow> Q (h + h1)\<close>

definition sepcoimp :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> (infixr \<open>\<sim>\<star>\<close> 86) where
  \<open>P \<sim>\<star> Q \<equiv> \<lambda>h. \<forall>h1 h2. h1 \<currency> h2 \<longrightarrow> h = h1 + h2 \<longrightarrow> P h1 \<longrightarrow> Q h2\<close>

definition septract :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> (infixr \<open>\<midarrow>\<odot>\<close> 86) where
  \<open>P \<midarrow>\<odot> Q \<equiv> \<lambda>h. \<exists>h1. h \<currency> h1 \<and> P h1 \<and> Q (h + h1)\<close>

definition septract_rev :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> (infixr \<open>\<odot>\<midarrow>\<close> 86) where
  \<open>P \<odot>\<midarrow> Q \<equiv> \<lambda>h. \<exists>h'. h \<currency> h' \<and> P (h + h') \<and> Q h'\<close>

lemma septract_reverse: \<open>P \<midarrow>\<odot> Q = Q \<odot>\<midarrow> P\<close>
  by (force simp add: septract_def septract_rev_def)

lemma sepconj_comm: \<open>P \<star> Q = Q \<star> P\<close>
  unfolding sepconj_def
  by (metis disjoint_symm partial_add_commute)


lemma septract_sepimp_dual: \<open>P \<midarrow>\<odot> Q = \<^bold>\<not>(P \<midarrow>\<star> \<^bold>\<not> Q)\<close>
  unfolding septract_def sepimp_def pred_neg_def
  by blast

lemma sepimp_sepcoimp_dual: \<open>P \<sim>\<star> Q = \<^bold>\<not>(P \<star> \<^bold>\<not> Q)\<close>
  unfolding sepconj_def sepcoimp_def pred_neg_def
  by blast

lemma sepconj_sepimp_galois: \<open>P \<star> Q \<le> R \<longleftrightarrow> P \<le> Q \<midarrow>\<star> R\<close>
  using sepconj_def sepimp_def by fastforce

lemma sepcoimp_septract_galois: \<open>P \<odot>\<midarrow> Q \<le> R \<longleftrightarrow> P \<le> Q \<sim>\<star> R\<close>
  unfolding sepcoimp_def septract_rev_def le_fun_def
  using disjoint_symm partial_add_commute by fastforce


definition emp :: \<open>'a \<Rightarrow> bool\<close> where
  \<open>emp \<equiv> (\<lambda>h. h = 0)\<close>

lemma emp_sepconj_unit: \<open>emp \<star> P = P\<close>
  by (simp add: emp_def sepconj_def)


definition precise :: \<open>('a \<Rightarrow> bool) \<Rightarrow> bool\<close> where
  \<open>precise P \<equiv> \<forall>h h1. h1\<le>h \<longrightarrow> P h1 \<longrightarrow> (\<forall>h2\<le>h. P h2 \<longrightarrow> h1 = h2)\<close>

lemma precise_iff_conj_distrib:
  assumes sepalg_add_right_cancel: \<open>\<And>a b c. (b + a = c + a) = (b = c)\<close>
  shows \<open>precise P \<longleftrightarrow> (\<forall>Q Q'. (Q \<^bold>\<and> Q') \<star> P = (Q \<star> P) \<^bold>\<and> (Q' \<star> P))\<close>
proof (rule iffI)
  assume distrib_assm: \<open>\<forall>Q Q'. (Q \<^bold>\<and> Q') \<star> P = (Q \<star> P) \<^bold>\<and> (Q' \<star> P)\<close>
  show \<open>precise P\<close>
  proof (clarsimp simp add: precise_def le_iff_sepadd)
    fix h1 h1' h2 h2'
    presume precise_assms:
      \<open>h1 + h1' = h2 + h2'\<close>
      \<open>h1 \<currency> h1'\<close>
      \<open>h2 \<currency> h2'\<close>
      \<open>P h1\<close>
      \<open>P h2\<close>

    have \<open>(((=) h1') \<star> P) (h2+h2')\<close>
      using precise_assms partial_add_commute disjoint_symm sepconj_def
      by auto
    moreover have \<open>(((=) h2') \<star> P) (h2+h2')\<close>
      using precise_assms partial_add_commute disjoint_symm sepconj_def
      by auto
    ultimately have \<open>((\<lambda>h. h1' = h \<and> h2' = h) \<star> P) (h2+h2')\<close>
      using distrib_assm precise_assms
      by (simp add: pred_conj_def)
    then show \<open>h1 = h2\<close>
      using precise_assms
      by (clarsimp simp add: sepconj_def precise_assms, metis sepalg_add_right_cancel)
  qed
next
  presume precise_assm:  \<open>precise P\<close>
  then show \<open>\<forall>Q Q'. (Q \<^bold>\<and> Q') \<star> P = (Q \<star> P) \<^bold>\<and> (Q' \<star> P)\<close>
    apply (auto simp add: sepconj_def precise_def pred_conj_def fun_eq_iff le_iff_sepadd)
    apply (metis partial_add_commute disjoint_symm sepalg_add_right_cancel)
    done
qed


lemma precise_iff_all_sepconj_imp_sepcoimp:
  assumes sepalg_add_right_cancel: \<open>\<And>a b c. (b + a = c + a) = (b = c)\<close>
  shows \<open>precise P \<longleftrightarrow> (\<forall>Q. P \<star> Q \<le> P \<sim>\<star> Q)\<close>
  apply (clarsimp simp add: sepconj_def sepcoimp_def precise_def le_fun_def le_iff_sepadd)
  apply (rule iffI)
   apply (metis sepalg_add_right_cancel partial_add_commute)
  apply (metis sepalg_add_right_cancel antisym order.refl)
  done

lemma secoimp_imp_sepconj:
  \<open>P \<^bold>\<and> (P \<sim>\<star> Q) \<le> P \<star> Q\<close>
  unfolding pred_conj_def sepcoimp_def sepconj_def le_fun_def le_bool_def
  by (metis disjoint_empty_right sep_add_0_right)

lemma sepcoimp_conj_distrib_left:
  \<open>P \<sim>\<star> (Q \<^bold>\<and> Q') = (P \<sim>\<star> Q) \<^bold>\<and> (P \<sim>\<star> Q')\<close>
  by (force simp add: pred_conj_def sepcoimp_def)

lemma not_coimp_emp:
  \<open>h \<noteq> 0 \<Longrightarrow> (\<^bold>\<not> (\<^bold>T \<sim>\<star> emp)) h\<close>
  apply (clarsimp simp add: pred_true_def pred_neg_def sepcoimp_def emp_def)
  apply (rule_tac x=0 in exI, force)
  done

end


section \<open> Concurrent Separation Logic \<close>

(* Based on
    Precision and the Conjunction Rule in Concurrent Separation Logic
    Alexey Gotsman, Josh Berdine, Byron Cook
*)

datatype 'v iexpr =
  IEVar 'v
  | IELit nat
  | IEAdd \<open>'v iexpr\<close> \<open>'v iexpr\<close>
  | IENull

datatype 'v bexpr =
  IBEq \<open>'v iexpr\<close> \<open>'v iexpr\<close>
  | IBNeg \<open>'v bexpr\<close>

datatype 'v ram_comm =
  CSkip
  | CAssign 'v  \<open>'v iexpr\<close>
  | CHeapR 'v  \<open>'v iexpr\<close>
  | CHeapW  \<open>'v iexpr\<close>  \<open>'v iexpr\<close>
  | CHeapNew 'v
  | CHeapDel \<open>'v iexpr\<close>
  | CAssume \<open>'v bexpr\<close>


datatype 'v comm =
  CRam \<open>'v ram_comm\<close>
  | CSeq \<open>'v comm\<close> \<open>'v comm\<close> (infixr \<open>;;\<close> 84)
  | CNDet \<open>'v comm\<close> \<open>'v comm\<close> (infixr \<open>\<sqinter>\<close> 86)
  | CLoop \<open>'v comm\<close> (\<open>(_)\<^sup>\<star>\<close> 88)
  | CAcquire nat
  | CRelease nat

type_synonym ('v,'r) prog = \<open>'v comm list\<close>

datatype 'v varenv = VarEnv (the_varenv: \<open>'v \<rightharpoonup> nat\<close>)
datatype heap = Heap (the_heap: \<open>nat \<rightharpoonup> nat\<close>)
datatype resources = Resources (the_resources: \<open>nat set\<close>)

lemma the_varenv_eq_iff:
  \<open>the_varenv a = b \<longleftrightarrow> a = VarEnv b\<close>
  by fastforce
lemma the_heap_eq_iff:
  \<open>the_heap a = b \<longleftrightarrow> a = Heap b\<close>
  by fastforce
lemma the_resources_eq_iff:
  \<open>the_resources a = b \<longleftrightarrow> a = Resources b\<close>
  by fastforce

type_synonym 'v state = \<open>'v varenv \<times> heap \<times> resources\<close>

fun denot_iexpr :: \<open>'v iexpr \<Rightarrow> (('v \<rightharpoonup> nat) \<rightharpoonup> nat)\<close> (\<open>(\<lbrakk>_\<rbrakk>\<^sub>I) _\<close> [80,80] 80) where
  \<open>\<lbrakk> IEVar x \<rbrakk>\<^sub>I \<sigma> = \<sigma> x\<close>
| \<open>\<lbrakk> IELit k \<rbrakk>\<^sub>I \<sigma> = Some k\<close>
| \<open>\<lbrakk> IEAdd a b \<rbrakk>\<^sub>I \<sigma> =
    (case (\<lbrakk>a\<rbrakk>\<^sub>I \<sigma>, \<lbrakk>b\<rbrakk>\<^sub>I \<sigma>) of
      (Some a, Some b) \<Rightarrow> Some (a + b)
    | _ \<Rightarrow> None
    )
  \<close>
| \<open>\<lbrakk> IENull \<rbrakk>\<^sub>I \<sigma> = None\<close> (* TODO: is this correct? *)

fun denot_bexpr :: \<open>'v bexpr \<Rightarrow> (('v \<rightharpoonup> nat) \<rightharpoonup> bool)\<close> (\<open>(\<lbrakk>_\<rbrakk>\<^sub>B) _\<close> [80,80] 80) where
  \<open>\<lbrakk> IBEq a b \<rbrakk>\<^sub>B \<sigma> =
    (case (\<lbrakk>a\<rbrakk>\<^sub>I \<sigma>, \<lbrakk>b\<rbrakk>\<^sub>I \<sigma>) of
      (Some a, Some b) \<Rightarrow> Some (a = b)
    | _ \<Rightarrow> None
    )
  \<close>
| \<open>\<lbrakk> IBNeg b \<rbrakk>\<^sub>B \<sigma> = map_option HOL.Not (\<lbrakk> b \<rbrakk>\<^sub>B \<sigma>)\<close>

inductive opsem_ram_comm :: \<open>'v state \<Rightarrow> 'v ram_comm \<Rightarrow> 'v state option \<Rightarrow> bool\<close> (\<open>_, _ \<leadsto> _\<close> [80,80,80] 80) where
  \<open>s, CSkip \<leadsto> Some s\<close>
| \<open>(VarEnv s, h, r), CAssign x e \<leadsto> Some (VarEnv (s(x := \<lbrakk>e\<rbrakk>\<^sub>I s)), h, r)\<close>
| \<open>\<lbrakk>ep\<rbrakk>\<^sub>I s = Some p \<Longrightarrow> (VarEnv s, h, r), CHeapR x ep \<leadsto> Some (VarEnv (s(x := the_heap h p)), h, r)\<close>
| \<open>\<lbrakk>ep\<rbrakk>\<^sub>I s = None   \<Longrightarrow> (VarEnv s, h, r), CHeapR x ep \<leadsto> None\<close>
| \<open>\<lbrakk>ep\<rbrakk>\<^sub>I s = Some p \<Longrightarrow> (VarEnv s, Heap h, r), CHeapW ep e \<leadsto> Some (VarEnv s, Heap (h(p := \<lbrakk>e\<rbrakk>\<^sub>I s)), r)\<close>
| \<open>\<lbrakk>ep\<rbrakk>\<^sub>I s = None   \<Longrightarrow> (VarEnv s, h, r), CHeapW ep e \<leadsto> None\<close>
| \<open>h p = None \<Longrightarrow> (VarEnv s, Heap h, r), CHeapNew x \<leadsto> Some (VarEnv (s(x \<mapsto> p)), Heap (h(p \<mapsto> undefined)), r)\<close>
| \<open>h p \<noteq> None \<Longrightarrow> (VarEnv s, Heap h, r), CHeapNew x \<leadsto> None\<close>
| \<open>\<lbrakk>e\<rbrakk>\<^sub>I s = Some p \<Longrightarrow> h p \<noteq> None \<Longrightarrow> (VarEnv s, Heap h, r), CHeapDel e \<leadsto> Some (VarEnv s, Heap (h(p := None)), r)\<close>
| \<open>\<lbrakk>e\<rbrakk>\<^sub>I s = None \<Longrightarrow> (VarEnv s, h, r), CHeapDel e \<leadsto> None\<close>
| \<open>\<lbrakk>e\<rbrakk>\<^sub>I s = Some p \<Longrightarrow> h p = None \<Longrightarrow> (VarEnv s, Heap h, r), CHeapDel e \<leadsto> None\<close>
| \<open>\<lbrakk>b\<rbrakk>\<^sub>B s = Some True \<Longrightarrow> (VarEnv s, h, r), CAssume b \<leadsto> Some (VarEnv s, h, r)\<close>


lemma map_le_restrict_eq: \<open>ma \<subseteq>\<^sub>m mb \<Longrightarrow> mb |` dom ma = ma\<close>
  by (rule ext, metis domIff map_le_def restrict_map_def)

lemma map_restrict_un_eq:
  \<open>m |` (A \<union> B) = m |` A ++ m |` B\<close>
  by (force simp add: restrict_map_def map_add_def split: option.splits)

lemma map_le_split:
  assumes \<open>ma \<subseteq>\<^sub>m mb\<close>
  shows \<open>mb = ma ++ mb |` (- dom ma)\<close>
  using assms
  by (subst map_le_restrict_eq[OF assms, symmetric], force simp add: map_restrict_un_eq[symmetric])


instantiation varenv :: (type) seplogic
begin
  definition
    \<open>disjoint_varenv a b \<equiv> dom (the_varenv a) \<inter> dom (the_varenv b) = {}\<close>
  definition
    \<open>bot_varenv \<equiv> VarEnv Map.empty\<close>
  definition
    \<open>zero_varenv \<equiv> VarEnv Map.empty\<close>
  definition
    \<open>plus_varenv a b \<equiv> VarEnv (the_varenv a ++ the_varenv b)\<close>
  definition
    \<open>less_eq_varenv a b \<equiv> the_varenv a \<subseteq>\<^sub>m the_varenv b\<close>
  definition
    \<open>less_varenv a b \<equiv> the_varenv a \<subseteq>\<^sub>m the_varenv b \<and> \<not> the_varenv b \<subseteq>\<^sub>m the_varenv a\<close>

instance
proof
  fix a b c :: \<open>'a varenv\<close>

  show \<open>(a < b) = (a \<le> b \<and> \<not> b \<le> a)\<close>
    by (simp add: less_varenv_def less_eq_varenv_def)
  show \<open>a \<le> a\<close>
    by (simp add: less_eq_varenv_def)
  show \<open>a \<le> b \<Longrightarrow> b \<le> c \<Longrightarrow> a \<le> c\<close>
    by (force intro: map_le_trans simp add: less_eq_varenv_def)
  show \<open>a \<le> b \<Longrightarrow> b \<le> a \<Longrightarrow> a = b\<close>
    by (simp add: varenv.expand less_eq_varenv_def prod_eq_iff map_le_antisym)
  show \<open>a \<currency> b \<Longrightarrow> b \<currency> c \<Longrightarrow> a \<currency> c \<Longrightarrow> a + b + c = a + (b + c)\<close>
    by (simp add: plus_varenv_def)
  show \<open>a \<currency> b \<Longrightarrow> a + b = b + a\<close>
    by (metis disjoint_varenv_def plus_varenv_def map_add_comm)
  show \<open>bot \<le> a\<close>
    by (clarsimp simp add: bot_varenv_def less_eq_varenv_def)
  show \<open>a \<noteq> 0 \<Longrightarrow> a \<currency> a = False\<close>
    by (simp add: disjoint_varenv_def zero_varenv_def the_varenv_eq_iff)
  show \<open>a \<currency> b = b \<currency> a\<close>
    by (force simp add: disjoint_varenv_def)
  show \<open>0 \<currency> a\<close>
    by (simp add: disjoint_varenv_def zero_varenv_def)

  have \<open>a \<le> b \<Longrightarrow>
    a \<currency> VarEnv (the_varenv b |` (- dom (the_varenv a))) \<and>
    b = a + VarEnv (the_varenv b |` (- dom (the_varenv a)))\<close>
    unfolding less_eq_varenv_def disjoint_varenv_def plus_varenv_def
    by (simp add: the_varenv_eq_iff[symmetric] map_le_split)
  then show \<open>(a \<le> b) = (\<exists>c. a \<currency> c \<and> b = a + c)\<close>
    unfolding less_eq_varenv_def disjoint_varenv_def plus_varenv_def
    by (fastforce simp add: map_add_comm)

  show \<open>0 + a = a\<close>
    by (simp add: plus_varenv_def zero_varenv_def)
qed

end

instantiation heap :: seplogic
begin
  definition
    \<open>disjoint_heap a b \<equiv> dom (the_heap a) \<inter> dom (the_heap b) = {}\<close>
  definition
    \<open>bot_heap \<equiv> Heap Map.empty\<close>
  definition
    \<open>zero_heap \<equiv> Heap Map.empty\<close>
  definition
    \<open>plus_heap a b \<equiv> Heap (the_heap a ++ the_heap b)\<close>
  definition
    \<open>less_eq_heap a b \<equiv> the_heap a \<subseteq>\<^sub>m the_heap b\<close>
  definition
    \<open>less_heap a b \<equiv> the_heap a \<subseteq>\<^sub>m the_heap b \<and> \<not> the_heap b \<subseteq>\<^sub>m the_heap a\<close>

instance
proof
  fix a b c :: heap

  show \<open>(a < b) = (a \<le> b \<and> \<not> b \<le> a)\<close>
    by (simp add: less_heap_def less_eq_heap_def)
  show \<open>a \<le> a\<close>
    by (simp add: less_eq_heap_def)
  show \<open>a \<le> b \<Longrightarrow> b \<le> c \<Longrightarrow> a \<le> c\<close>
    by (force intro: map_le_trans simp add: less_eq_heap_def)
  show \<open>a \<le> b \<Longrightarrow> b \<le> a \<Longrightarrow> a = b\<close>
    by (simp add: heap.expand less_eq_heap_def prod_eq_iff map_le_antisym)
  show \<open>a \<currency> b \<Longrightarrow> b \<currency> c \<Longrightarrow> a \<currency> c \<Longrightarrow> a + b + c = a + (b + c)\<close>
    by (simp add: plus_heap_def)
  show \<open>a \<currency> b \<Longrightarrow> a + b = b + a\<close>
    by (metis disjoint_heap_def plus_heap_def map_add_comm)
  show \<open>bot \<le> a\<close>
    by (clarsimp simp add: bot_heap_def less_eq_heap_def)
  show \<open>a \<noteq> 0 \<Longrightarrow> a \<currency> a = False\<close>
    by (simp add: disjoint_heap_def zero_heap_def the_heap_eq_iff)
  show \<open>a \<currency> b = b \<currency> a\<close>
    by (force simp add: disjoint_heap_def)
  show \<open>0 \<currency> a\<close>
    by (simp add: disjoint_heap_def zero_heap_def)

  have \<open>a \<le> b \<Longrightarrow>
    a \<currency> Heap (the_heap b |` (- dom (the_heap a))) \<and>
    b = a + Heap (the_heap b |` (- dom (the_heap a)))\<close>
    unfolding less_eq_heap_def disjoint_heap_def plus_heap_def
    by (simp add: the_heap_eq_iff[symmetric] map_le_split)
  then show \<open>(a \<le> b) = (\<exists>c. a \<currency> c \<and> b = a + c)\<close>
    unfolding less_eq_heap_def disjoint_heap_def plus_heap_def
    by (fastforce simp add: map_add_comm)

  show \<open>0 + a = a\<close>
    by (simp add: plus_heap_def zero_heap_def)
qed

end


instantiation resources :: seplogic
begin
  definition
    \<open>disjoint_resources a b \<equiv> the_resources a \<inter> the_resources b = {}\<close>
  definition
    \<open>bot_resources \<equiv> Resources {}\<close>
  definition
    \<open>zero_resources \<equiv> Resources {}\<close>
  definition
    \<open>plus_resources a b \<equiv> Resources (the_resources a \<union> the_resources b)\<close>
  definition
    \<open>less_eq_resources a b \<equiv> the_resources a \<subseteq> the_resources b\<close>
  definition
    \<open>less_resources a b \<equiv> the_resources a \<subseteq> the_resources b \<and> \<not> the_resources b \<subseteq> the_resources a\<close>

instance
proof
  fix a b c :: resources

  show \<open>(a < b) = (a \<le> b \<and> \<not> b \<le> a)\<close>
    by (simp add: less_resources_def less_eq_resources_def)
  show \<open>a \<le> a\<close>
    by (simp add: less_eq_resources_def)
  show \<open>a \<le> b \<Longrightarrow> b \<le> c \<Longrightarrow> a \<le> c\<close>
    by (force simp add: less_eq_resources_def)
  show \<open>a \<le> b \<Longrightarrow> b \<le> a \<Longrightarrow> a = b\<close>
    by (simp add: less_eq_resources_def resources.expand)
  show \<open>a \<currency> b \<Longrightarrow> b \<currency> c \<Longrightarrow> a \<currency> c \<Longrightarrow> a + b + c = a + (b + c)\<close>
    by (force simp add: disjoint_resources_def plus_resources_def)
  show \<open>a \<currency> b \<Longrightarrow> a + b = b + a\<close>
    by (force simp add: disjoint_resources_def plus_resources_def)
  show \<open>bot \<le> a\<close>
    by (clarsimp simp add: bot_resources_def less_eq_resources_def)
  show \<open>a \<noteq> 0 \<Longrightarrow> a \<currency> a = False\<close>
    by (simp add: disjoint_resources_def zero_resources_def the_resources_eq_iff)
  show \<open>a \<currency> b = b \<currency> a\<close>
    by (force simp add: disjoint_resources_def)
  show \<open>0 \<currency> a\<close>
    by (simp add: disjoint_resources_def zero_resources_def)
  show \<open>(a \<le> b) = (\<exists>c. a \<currency> c \<and> b = a + c)\<close>
    apply (simp add: less_eq_resources_def disjoint_resources_def plus_resources_def)
    sledgehammer
    sorry
  show \<open>0 + a = a\<close>
    by (simp add: plus_resources_def zero_resources_def)
qed

end


instantiation prod :: (seplogic,seplogic) seplogic
begin
  definition
    \<open>disjoint_prod a b \<equiv> fst a \<currency> fst b \<and> snd a \<currency> snd b\<close>
  definition
    \<open>less_eq_prod a b \<equiv> fst a \<le> fst b \<and> snd a \<le> snd b\<close>
  definition
    \<open>less_prod a b \<equiv> fst a \<le> fst b \<and> snd a \<le> snd b \<and> \<not> (fst b \<le> fst a \<and> snd b \<le> snd a)\<close>
  definition
    \<open>zero_prod \<equiv> (0, 0)\<close>
  definition
    \<open>bot_prod \<equiv> (bot, bot)\<close>
  definition
    \<open>plus_prod a b \<equiv> (fst a + fst b, snd a + snd b)\<close>

instance
proof
  fix a b c :: \<open>('a, 'b) prod\<close>
  show \<open>a \<currency> b \<Longrightarrow> b \<currency> c \<Longrightarrow> a \<currency> c \<Longrightarrow> a + b + c = a + (b + c)\<close>
    by (clarsimp simp add: disjoint_prod_def plus_prod_def partial_add_assoc)
  show \<open>a \<currency> b \<Longrightarrow> a + b = b + a\<close>
    by (metis disjoint_prod_def plus_prod_def partial_add_commute)
  show \<open>0 + a = a\<close>
    by (simp add: plus_prod_def zero_prod_def)
  show \<open>(a < b) = (a \<le> b \<and> \<not> b \<le> a)\<close>
    by (simp add: less_prod_def less_eq_prod_def)
  show \<open>a \<le> a\<close>
    by (simp add: less_eq_prod_def)
  show \<open>a \<le> b \<Longrightarrow> b \<le> c \<Longrightarrow> a \<le> c\<close>
    by (force simp add: less_eq_prod_def)
  show \<open>a \<le> b \<Longrightarrow> b \<le> a \<Longrightarrow> a = b\<close>
    by (clarsimp simp add: less_eq_prod_def prod_eq_iff)
  show \<open>bot \<le> a\<close>
    by (clarsimp simp add: bot_prod_def less_eq_prod_def)
  show \<open>a \<noteq> 0 \<Longrightarrow> a \<currency> a = False\<close>
    by (metis (mono_tags) disjoint_nonrefl disjoint_prod_def prod.exhaust_sel zero_prod_def)
  show \<open>a \<currency> b = b \<currency> a\<close>
    by (simp add: disjoint_prod_def disjoint_symm)
  show \<open>0 \<currency> a\<close>
    by (simp add: disjoint_prod_def zero_prod_def)
  show \<open>(a \<le> b) = (\<exists>c. a \<currency> c \<and> b = a + c)\<close>
    by (force simp add: plus_prod_def disjoint_prod_def less_eq_prod_def le_iff_sepadd prod_eq_iff)
qed

end


inductive logic_comm :: \<open>('v state \<Rightarrow> bool) list \<Rightarrow>('v state \<Rightarrow> bool) \<Rightarrow> 'v comm \<Rightarrow> ('v state \<Rightarrow> bool) \<Rightarrow> bool\<close>
  (\<open>_ \<turnstile>\<^sub>c \<lbrace> _ \<rbrace> _ \<lbrace> _ \<rbrace>\<close> [80,80,80] 80)
  where
  seplogic_ramcomm: \<open>P h \<Longrightarrow> s, c \<leadsto> Some s' \<Longrightarrow> Q h' \<Longrightarrow> I \<turnstile>\<^sub>c \<lbrace> P \<rbrace> CRam c \<lbrace> Q \<rbrace>\<close>
| seplogic_seq: \<open>I \<turnstile>\<^sub>c \<lbrace> P \<rbrace> c0 \<lbrace> Q \<rbrace> \<Longrightarrow> I \<turnstile>\<^sub>c \<lbrace> Q \<rbrace> c1 \<lbrace> R \<rbrace> \<Longrightarrow> I \<turnstile>\<^sub>c \<lbrace> P \<rbrace> c0 ;; c1 \<lbrace> R \<rbrace>\<close>
| seplogic_choice: \<open>I \<turnstile>\<^sub>c \<lbrace> P \<rbrace> c0 \<lbrace> Q \<rbrace> \<Longrightarrow> I \<turnstile>\<^sub>c \<lbrace> P \<rbrace> c1 \<lbrace> Q \<rbrace> \<Longrightarrow> I \<turnstile>\<^sub>c \<lbrace> P \<rbrace> c0 \<sqinter> c1 \<lbrace> Q \<rbrace>\<close>
| seplogic_loop: \<open>I \<turnstile>\<^sub>c \<lbrace> P \<rbrace> c \<lbrace> P \<rbrace> \<Longrightarrow> I \<turnstile>\<^sub>c \<lbrace> P \<rbrace> c\<^sup>\<star> \<lbrace> P \<rbrace>\<close>
| seplogic_disj: \<open>I \<turnstile>\<^sub>c \<lbrace> P1 \<rbrace> c \<lbrace> Q1 \<rbrace> \<Longrightarrow> I \<turnstile>\<^sub>c \<lbrace> P2 \<rbrace> c \<lbrace> Q2 \<rbrace> \<Longrightarrow> I \<turnstile>\<^sub>c \<lbrace> P1 \<^bold>\<or> P2 \<rbrace> c \<lbrace> Q1 \<^bold>\<or> Q2 \<rbrace>\<close>
| seplogic_conj: \<open>I \<turnstile>\<^sub>c \<lbrace> P1 \<rbrace> c \<lbrace> Q1 \<rbrace> \<Longrightarrow> I \<turnstile>\<^sub>c \<lbrace> P2 \<rbrace> c \<lbrace> Q2 \<rbrace> \<Longrightarrow> I \<turnstile>\<^sub>c \<lbrace> P1 \<^bold>\<and> P2 \<rbrace> c \<lbrace> Q1 \<^bold>\<and> Q2 \<rbrace>\<close>
| seplogic_conseq: \<open>
  \<lbrakk> All (P \<^bold>\<longrightarrow> P')
  ; I \<turnstile>\<^sub>c \<lbrace> P' \<rbrace> c \<lbrace> Q' \<rbrace>
  ; All (Q' \<^bold>\<longrightarrow> Q)
  \<rbrakk> \<Longrightarrow> I \<turnstile>\<^sub>c \<lbrace> P \<rbrace> c \<lbrace> Q \<rbrace>\<close>
| seplogic_frame: \<open>I \<turnstile>\<^sub>c \<lbrace> P \<rbrace> c \<lbrace> Q \<rbrace> \<Longrightarrow> I \<turnstile>\<^sub>c \<lbrace> P \<star> R \<rbrace> c \<lbrace> Q \<star> R \<rbrace>\<close>
| seplogic_acquire: \<open>I \<turnstile>\<^sub>c \<lbrace> emp \<rbrace> CAcquire r \<lbrace> I ! r \<rbrace>\<close>
| seplogic_release: \<open>I \<turnstile>\<^sub>c \<lbrace> I ! r \<rbrace> CRelease r \<lbrace> emp \<rbrace>\<close>
