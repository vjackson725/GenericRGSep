theory SepLogic
  imports Main "HOL-Library.Lattice_Syntax"
begin



lemma prod_eq_decompose:
  \<open>a = (b,c) \<longleftrightarrow> fst a = b \<and> snd a = c\<close>
  \<open>(b,c) = a \<longleftrightarrow> fst a = b \<and> snd a = c\<close>
  by force+

lemma upt_add_eq_append:
  assumes \<open>i \<le> j\<close> \<open>j \<le> k\<close>
  shows \<open>[i..<k] = [i..<j] @ [j..<k]\<close>
  using assms
proof (induct k arbitrary: i j)
  case 0 then show ?case by simp
next
  case (Suc k)
  show ?case
  proof (cases \<open>j \<le> k\<close>)
    case True
    have \<open>[i..<Suc k] = [i..<k] @ [k]\<close>
      using Suc.prems True
      by simp
    also have \<open>... = [i..<j] @ [j..<k] @ [k]\<close>
      using Suc.prems True
      by (subst Suc.hyps[where j=j]; simp)
    also have \<open>... = [i..<j] @ [j..<Suc k]\<close>
      using True
      by simp
    finally show ?thesis .
  next
    case False
    then show ?thesis
      using Suc.prems
      by (clarsimp simp add: le_Suc_eq)
  qed
qed


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

definition
  \<open>seplogic_model U L D p z \<equiv>
    (z \<in> U) \<and>
    (\<forall>a\<in>U. \<forall>b\<in>U. p a b \<in> U) \<and>
    (\<forall>a\<in>U. \<forall>b\<in>U. \<forall>c\<in>U. L a b \<longrightarrow> L b c \<longrightarrow> L a c) \<and>
    (\<forall>a\<in>U. L a a) \<and>
    (\<forall>a\<in>U. \<forall>b\<in>U. L a b \<longrightarrow> L b a \<longrightarrow> a = b) \<and>
    (\<forall>a\<in>U. L z a) \<and>
    (\<forall>a\<in>U. D a a \<longrightarrow> a \<noteq> z) \<and>
    (\<forall>a\<in>U. \<forall>b\<in>U. D a b = D b a) \<and>
    (\<forall>a\<in>U. D z a) \<and>
    (\<forall>a\<in>U. \<forall>b\<in>U. \<forall>c\<in>U. D a (p b c) \<longleftrightarrow> D a b \<and> D a c) \<and>
    (\<forall>a\<in>U. \<forall>b\<in>U. L a b \<longleftrightarrow> (\<exists>c. D a c \<and> b = p a c)) \<and>
    (\<forall>a\<in>U. \<forall>b\<in>U. \<forall>c\<in>U. D a b \<longrightarrow> D b c \<longrightarrow> D a c \<longrightarrow> p (p a b) c = p a (p b c)) \<and>
    (\<forall>a\<in>U. \<forall>b\<in>U. D a b \<longrightarrow> p a b = p b a) \<and>
    (\<forall>a\<in>U. p z a = a)\<close>


definition
  \<open>seplogic_error_model U L D p z bad \<equiv>
    seplogic_model U L D p z \<and>
    (bad \<in> U) \<and>
    (\<forall>a\<in>U. \<forall>b\<in>U. \<not> D a b \<longrightarrow> p a b = bad)
  \<close>

lemma
    \<open>seplogic_model U L D p z \<longleftrightarrow>
      seplogic_error_model (insert bad U) L D (\<lambda>a b. if D a b then p a b else bad) z bad\<close>
  unfolding seplogic_model_def seplogic_error_model_def
  by (safe; fast)


class seplogic = plus + zero + order_bot +
  fixes disjoint :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (infix \<open>\<currency>\<close> 70)
  assumes disjoint_refl_only_zero: \<open>a \<currency> a \<Longrightarrow> a = 0\<close>
  assumes disjoint_symm: \<open>a \<currency> b = b \<currency> a\<close>
  assumes disjoint_empty[simp]: \<open>0 \<currency> a\<close>
  assumes disjoint_add_left[simp]: \<open>a \<currency> (b + c) \<longleftrightarrow> a \<currency> b \<and> a \<currency> c\<close>
  assumes le_iff_sepadd: \<open>a \<le> b \<longleftrightarrow> (\<exists>c. a \<currency> c \<and> b = a + c)\<close>
  (* partial commutative monoid *)
  assumes partial_add_assoc:
    "a \<currency> b \<Longrightarrow> b \<currency> c \<Longrightarrow> a \<currency> c \<Longrightarrow> (a + b) + c = a + (b + c)"
  assumes partial_add_commute: \<open>a \<currency> b \<Longrightarrow> a + b = b + a\<close>
  assumes partial_add_0[simp]: "0 + a = a"
(*
  fixes bad :: 'a
  assumes \<open>\<not> (a \<currency> b) \<Longrightarrow> a + b = bad\<close>
*)
begin

(*
lemma bad_not_sep: \<open>a \<noteq> 0 \<Longrightarrow> \<not> (bad \<currency> a)\<close>
  by (metis disjoint_add_left disjoint_refl_only_zero disjoint_symm not_sep_add_bad)
*)

lemma disjoint_add_right[simp]: \<open>(a + b) \<currency> c \<longleftrightarrow> a \<currency> c \<and> b \<currency> c\<close>
  by (simp add: disjoint_symm)

(*
lemma inf_plus_distrib_right: \<open>a \<currency> b \<Longrightarrow> (a + b) \<sqinter> c = a \<sqinter> c + b \<sqinter> c\<close>
  by (simp add: inf_commute inf_plus_distrib_left)
*)

lemma disjoint_empty_right[simp]: \<open>h \<currency> 0\<close>
  using disjoint_symm by fastforce

lemma sep_add_0_right[simp]: "a + 0 = a"
  by (metis disjoint_empty partial_add_0 partial_add_commute)

lemma zero_le[simp]: \<open>0 \<le> a\<close>
  by (simp add: le_iff_sepadd)

lemma le_zero_eq: \<open>a \<le> 0 \<longleftrightarrow> a = 0\<close>
  by (meson antisym zero_le)

lemma bot_eq_zero: \<open>bot = 0\<close>
  by (simp add: antisym)

lemma le_nonzero_not_disjoint: \<open>a \<le> b \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> \<not> (a \<currency> b)\<close>
  using disjoint_refl_only_zero le_iff_sepadd by force

lemma le_plus: \<open>a \<currency> b \<Longrightarrow> a \<le> a + b\<close>
  using le_iff_sepadd by auto

lemma le_plus2: \<open>a \<currency> b \<Longrightarrow> b \<le> a + b\<close>
  by (metis le_plus disjoint_symm partial_add_commute)


lemma exists_intersection_heap:
  \<open>\<exists>ab. ab \<le> a \<and> ab \<le> b \<and> (\<forall>ab'. ab' \<le> a \<longrightarrow> ab' \<le> b \<longrightarrow> ab' \<le> ab)\<close>
  oops

(*
lemma disjoint_impl_int_empty: \<open>a \<currency> b \<Longrightarrow> a \<sqinter> b = 0\<close>
  by (metis disjoint_add_right le_nonzero_not_disjoint inf.cobounded1 inf_le2 le_iff_sepadd)
  thm le_nonzero_not_disjoint disjoint_add_left disjoint_symm inf.cobounded2 inf_le1 le_iff_sepadd
  thm disjoint_add_right le_nonzero_not_disjoint inf.cobounded1 inf_le2 le_iff_sepadd
*)

lemma sepalg_add_right_cancel: \<open>(b + a = c + a) = (b = c)\<close>
  oops

(*
lemma plus_eq_plus_split:
  \<open>a \<currency> b \<Longrightarrow> c \<currency> d \<Longrightarrow> a + b = c + d \<longleftrightarrow> (\<exists>ac bc ad bd. a = ac + ad \<and> b = bc + bd \<and> c = ac + bc \<and> d = ad + bd)\<close>
  apply (rule iffI)
   apply (rule_tac x=\<open>a \<sqinter> c\<close> in exI)
   apply (rule_tac x=\<open>b \<sqinter> c\<close> in exI)
   apply (rule_tac x=\<open>a \<sqinter> d\<close> in exI)
   apply (rule_tac x=\<open>b \<sqinter> d\<close> in exI)
   apply (intro conjI)
      apply (metis inf.orderE inf_plus_distrib_left le_iff_sepadd)
     apply (metis disjoint_symm inf.orderE inf_plus_distrib_left le_iff_sepadd partial_add_commute)
    apply (metis inf.commute inf.orderE inf_plus_distrib_left le_iff_sepadd)
   apply (metis inf_plus_distrib_right disjoint_symm inf.absorb_iff2 le_iff_sepadd partial_add_commute)
  using disjoint_symm partial_add_assoc partial_add_commute apply force
  done
*)

definition sepconj :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> (infixl \<open>\<^emph>\<close> 88) where
  \<open>P \<^emph> Q \<equiv> \<lambda>h. \<exists>h1 h2. h1 \<currency> h2 \<and> h = h1 + h2 \<and> P h1 \<and> Q h2\<close>

definition sepimp :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> (infixr \<open>\<midarrow>\<^emph>\<close> 86) where
  \<open>P \<midarrow>\<^emph> Q \<equiv> \<lambda>h. \<forall>h1. h \<currency> h1 \<longrightarrow> P h1 \<longrightarrow> Q (h + h1)\<close>

definition sepcoimp :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> (infixr \<open>\<sim>\<^emph>\<close> 86) where
  \<open>P \<sim>\<^emph> Q \<equiv> \<lambda>h. \<forall>h1 h2. h1 \<currency> h2 \<longrightarrow> h = h1 + h2 \<longrightarrow> P h1 \<longrightarrow> Q h2\<close>

definition septract :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> (infixr \<open>\<midarrow>\<odot>\<close> 86) where
  \<open>P \<midarrow>\<odot> Q \<equiv> \<lambda>h. \<exists>h1. h \<currency> h1 \<and> P h1 \<and> Q (h + h1)\<close>

definition septract_rev :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> (infixr \<open>\<odot>\<midarrow>\<close> 86) where
  \<open>P \<odot>\<midarrow> Q \<equiv> \<lambda>h. \<exists>h'. h \<currency> h' \<and> P (h + h') \<and> Q h'\<close>

definition emp :: \<open>'a \<Rightarrow> bool\<close> where
  \<open>emp \<equiv> (\<lambda>h. h = 0)\<close>

fun iterated_sepconj :: \<open>('a \<Rightarrow> bool) list \<Rightarrow> ('a \<Rightarrow> bool)\<close> where
  \<open>iterated_sepconj (P # Ps) = P \<^emph> iterated_sepconj Ps\<close>
| \<open>iterated_sepconj [] = emp\<close>


lemma septract_reverse: \<open>P \<midarrow>\<odot> Q = Q \<odot>\<midarrow> P\<close>
  by (force simp add: septract_def septract_rev_def)

lemma sepconj_assoc: \<open>(P \<^emph> Q) \<^emph> R = P \<^emph> (Q \<^emph> R)\<close>
  by (force simp add: sepconj_def ex_simps[symmetric] partial_add_assoc simp del: ex_simps)

lemma sepconj_comm: \<open>P \<^emph> Q = Q \<^emph> P\<close>
  unfolding sepconj_def
  by (metis disjoint_symm partial_add_commute)

lemma sepconj_left_comm: \<open>Q \<^emph> (P \<^emph> R) = P \<^emph> (Q \<^emph> R)\<close>
  apply (clarsimp simp add: sepconj_def ex_simps[symmetric] simp del: ex_simps)
  apply (metis (hide_lams) disjoint_symm partial_add_assoc partial_add_commute)
  done

lemmas sepconj_ac = sepconj_assoc sepconj_comm sepconj_left_comm

lemma septract_sepimp_dual: \<open>P \<midarrow>\<odot> Q = \<^bold>\<not>(P \<midarrow>\<^emph> \<^bold>\<not> Q)\<close>
  unfolding septract_def sepimp_def pred_neg_def
  by blast

lemma sepimp_sepcoimp_dual: \<open>P \<sim>\<^emph> Q = \<^bold>\<not>(P \<^emph> \<^bold>\<not> Q)\<close>
  unfolding sepconj_def sepcoimp_def pred_neg_def
  by blast

lemma sepconj_sepimp_galois: \<open>P \<^emph> Q \<le> R \<longleftrightarrow> P \<le> Q \<midarrow>\<^emph> R\<close>
  using sepconj_def sepimp_def by fastforce

lemma sepcoimp_septract_galois: \<open>P \<odot>\<midarrow> Q \<le> R \<longleftrightarrow> P \<le> Q \<sim>\<^emph> R\<close>
  unfolding sepcoimp_def septract_rev_def le_fun_def
  using disjoint_symm partial_add_commute by fastforce

lemma emp_sepconj_unit[simp]: \<open>emp \<^emph> P = P\<close>
  by (simp add: emp_def sepconj_def)

lemma emp_sepconj_unit_right[simp]: \<open>P \<^emph> emp = P\<close>
  by (simp add: emp_def sepconj_def)

lemma sepcoimp_curry: \<open>P \<sim>\<^emph> Q \<sim>\<^emph> R = P \<^emph> Q \<sim>\<^emph> R\<close>
  unfolding sepcoimp_def sepconj_def
  apply (intro ext iffI; clarsimp)
   apply (metis disjoint_add_left partial_add_assoc)
  apply (metis disjoint_add_right partial_add_assoc)
  done

lemma sepconj_left_mono:
  \<open>P \<le> Q \<Longrightarrow> P \<^emph> R \<le> Q \<^emph> R\<close>
  using sepconj_def by auto

lemma sepconj_right_mono:
  \<open>Q \<le> R \<Longrightarrow> P \<^emph> Q \<le> P \<^emph> R\<close>
  using sepconj_def by auto


definition precise :: \<open>('a \<Rightarrow> bool) \<Rightarrow> bool\<close> where
  \<open>precise P \<equiv> \<forall>h h1. h1\<le>h \<longrightarrow> P h1 \<longrightarrow> (\<forall>h2\<le>h. P h2 \<longrightarrow> h1 = h2)\<close>

lemma precise_iff_conj_distrib:
  assumes sepalg_add_right_cancel: \<open>\<And>a b c. (b + a = c + a) = (b = c)\<close>
  shows \<open>precise P \<longleftrightarrow> (\<forall>Q Q'. (Q \<^bold>\<and> Q') \<^emph> P = (Q \<^emph> P) \<^bold>\<and> (Q' \<^emph> P))\<close>
proof (rule iffI)
  assume distrib_assm: \<open>\<forall>Q Q'. (Q \<^bold>\<and> Q') \<^emph> P = (Q \<^emph> P) \<^bold>\<and> (Q' \<^emph> P)\<close>
  show \<open>precise P\<close>
  proof (clarsimp simp add: precise_def le_iff_sepadd)
    fix h1 h1' h2 h2'
    presume precise_assms:
      \<open>h1 + h1' = h2 + h2'\<close>
      \<open>h1 \<currency> h1'\<close>
      \<open>h2 \<currency> h2'\<close>
      \<open>P h1\<close>
      \<open>P h2\<close>

    have \<open>(((=) h1') \<^emph> P) (h2+h2')\<close>
      using precise_assms partial_add_commute disjoint_symm sepconj_def
      by auto
    moreover have \<open>(((=) h2') \<^emph> P) (h2+h2')\<close>
      using precise_assms partial_add_commute disjoint_symm sepconj_def
      by auto
    ultimately have \<open>((\<lambda>h. h1' = h \<and> h2' = h) \<^emph> P) (h2+h2')\<close>
      using distrib_assm precise_assms
      by (simp add: pred_conj_def)
    then show \<open>h1 = h2\<close>
      using precise_assms
      by (clarsimp simp add: sepconj_def precise_assms, metis sepalg_add_right_cancel)
  qed
next
  presume precise_assm:  \<open>precise P\<close>
  then show \<open>\<forall>Q Q'. (Q \<^bold>\<and> Q') \<^emph> P = (Q \<^emph> P) \<^bold>\<and> (Q' \<^emph> P)\<close>
    apply (auto simp add: sepconj_def precise_def pred_conj_def fun_eq_iff le_iff_sepadd)
    apply (metis partial_add_commute disjoint_symm sepalg_add_right_cancel)
    done
qed


lemma precise_iff_all_sepconj_imp_sepcoimp:
  assumes sepalg_add_right_cancel: \<open>\<And>a b c. (b + a = c + a) = (b = c)\<close>
  shows \<open>precise P \<longleftrightarrow> (\<forall>Q. P \<^emph> Q \<le> P \<sim>\<^emph> Q)\<close>
  apply (clarsimp simp add: sepconj_def sepcoimp_def precise_def le_fun_def le_iff_sepadd)
  apply (rule iffI)
   apply (metis sepalg_add_right_cancel partial_add_commute)
  apply (metis sepalg_add_right_cancel antisym order.refl)
  done

lemma secoimp_imp_sepconj:
  \<open>P \<^bold>\<and> (P \<sim>\<^emph> Q) \<le> P \<^emph> Q\<close>
  unfolding pred_conj_def sepcoimp_def sepconj_def le_fun_def le_bool_def
  by (metis disjoint_empty_right sep_add_0_right)

lemma sepcoimp_conj_distrib_left:
  \<open>P \<sim>\<^emph> (Q \<^bold>\<and> Q') = (P \<sim>\<^emph> Q) \<^bold>\<and> (P \<sim>\<^emph> Q')\<close>
  by (force simp add: pred_conj_def sepcoimp_def)

lemma not_coimp_emp:
  \<open>h \<noteq> 0 \<Longrightarrow> (\<^bold>\<not> (\<^bold>T \<sim>\<^emph> emp)) h\<close>
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
  | CNDet \<open>'v comm\<close> \<open>'v comm\<close> (infixr \<open>\<box>\<close> 86)
  | CLoop \<open>'v comm\<close> (\<open>(_)\<^sup>\<star>\<close> 88)
  | CAcquire nat
  | CRelease nat

type_synonym 'v prog = \<open>'v comm list\<close>

datatype 'v varenv = VarEnv (the_varenv: \<open>'v \<rightharpoonup> nat\<close>)
datatype heap = Heap (the_heap: \<open>nat \<rightharpoonup> nat\<close>)
datatype resources = Resources (the_resources: \<open>nat set\<close>)

definition \<open>remove_res j r \<equiv> case r of Resources R \<Rightarrow> Resources (R - {j})\<close>
definition \<open>insert_res j r \<equiv> case r of Resources R \<Rightarrow> Resources (insert j R)\<close>

lemma resources_the_of_remove[simp]:
  \<open>the_resources (remove_res r R) = the_resources R - {r}\<close>
  by (simp add: remove_res_def split: resources.splits)

lemma resources_the_of_insert[simp]:
  \<open>the_resources (insert_res r R) = insert r (the_resources R)\<close>
  by (simp add: insert_res_def split: resources.splits)


lemma VarEnv_always_ex: \<open>\<exists>v'. v = VarEnv v'\<close>
  by (meson varenv.exhaust_sel)
lemma Heap_always_ex: \<open>\<exists>h'. h = Heap h'\<close>
  by (meson heap.exhaust_sel)
lemma Resources_always_ex: \<open>\<exists>r'. r = Resources r'\<close>
  by (meson resources.exhaust_sel)


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

inductive_cases opsem_ram_comm_CSkipE[elim!]: \<open>s, CSkip \<leadsto> s'\<close>
inductive_cases opsem_ram_comm_CAssignE[elim!]: \<open>s, CAssign x e \<leadsto> s'\<close>
inductive_cases opsem_ram_comm_CHeapRE[elim]: \<open>s, CHeapR x e \<leadsto> s'\<close>
inductive_cases opsem_ram_comm_CHeapWE[elim!]: \<open>s, CHeapW ep e \<leadsto> s'\<close>
inductive_cases opsem_ram_comm_CHeapNewE[elim]: \<open>s, CHeapNew x \<leadsto> s'\<close>
inductive_cases opsem_ram_comm_CHeapDelE[elim]: \<open>s, CHeapDel e \<leadsto> s'\<close>
inductive_cases opsem_ram_comm_CAssumeE[elim!]: \<open>s, CAssume b \<leadsto> s'\<close>

lemma opsem_ram_comm_simps:
  \<open>s, CSkip \<leadsto> os' \<longleftrightarrow> (\<exists>s1. os' = Some s1 \<and> s = s1)\<close>
  \<open>s, CAssign x e \<leadsto> os' \<longleftrightarrow>
    (\<exists>v h r. s = (VarEnv v, h, r) \<and> os' = Some (VarEnv (v(x := \<lbrakk>e\<rbrakk>\<^sub>I v)), h, r))\<close>
  \<open>s, CHeapR x ep \<leadsto> os' \<longleftrightarrow>
    (\<exists>v h r. s = (VarEnv v, h, r) \<and>
    (case \<lbrakk>ep\<rbrakk>\<^sub>I v of
      Some p \<Rightarrow> os' = Some (VarEnv (v(x := the_heap h p)), h, r)
    | None \<Rightarrow> os' = None))\<close>
  \<open>s, CHeapW ep e \<leadsto> os' \<longleftrightarrow>
    (\<exists>v h r. s = (VarEnv v, Heap h, r) \<and>
    (case \<lbrakk>ep\<rbrakk>\<^sub>I v of
      Some p \<Rightarrow> os' = Some (VarEnv v, Heap (h(p := \<lbrakk>e\<rbrakk>\<^sub>I v)), r)
    | None \<Rightarrow> os' = None))\<close>
  \<open>s, CHeapNew x \<leadsto> os' \<longleftrightarrow>
    (\<exists>v h r p. s = (VarEnv v, Heap h, r) \<and>
    (case h p of
      Some _ \<Rightarrow> os' = None
    | None \<Rightarrow> os' = Some (VarEnv (v(x \<mapsto> p)), Heap (h(p \<mapsto> undefined)), r)))\<close>
  \<open>s, CHeapDel e \<leadsto> os' \<longleftrightarrow>
    (\<exists>v h r. s = (VarEnv v, Heap h, r) \<and>
    (case \<lbrakk>e\<rbrakk>\<^sub>I v of
      Some p \<Rightarrow> (case h p of
          Some _ \<Rightarrow> os' = Some (VarEnv v, Heap (h(p := None)), r)
        | None \<Rightarrow> os' = None
        )
    | None \<Rightarrow> os' = None))\<close>
  \<open>s, CAssume b \<leadsto> os' \<longleftrightarrow>
    (\<exists>v h r. s = (VarEnv v, h, r) \<and> \<lbrakk>b\<rbrakk>\<^sub>B v = Some True \<and> os' = Some (VarEnv v, h, r))\<close>
proof -
  show \<open>s, CHeapW ep e \<leadsto> os' =
    (\<exists>v h r.
        s = (VarEnv v, Heap h, r) \<and>
        (case \<lbrakk>ep\<rbrakk>\<^sub>I v of None \<Rightarrow> os' = None
        | Some p \<Rightarrow> os' = Some (VarEnv v, Heap (h(p := \<lbrakk>e\<rbrakk>\<^sub>I v)), r)))\<close>
    by (fastforce simp add: Heap_always_ex intro: opsem_ram_comm.intros split: option.splits)
  show \<open>s, CHeapNew x \<leadsto> os' =
    (\<exists>v h r p.
        s = (VarEnv v, Heap h, r) \<and>
        (case h p of None \<Rightarrow> os' = Some (VarEnv (v(x \<mapsto> p)), Heap (h(p \<mapsto> undefined)), r)
         | Some x \<Rightarrow> os' = None))\<close>
    by (force simp add: opsem_ram_comm.simps split: option.splits)
  show \<open>s, CHeapDel e \<leadsto> os' =
    (\<exists>v h r.
        s = (VarEnv v, Heap h, r) \<and>
        (case \<lbrakk>e\<rbrakk>\<^sub>I v of None \<Rightarrow> os' = None
         | Some p \<Rightarrow>
             (case h p of None \<Rightarrow> os' = None | Some x \<Rightarrow> os' = Some (VarEnv v, Heap (h(p := None)), r))))\<close>
    apply (simp split: option.splits)
    apply (rule iffI)
      (* Part 1 *)
     apply (erule opsem_ram_comm_CHeapDelE)
       apply (clarsimp, metis not_Some_eq option.inject)
      apply (force simp add: the_heap_eq_iff[symmetric] split: option.splits)
     apply fastforce
      (* Part 2 *)
    apply clarsimp
    apply (case_tac \<open>\<lbrakk>e\<rbrakk>\<^sub>I v\<close>; clarsimp simp add: opsem_ram_comm.intros)
    apply (case_tac \<open>h a\<close>; simp add: opsem_ram_comm.intros all_conj_distrib)
    done
qed (fastforce intro: opsem_ram_comm.intros split: option.splits)+


lemma opsem_ram_comm_mostly_deterministic:
  \<open>s, c \<leadsto> s0 \<Longrightarrow> s, c \<leadsto> s1 \<Longrightarrow> \<forall>x. c \<noteq> CHeapNew x \<Longrightarrow> s0 = s1\<close>
  by (induct arbitrary: s1 rule: opsem_ram_comm.inducts) fastforce+

lemma opsem_ram_comm_success_mono:
  \<open>s, c \<leadsto> os' \<Longrightarrow>
  P \<le> Q \<Longrightarrow>
  P s \<Longrightarrow>
  \<exists>s. Q s \<and> s, c \<leadsto> os'\<close>
  by (induct rule: opsem_ram_comm.inducts)
    (fastforce simp add: le_fun_def intro: opsem_ram_comm.intros)+

lemma opsem_ram_comm_same_resources:
  \<open>s, c \<leadsto> os' \<Longrightarrow> os' = Some s' \<Longrightarrow> snd (snd s) = snd (snd s')\<close>
  by (induct arbitrary: s' rule: opsem_ram_comm.inducts) force+


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
  show \<open>a \<currency> a \<Longrightarrow> a = 0\<close>
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
  show \<open>a \<currency> (b + c) = (a \<currency> b \<and> a \<currency> c)\<close>
    by (force simp add: disjoint_varenv_def plus_varenv_def Int_Un_distrib)
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
  show \<open>a \<currency> a \<Longrightarrow> a = 0\<close>
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
  show \<open>a \<currency> (b + c) = (a \<currency> b \<and> a \<currency> c)\<close>
    by (force simp add: disjoint_heap_def plus_heap_def Int_Un_distrib)
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
  show \<open>a \<currency> a \<Longrightarrow> a = 0\<close>
    by (simp add: disjoint_resources_def zero_resources_def the_resources_eq_iff)
  show \<open>a \<currency> b = b \<currency> a\<close>
    by (force simp add: disjoint_resources_def)
  show \<open>0 \<currency> a\<close>
    by (simp add: disjoint_resources_def zero_resources_def)
  show \<open>(a \<le> b) = (\<exists>c. a \<currency> c \<and> b = a + c)\<close>
    apply (simp add: less_eq_resources_def disjoint_resources_def plus_resources_def)
    apply (rule iffI)
     apply (metis Diff_disjoint Diff_partition the_resources_eq_iff)
    apply force
    done
  show \<open>0 + a = a\<close>
    by (simp add: plus_resources_def zero_resources_def)
  show \<open>a \<currency> (b + c) = (a \<currency> b \<and> a \<currency> c)\<close>
    by (force simp add: disjoint_resources_def plus_resources_def Int_Un_distrib)
qed

end


instantiation prod :: (seplogic,seplogic) seplogic
begin
  definition
    \<open>disjoint_prod a b \<equiv> fst a \<currency> fst b \<and> snd a \<currency> snd b\<close>
  declare disjoint_prod_def[simp]
  definition
    \<open>less_eq_prod a b \<equiv> fst a \<le> fst b \<and> snd a \<le> snd b\<close>
  declare less_eq_prod_def[simp]
  definition
    \<open>less_prod a b \<equiv> fst a \<le> fst b \<and> snd a \<le> snd b \<and> \<not> (fst b \<le> fst a \<and> snd b \<le> snd a)\<close>
  declare less_prod_def[simp]
  definition
    \<open>zero_prod \<equiv> (0, 0)\<close>
  declare zero_prod_def[simp]
  definition
    \<open>bot_prod \<equiv> (bot, bot)\<close>
  declare bot_prod_def[simp]
  definition
    \<open>plus_prod a b \<equiv> (fst a + fst b, snd a + snd b)\<close>
  declare plus_prod_def[simp]

instance
proof
  fix a b c :: \<open>('a, 'b) prod\<close>
  show \<open>a \<currency> b \<Longrightarrow> b \<currency> c \<Longrightarrow> a \<currency> c \<Longrightarrow> a + b + c = a + (b + c)\<close>
    by (clarsimp simp add: partial_add_assoc)
  show \<open>a \<currency> b \<Longrightarrow> a + b = b + a\<close>
    by (metis disjoint_prod_def plus_prod_def partial_add_commute)
  show \<open>0 + a = a\<close>
    by simp
  show \<open>(a < b) = (a \<le> b \<and> \<not> b \<le> a)\<close>
    by simp
  show \<open>a \<le> a\<close>
    by simp
  show \<open>a \<le> b \<Longrightarrow> b \<le> c \<Longrightarrow> a \<le> c\<close>
    by force
  show \<open>a \<le> b \<Longrightarrow> b \<le> a \<Longrightarrow> a = b\<close>
    by (clarsimp simp add: prod_eq_iff)
  show \<open>bot \<le> a\<close>
    by simp
  show \<open>a \<currency> a \<Longrightarrow> a = 0\<close>
    by (metis (mono_tags) disjoint_refl_only_zero disjoint_prod_def prod.exhaust_sel zero_prod_def)
  show \<open>a \<currency> b = b \<currency> a\<close>
    by (simp add: disjoint_symm)
  show \<open>0 \<currency> a\<close>
    by simp
  show \<open>(a \<le> b) = (\<exists>c. a \<currency> c \<and> b = a + c)\<close>
    by (force simp add: le_iff_sepadd prod_eq_iff)
  show \<open>a \<currency> (b + c) = (a \<currency> b \<and> a \<currency> c)\<close>
    by force
qed

end


inductive logic_comm :: \<open>('v state \<Rightarrow> bool) list \<Rightarrow>('v state \<Rightarrow> bool) \<Rightarrow> 'v comm \<Rightarrow> ('v state \<Rightarrow> bool) \<Rightarrow> bool\<close>
  (\<open>_ \<turnstile>\<^sub>c \<lbrace> _ \<rbrace> _ \<lbrace> _ \<rbrace>\<close> [80,80,80,80] 80)
  where
  seplogic_ramcomm: \<open>P h \<Longrightarrow> s, c \<leadsto> Some s' \<Longrightarrow> Q h' \<Longrightarrow> I \<turnstile>\<^sub>c \<lbrace> P \<rbrace> CRam c \<lbrace> Q \<rbrace>\<close>
| seplogic_seq: \<open>I \<turnstile>\<^sub>c \<lbrace> P \<rbrace> c0 \<lbrace> Q \<rbrace> \<Longrightarrow> I \<turnstile>\<^sub>c \<lbrace> Q \<rbrace> c1 \<lbrace> R \<rbrace> \<Longrightarrow> I \<turnstile>\<^sub>c \<lbrace> P \<rbrace> c0 ;; c1 \<lbrace> R \<rbrace>\<close>
| seplogic_choice: \<open>I \<turnstile>\<^sub>c \<lbrace> P \<rbrace> c0 \<lbrace> Q \<rbrace> \<Longrightarrow> I \<turnstile>\<^sub>c \<lbrace> P \<rbrace> c1 \<lbrace> Q \<rbrace> \<Longrightarrow> I \<turnstile>\<^sub>c \<lbrace> P \<rbrace> c0 \<box> c1 \<lbrace> Q \<rbrace>\<close>
| seplogic_loop: \<open>I \<turnstile>\<^sub>c \<lbrace> P \<rbrace> c \<lbrace> P \<rbrace> \<Longrightarrow> I \<turnstile>\<^sub>c \<lbrace> P \<rbrace> c\<^sup>\<star> \<lbrace> P \<rbrace>\<close>
| seplogic_disj: \<open>I \<turnstile>\<^sub>c \<lbrace> P1 \<rbrace> c \<lbrace> Q1 \<rbrace> \<Longrightarrow> I \<turnstile>\<^sub>c \<lbrace> P2 \<rbrace> c \<lbrace> Q2 \<rbrace> \<Longrightarrow> I \<turnstile>\<^sub>c \<lbrace> P1 \<^bold>\<or> P2 \<rbrace> c \<lbrace> Q1 \<^bold>\<or> Q2 \<rbrace>\<close>
| seplogic_conj: \<open>I \<turnstile>\<^sub>c \<lbrace> P1 \<rbrace> c \<lbrace> Q1 \<rbrace> \<Longrightarrow> I \<turnstile>\<^sub>c \<lbrace> P2 \<rbrace> c \<lbrace> Q2 \<rbrace> \<Longrightarrow> I \<turnstile>\<^sub>c \<lbrace> P1 \<^bold>\<and> P2 \<rbrace> c \<lbrace> Q1 \<^bold>\<and> Q2 \<rbrace>\<close>
| seplogic_conseq: \<open>
  \<lbrakk> All (P \<^bold>\<longrightarrow> P')
  ; I \<turnstile>\<^sub>c \<lbrace> P' \<rbrace> c \<lbrace> Q' \<rbrace>
  ; All (Q' \<^bold>\<longrightarrow> Q)
  \<rbrakk> \<Longrightarrow> I \<turnstile>\<^sub>c \<lbrace> P \<rbrace> c \<lbrace> Q \<rbrace>\<close>
| seplogic_frame: \<open>I \<turnstile>\<^sub>c \<lbrace> P \<rbrace> c \<lbrace> Q \<rbrace> \<Longrightarrow> I \<turnstile>\<^sub>c \<lbrace> P \<^emph> R \<rbrace> c \<lbrace> Q \<^emph> R \<rbrace>\<close>
| seplogic_acquire: \<open>I \<turnstile>\<^sub>c \<lbrace> emp \<rbrace> CAcquire r \<lbrace> I ! r \<rbrace>\<close>
| seplogic_release: \<open>I \<turnstile>\<^sub>c \<lbrace> I ! r \<rbrace> CRelease r \<lbrace> emp \<rbrace>\<close>


definition logic_prog :: \<open>('v state \<Rightarrow> bool) list \<Rightarrow> ('v state \<Rightarrow> bool) \<Rightarrow> 'v prog \<Rightarrow> ('v state \<Rightarrow> bool) \<Rightarrow> bool\<close>
  (\<open>_ \<turnstile>\<^sub>p \<lbrace> _ \<rbrace> _ \<lbrace> _ \<rbrace>\<close> [80,80,80,80] 80)
  where
    \<open>I \<turnstile>\<^sub>p \<lbrace> P \<rbrace> cs \<lbrace> Q \<rbrace> \<equiv>
      \<exists>Ps Qs.
        P = iterated_sepconj Ps \<and>
        Q = iterated_sepconj Qs \<and>
        length Ps = length cs \<and>
        length Qs = length cs \<and>
        (\<forall>i<length cs. I \<turnstile>\<^sub>c \<lbrace> Ps ! i \<rbrace> cs ! i \<lbrace> Qs ! i \<rbrace>)\<close>


section \<open>ram_comm Forward predicate transformer\<close>

definition ram_comm_forward :: \<open>'v ram_comm \<Rightarrow> ('v state \<Rightarrow> bool) \<Rightarrow> ('v state \<Rightarrow> bool)\<close> where
  \<open>ram_comm_forward c \<equiv> \<lambda>P. \<lambda>s'. \<exists>s. P s \<and> s, c \<leadsto> Some s'\<close>

lemma ram_comm_step_iff_forward:
  \<open>(s, c \<leadsto> Some s') \<longleftrightarrow> (=) s' \<le> ram_comm_forward c ((=) s)\<close>
  by (simp add: ram_comm_forward_def le_fun_def prod_eq_decompose)

lemma ram_comm_forward_mono:
  \<open>mono (ram_comm_forward c)\<close>
  unfolding mono_def ram_comm_forward_def le_fun_def
  by (simp, metis)

section \<open>Operational Semantics\<close>

inductive cfg :: \<open>'v comm \<Rightarrow> 'l set \<Rightarrow> ('l \<times> 'v comm \<times> 'l) set \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> bool\<close> where
  \<open>cfg (CRam c) {start,end} {(start, CRam c, end)} start end\<close>
| \<open>\<lbrakk> cfg c1 N1 T1 start1 end1
   ; cfg c2 N2 T2 start2 end2
   \<rbrakk> \<Longrightarrow> cfg (c1 ;; c2) (N1 \<union> N2) (insert (end1, CRam CSkip, start2) (T1 \<union> T2)) start1 end2\<close>
| \<open>\<lbrakk> cfg c1 N1 T1 start1 end1
   ; cfg c2 N2 T2 start2 end2
   \<rbrakk> \<Longrightarrow>
    cfg
      (c1 \<box> c2) (N1 \<union> N2 \<union> {start,end})
      (T1 \<union> T2 \<union>
        {(start,CRam CSkip,start1), (start,CRam CSkip,start2),
          (end1,CRam CSkip,end), (end2,CRam CSkip,end)})
      start end\<close>
| \<open>cfg c N T start end \<Longrightarrow>
   cfg
     (c\<^sup>\<star>) (N \<union> {start', end'})
     (T \<union> {(start',CRam CSkip,start), (end,CRam CSkip,start), (end,CRam CSkip,end')})
     start' end'\<close>


lemma cfg_start_label_in_labels:
  \<open>cfg c N T s e \<Longrightarrow> s \<in> N\<close>
  by (induct rule: cfg.inducts) simp+

lemma cfg_end_label_in_labels:
  \<open>cfg c N T s e \<Longrightarrow> e \<in> N\<close>
  by (induct rule: cfg.inducts) simp+

lemma cfg_left_transition_label_in_labels:
  \<open>cfg c N T s e \<Longrightarrow> (l,c',l') \<in> T \<Longrightarrow> l \<in> N\<close>
  by (induct rule: cfg.inducts)
    (force dest: cfg_end_label_in_labels)+

lemma cfg_right_transition_label_in_labels:
  \<open>cfg c N T s e \<Longrightarrow> (l,c',l') \<in> T \<Longrightarrow> l' \<in> N\<close>
  by (induct rule: cfg.inducts)
    (force dest: cfg_start_label_in_labels)+


subsection \<open>Small-step\<close>

inductive opsem_prog_smallstep ::
  \<open>'l list \<Rightarrow> 'v state \<Rightarrow> resources \<Rightarrow>
    ('l \<times> 'v comm \<times> 'l) set \<Rightarrow>
    'l list \<Rightarrow> 'v state option \<Rightarrow> resources \<Rightarrow>
    bool\<close>
  (\<open>_, _, _ \<sim>[_]\<leadsto>\<^sub>S _, _, _\<close> [80,0,80,0,80] 80)
  where
  \<open>\<lbrakk> k < length p
   ; (p ! k, CRam c, l') \<in> T
   ; \<sigma>, c \<leadsto> Some \<sigma>'
   \<rbrakk> \<Longrightarrow> p, \<sigma>, fR \<sim>[T]\<leadsto>\<^sub>S p[k := l'], Some \<sigma>', fR\<close>
| \<open>\<lbrakk> k < length p; (p ! k, CRam c, l') \<in> T
   ; \<sigma>, c \<leadsto> None
   \<rbrakk> \<Longrightarrow> p, \<sigma>, fR \<sim>[T]\<leadsto>\<^sub>S p[k := l'], None, fR\<close>
| \<open>\<lbrakk> k < length p
   ; (p ! k, CRelease j, l') \<in> T
   ; j \<notin> the_resources fR
   \<rbrakk> \<Longrightarrow> p, \<sigma>, fR \<sim>[T]\<leadsto>\<^sub>S p[k := l'], Some \<sigma>, (insert_res j fR)\<close>
| \<open>\<lbrakk> k < length p
   ; (p ! k, CAcquire j, l') \<in> T
   ; j \<in> the_resources fR
   \<rbrakk> \<Longrightarrow> p, \<sigma>, fR \<sim>[T]\<leadsto>\<^sub>S p[k := l'], Some \<sigma>, (remove_res j fR)\<close>

inductive opsem_prog_iter_smallstep ::
  \<open>'l list \<Rightarrow> 'v state \<Rightarrow> resources \<Rightarrow>
    ('l \<times> 'v comm \<times> 'l) set \<Rightarrow>
    'l list \<Rightarrow> 'v state option \<Rightarrow> resources \<Rightarrow>
    bool\<close>
  (\<open>_, _, _ \<sim>[_]\<leadsto>*\<^sub>S _, _, _\<close> [80,0,80,0,80] 80)
where
  opsem_prog_iter_smallstep_base: \<open>p, s, fR \<sim>[T]\<leadsto>*\<^sub>S p, Some s, fR\<close>
| opsem_prog_iter_smallstep_step:
  \<open>\<lbrakk> p, s, fR \<sim>[T]\<leadsto>\<^sub>S p', Some s', fR'
   ; p', s', fR' \<sim>[T]\<leadsto>*\<^sub>S p'', s'', fR''
   \<rbrakk> \<Longrightarrow> p, s, fR \<sim>[T]\<leadsto>*\<^sub>S p'', s'', fR''\<close>

lemma opsem_prog_smallstep_length:
  \<open>p, s, fR \<sim>[T]\<leadsto>\<^sub>S p', os', fR' \<Longrightarrow> length p = length p'\<close>
  by (induct rule: opsem_prog_smallstep.induct) simp+

lemma opsem_prog_iter_smallstep_length:
  \<open>p, s, fR \<sim>[T]\<leadsto>*\<^sub>S p', os', fR' \<Longrightarrow> length p = length p'\<close>
  by (induct rule: opsem_prog_iter_smallstep.induct) (simp add: opsem_prog_smallstep_length)+


definition semantic_proof :: \<open>'v comm \<Rightarrow> ('l \<Rightarrow> ('v state \<Rightarrow> bool)) \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close> where
  \<open>semantic_proof C G I T \<equiv>
    \<exists>N::'l set. \<exists>start end.
      cfg C N T start end \<and>
      (\<forall>(l,c',l')\<in>T. case c' of
        CRam cr' \<Rightarrow> ram_comm_forward cr' (G l) \<le> G l'
      | CAcquire r \<Rightarrow> r < length I \<and> G l \<^emph> I ! r \<le> G l'
      | CRelease r \<Rightarrow> r < length I \<and> G l \<le> G l' \<^emph> I ! r
      )\<close>

lemma map_if_index_update_eq:
  \<open>j < n \<Longrightarrow> map (\<lambda>i. if j = i then f i else g i) [0..<n] = (map g [0..<n])[j := f j]\<close>
  by (induct n arbitrary: j)
   (simp add: less_Suc_eq list_update_append split: nat.splits)+

lemma iterated_sepconj_update:
  \<open>i < length ps \<Longrightarrow>
    iterated_sepconj (ps[i := p]) =
    iterated_sepconj (take i ps) \<^emph> p \<^emph> iterated_sepconj (drop (Suc i) ps)\<close>
  by (induct ps arbitrary: p i)
    (force simp add: less_Suc_eq_0_disj sepconj_assoc)+

lemma iterated_sepconj_append_split:
  \<open>iterated_sepconj (xs @ ys) = iterated_sepconj xs \<^emph> iterated_sepconj ys\<close>
  by (induct xs arbitrary: ys) (simp add: sepconj_assoc)+

lemma iterated_sepconj_take_drop_split_at:
  assumes
    \<open>k < length xs\<close>
  shows
    \<open>iterated_sepconj xs =
    iterated_sepconj (take k xs) \<^emph> xs ! k \<^emph> iterated_sepconj (drop (Suc k) xs)\<close>
  using assms
  by (induct xs arbitrary: k) (force simp add: less_Suc_eq_0_disj sepconj_assoc)+

lemma iterated_sepconj_map_range_split_at:
  assumes
    \<open>k < n\<close>
  shows
    \<open>iterated_sepconj (map f [0..<n]) =
    iterated_sepconj (map f [0..<k]) \<^emph> f k \<^emph> iterated_sepconj (map f [Suc k..<n])\<close>
  using assms
  by (simp add: iterated_sepconj_take_drop_split_at take_map drop_map)

definition \<open>local_command c \<equiv> \<forall>P Q. ram_comm_forward c (P \<^emph> Q) \<le> (ram_comm_forward c P) \<^emph> Q\<close>

lemma local_commandI:
  \<open>local_command c \<Longrightarrow> ram_comm_forward c (P \<^emph> Q) \<le> (ram_comm_forward c P) \<^emph> Q\<close>
  by (simp add: local_command_def)

lemma \<open>local_command c\<close>
  apply (clarsimp
      simp add: local_command_def ram_comm_forward_def sepconj_def ex_simps[symmetric]
      simp del: ex_simps)
  apply (rename_tac v0 h0 r0 v1 h1 r1 v2 h2 r2)
  apply (rotate_tac 5)
  apply (rule opsem_ram_comm.induct, blast)
             apply simp
  oops

definition
  \<open>active_resource_invs I fR \<equiv>
    map (\<lambda>k. if k \<in> the_resources fR then I ! k else emp) [0..<length I]\<close>


lemma active_resource_invs_index[simp]:
  \<open>k < length I \<Longrightarrow> active_resource_invs I fR ! k = (if k \<in> the_resources fR then I ! k else emp)\<close>
  by (simp add: active_resource_invs_def)

lemma active_resource_invs_length[simp]:
  \<open>length (active_resource_invs I fR) = length I\<close>
  by (simp add: active_resource_invs_def)


lemma lem_4_2_separation_property:
  assumes
    \<open>pc0, s0, fR0 \<sim>[T]\<leadsto>*\<^sub>S pc, os, fR\<close>
    \<open>\<forall>k<length pc0. semantic_proof (Cs k) (Gs k) I T\<close>
    \<open>os = Some s\<close>
    \<open>(iterated_sepconj (map (\<lambda>k. Gs k (pc0 ! k)) [0..<length pc0]) \<^emph>
      iterated_sepconj (active_resource_invs I fR0))
      s0\<close>
  shows
    \<open>(iterated_sepconj (map (\<lambda>k. Gs k (pc ! k)) [0..<length pc]) \<^emph>
      iterated_sepconj (active_resource_invs I fR))
      s\<close>
  using assms
proof (induct arbitrary: s rule: opsem_prog_iter_smallstep.induct)
  case opsem_prog_iter_smallstep_base then show ?case by (simp add: le_fun_def)
next
  case (opsem_prog_iter_smallstep_step p s fR T p' s' fR' p'' os'' fR'' s'')
  then show ?case
  proof (cases rule: opsem_prog_smallstep.cases[case_names CRam_succeed CRam_fail CRelease CAcquire])
    case (CRam_succeed k c l')

    have c_local: \<open>local_command c\<close>
      sorry

    show ?thesis
    proof (rule opsem_prog_iter_smallstep_step)
      show \<open>\<forall>k<length p'. semantic_proof (Cs k) (Gs k) I T\<close>
        using opsem_prog_iter_smallstep_step.prems CRam_succeed
        by simp

      show \<open>os'' = Some s''\<close>
        using opsem_prog_iter_smallstep_step.prems
        by simp

      have c_predicate_transformer: \<open>ram_comm_forward c (Gs k (p ! k)) \<le> Gs k l'\<close>
        using CRam_succeed opsem_prog_iter_smallstep_step(4)
        by (fastforce simp add: semantic_proof_def)

      show
        \<open>(iterated_sepconj (map (\<lambda>k. Gs k (p' ! k)) [0..<length p']) \<^emph>
          iterated_sepconj (active_resource_invs I fR')) s'\<close>
      proof -
        have \<open>(=) s' \<le> ram_comm_forward c ((=) s)\<close>
          using CRam_succeed
          by (clarsimp simp add: le_fun_def ram_comm_forward_def prod_eq_decompose)
        also have \<open>... \<le>
          ram_comm_forward c (iterated_sepconj (map (\<lambda>k. Gs k (p ! k)) [0..<length p]) \<^emph>
          iterated_sepconj (active_resource_invs I fR))\<close>
          using opsem_prog_iter_smallstep_step.prems
          by (force intro!: monoD[OF ram_comm_forward_mono] simp add: le_fun_def)
        also have \<open>... \<le>
          ram_comm_forward c
         (iterated_sepconj (map (\<lambda>k. Gs k (p ! k)) [0..<k]) \<^emph>
          iterated_sepconj (map (\<lambda>k. Gs k (p ! k)) [k..<length p]) \<^emph>
          iterated_sepconj (active_resource_invs I fR))\<close>
          using CRam_succeed
          by (simp add:
              iterated_sepconj_append_split upt_add_eq_append[OF le0 order.strict_implies_order])
        also have \<open>... \<le>
          ram_comm_forward c
          (Gs k (p ! k) \<^emph>
          (iterated_sepconj (map (\<lambda>k. Gs k (p ! k)) [0..<k]) \<^emph>
          iterated_sepconj (map (\<lambda>k. Gs k (p ! k)) [Suc k..<length p]) \<^emph>
          iterated_sepconj (active_resource_invs I fR)))\<close>
          using CRam_succeed
          by (simp add: upt_conv_Cons sepconj_assoc sepconj_left_comm)
        also have \<open>... \<le>
          ram_comm_forward c (Gs k (p ! k)) \<^emph>
          (iterated_sepconj (map (\<lambda>k. Gs k (p ! k)) [0..<k]) \<^emph>
          iterated_sepconj (map (\<lambda>k. Gs k (p ! k))[Suc k..<length p]) \<^emph>
          iterated_sepconj (active_resource_invs I fR))\<close>
          using c_local
          by (force intro!: local_commandI)
        also have \<open>... \<le>
          Gs k l' \<^emph>
          ((iterated_sepconj (map (\<lambda>k. Gs k (p ! k)) [0..<k]) \<^emph>
          iterated_sepconj (map (\<lambda>k. Gs k (p ! k))[Suc k..<length p])) \<^emph>
          iterated_sepconj (active_resource_invs I fR))\<close>
          using c_predicate_transformer
          by (simp add: sepconj_left_mono sepconj_right_mono)
        also have \<open>... \<le>
          (iterated_sepconj (map (\<lambda>ka. Gs ka (p ! ka)) [0..<k]) \<^emph>
          Gs k l' \<^emph>
          iterated_sepconj (map (\<lambda>ka. Gs ka (p ! ka)) [Suc k..<length p])) \<^emph>
          iterated_sepconj (active_resource_invs I fR)\<close>
          by (simp add: sepconj_assoc sepconj_left_comm)
        also have \<open>... \<le>
          iterated_sepconj (map (\<lambda>ka. Gs ka (p[k := l'] ! ka)) [0..<length p]) \<^emph>
          iterated_sepconj (active_resource_invs I fR)\<close>
        proof -
          have s0: \<open>map (\<lambda>ka. Gs ka (p[k := l'] ! ka)) [0..<k] = map (\<lambda>ka. Gs ka (p ! ka)) [0..<k]\<close>
            by simp
          have s1: \<open>
          map (\<lambda>ka. Gs ka (p[k := l'] ! ka)) [Suc k..<length p] =
          map (\<lambda>ka. Gs ka (p ! ka)) [Suc k..<length p]\<close>
            by simp
          have s2: \<open>
            map (\<lambda>ka. Gs ka (p[k := l'] ! ka)) [0..<length p] =
              map (\<lambda>ka. Gs ka (p[k := l'] ! ka)) [0..<k] @
              map (\<lambda>ka. Gs ka (p[k := l'] ! ka)) [k..<length p]\<close>
            using CRam_succeed
            by (force dest: upt_add_eq_append[OF le0 less_imp_le_nat])
          show ?thesis
            using CRam_succeed
            by (simp add: s0 s1 s2 iterated_sepconj_append_split sepconj_assoc upt_conv_Cons)
        qed
        finally show ?thesis
          using CRam_succeed
          by (force simp add: opsem_ram_comm_same_resources)
      qed
    qed
  next
    case (CRelease k r l')
    show ?thesis
    proof (rule opsem_prog_iter_smallstep_step.hyps)
      show \<open>\<forall>k<length p'. semantic_proof (Cs k) (Gs k) I T\<close>
        using CRelease opsem_prog_iter_smallstep_step.prems
        by simp

      show \<open>os'' = Some s''\<close>
        using opsem_prog_iter_smallstep_step.prems
        by simp

      have sem_proof_step:
        \<open>r < length I\<close>
        \<open>Gs k (p ! k) \<le> Gs k l' \<^emph> I ! r\<close>
        using CRelease opsem_prog_iter_smallstep_step.prems(1)
        by (force simp add: semantic_proof_def)+

      have
        \<open>iterated_sepconj (map (\<lambda>j. Gs j (p ! j)) [0..<length p]) \<^emph>
          iterated_sepconj (active_resource_invs I fR)
        \<le> iterated_sepconj (map (\<lambda>j. Gs j (p[k := l'] ! j)) [0..<length p]) \<^emph>
          iterated_sepconj (active_resource_invs I fR')\<close>
      proof -
        have
          \<open>iterated_sepconj (map (\<lambda>j. Gs j (p ! j)) [0..<length p]) \<^emph>
            iterated_sepconj (active_resource_invs I fR)
          \<le>
            (iterated_sepconj (map (\<lambda>j. Gs j (p ! j)) [0..<k]) \<^emph>
            Gs k (p ! k) \<^emph>
            iterated_sepconj (map (\<lambda>j. Gs j (p ! j)) [Suc k..<length p])) \<^emph>
            (iterated_sepconj (take r (active_resource_invs I fR)) \<^emph>
            emp \<^emph>
            iterated_sepconj (drop (Suc r) (active_resource_invs I fR)))\<close>
          using CRelease sem_proof_step
          by (clarsimp simp add:
              iterated_sepconj_map_range_split_at
              iterated_sepconj_take_drop_split_at[where xs=\<open>active_resource_invs _ _\<close>])
        also have \<open>... \<le>
          Gs k (p ! k) \<^emph>
          (iterated_sepconj (map (\<lambda>j. Gs j (p ! j)) [0..<k]) \<^emph>
          iterated_sepconj (map (\<lambda>j. Gs j (p ! j)) [Suc k..<length p])) \<^emph>
          (iterated_sepconj (take r (active_resource_invs I fR)) \<^emph>
          iterated_sepconj (drop (Suc r) (active_resource_invs I fR)))\<close>
          by (simp add: upt_conv_Cons sepconj_ac)
        also have \<open>... \<le>
          Gs k l' \<^emph> I ! r \<^emph>
          (iterated_sepconj (map (\<lambda>j. Gs j (p ! j)) [0..<k]) \<^emph>
          iterated_sepconj (map (\<lambda>j. Gs j (p ! j)) [Suc k..<length p])) \<^emph>
          (iterated_sepconj (take r (active_resource_invs I fR)) \<^emph>
          iterated_sepconj (drop (Suc r) (active_resource_invs I fR)))\<close>
          using sem_proof_step
          by (simp add: sepconj_left_mono)
        also have \<open>... \<le>
          iterated_sepconj (map (\<lambda>j. Gs j (p[k := l'] ! j)) [0..<length p]) \<^emph>
          iterated_sepconj (active_resource_invs I fR')\<close>
        proof -
          have s0: \<open>map (\<lambda>ka. Gs ka (p[k := l'] ! ka)) [0..<k] = map (\<lambda>ka. Gs ka (p ! ka)) [0..<k]\<close>
            by simp
          have s1: \<open>
          map (\<lambda>ka. Gs ka (p[k := l'] ! ka)) [Suc k..<length p] =
          map (\<lambda>ka. Gs ka (p ! ka)) [Suc k..<length p]\<close>
            by simp
          have s2:
            \<open>iterated_sepconj (take r (active_resource_invs I fR))
              = iterated_sepconj (take r (active_resource_invs I fR'))\<close>
            using CRelease
            by (force intro: arg_cong[where f=iterated_sepconj] simp add: list_eq_iff_nth_eq)
          have s3:
            \<open>iterated_sepconj (drop (Suc r) (active_resource_invs I fR))
              = iterated_sepconj (drop (Suc r) (active_resource_invs I fR'))\<close>
            using CRelease
            by (force intro: arg_cong[where f=iterated_sepconj] simp add: list_eq_iff_nth_eq)
          show ?thesis
            using CRelease sem_proof_step
            by (simp add: sepconj_ac  s0 s1 s2 s3
                iterated_sepconj_map_range_split_at
                iterated_sepconj_take_drop_split_at[where k=r])
        qed
        finally show ?thesis
          by blast
      qed
      then show
        \<open>(iterated_sepconj (map (\<lambda>k. Gs k (p' ! k)) [0..<length p']) \<^emph>
          iterated_sepconj (active_resource_invs I fR')) s'\<close>
        using CRelease opsem_prog_iter_smallstep_step.prems
          length_list_update predicate1D
        by auto
  qed
  next
    case (CAcquire k r l')
    show ?thesis
    proof (rule opsem_prog_iter_smallstep_step.hyps)
      show \<open>\<forall>k<length p'. semantic_proof (Cs k) (Gs k) I T\<close>
        using CAcquire opsem_prog_iter_smallstep_step.prems
        by simp

      show \<open>os'' = Some s''\<close>
        using opsem_prog_iter_smallstep_step.prems
        by simp

      have sem_proof_step:
        \<open>r < length I\<close>
        \<open>Gs k (p ! k) \<^emph> I ! r \<le> Gs k l'\<close>
        using CAcquire opsem_prog_iter_smallstep_step.prems(1)
        by (force simp add: semantic_proof_def)+

      have
        \<open>iterated_sepconj (map (\<lambda>j. Gs j (p ! j)) [0..<length p]) \<^emph>
          iterated_sepconj (active_resource_invs I fR)
        \<le> iterated_sepconj (map (\<lambda>j. Gs j (p[k := l'] ! j)) [0..<length p]) \<^emph>
          iterated_sepconj (active_resource_invs I fR')\<close>
      proof -
        have
          \<open>iterated_sepconj (map (\<lambda>j. Gs j (p ! j)) [0..<length p]) \<^emph>
            iterated_sepconj (active_resource_invs I fR)
          \<le>
            (iterated_sepconj (map (\<lambda>j. Gs j (p ! j)) [0..<k]) \<^emph>
            Gs k (p ! k) \<^emph>
            iterated_sepconj (map (\<lambda>j. Gs j (p ! j)) [Suc k..<length p])) \<^emph>
            (iterated_sepconj (take r (active_resource_invs I fR)) \<^emph>
            I ! r \<^emph>
            iterated_sepconj (drop (Suc r) (active_resource_invs I fR)))\<close>
          using CAcquire sem_proof_step
          by (clarsimp simp add:
              iterated_sepconj_map_range_split_at
              iterated_sepconj_take_drop_split_at[where xs=\<open>active_resource_invs _ _\<close>])
        also have \<open>... \<le>
          Gs k (p ! k) \<^emph> I ! r \<^emph>
          (iterated_sepconj (map (\<lambda>j. Gs j (p ! j)) [0..<k]) \<^emph>
          iterated_sepconj (map (\<lambda>j. Gs j (p ! j)) [Suc k..<length p])) \<^emph>
          (iterated_sepconj (take r (active_resource_invs I fR)) \<^emph>
          iterated_sepconj (drop (Suc r) (active_resource_invs I fR)))\<close>
          by (simp add: upt_conv_Cons sepconj_ac)
        also have \<open>... \<le>
          Gs k l' \<^emph>
          (iterated_sepconj (map (\<lambda>j. Gs j (p ! j)) [0..<k]) \<^emph>
          iterated_sepconj (map (\<lambda>j. Gs j (p ! j)) [Suc k..<length p])) \<^emph>
          (iterated_sepconj (take r (active_resource_invs I fR)) \<^emph>
          iterated_sepconj (drop (Suc r) (active_resource_invs I fR)))\<close>
          using sem_proof_step
          by (simp add: sepconj_left_mono)
        also have \<open>... \<le>
          iterated_sepconj (map (\<lambda>j. Gs j (p[k := l'] ! j)) [0..<length p]) \<^emph>
          iterated_sepconj (active_resource_invs I fR')\<close>
        proof -
          have s0: \<open>map (\<lambda>ka. Gs ka (p[k := l'] ! ka)) [0..<k] = map (\<lambda>ka. Gs ka (p ! ka)) [0..<k]\<close>
            by simp
          have s1: \<open>
          map (\<lambda>ka. Gs ka (p[k := l'] ! ka)) [Suc k..<length p] =
          map (\<lambda>ka. Gs ka (p ! ka)) [Suc k..<length p]\<close>
            by simp
          have s2:
            \<open>iterated_sepconj (take r (active_resource_invs I fR))
              = iterated_sepconj (take r (active_resource_invs I fR'))\<close>
            using CAcquire
            by (force intro: arg_cong[where f=iterated_sepconj] simp add: list_eq_iff_nth_eq)
          have s3:
            \<open>iterated_sepconj (drop (Suc r) (active_resource_invs I fR))
              = iterated_sepconj (drop (Suc r) (active_resource_invs I fR'))\<close>
            using CAcquire
            by (force intro: arg_cong[where f=iterated_sepconj] simp add: list_eq_iff_nth_eq)
          show ?thesis
            using CAcquire sem_proof_step
            by (simp add: sepconj_ac s0 s1 s2 s3
              iterated_sepconj_map_range_split_at
              iterated_sepconj_take_drop_split_at[where k=r])
        qed
        finally show ?thesis
          by blast
      qed
      then show
        \<open>(iterated_sepconj (map (\<lambda>k. Gs k (p' ! k)) [0..<length p']) \<^emph>
          iterated_sepconj (active_resource_invs I fR')) s'\<close>
        using CAcquire opsem_prog_iter_smallstep_step.prems
          length_list_update predicate1D
        by auto
  qed
qed
