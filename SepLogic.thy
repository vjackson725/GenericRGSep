theory SepLogic
  imports Main "HOL-Library.Lattice_Syntax"
begin

lemma bool_left_mp[simp]: \<open>P \<and> (P \<longrightarrow> Q) \<longleftrightarrow> P \<and> Q\<close>
  by blast

lemma bool_right_mp[simp]: \<open>(P \<longrightarrow> Q) \<and> P \<longleftrightarrow> P \<and> Q\<close>
  by blast

lemma exsome_conj_some_imp:
  \<open>(\<exists>x. y = Some x) \<and> (\<forall>x. y = Some x \<longrightarrow> P x) \<longleftrightarrow> (\<exists>x. y = Some x \<and> P x)\<close>
  by blast

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

lemmas bij_betw_disjoint_insert =
  bij_betw_disjoint_Un[where A=\<open>{b}\<close> and C=\<open>{d}\<close> for b d, simplified]

lemma bij_betw_insert_ignore:
  \<open>bij_betw f B D \<Longrightarrow> b \<in> B \<Longrightarrow> d \<in> D \<Longrightarrow> bij_betw f (insert b B) (insert d D)\<close>
  by (simp add: insert_absorb)

lemma bij_betw_singleton:
  \<open>f a = b \<Longrightarrow> bij_betw f {a} {b}\<close>
  by (simp add: bij_betw_def)

lemmas bij_betw_combine_insert =
  bij_betw_combine[where A=\<open>{b}\<close> and B=\<open>{d}\<close> for b d, simplified]


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

lemma map_disjoint_dom_cancel_right:
  assumes disjoint_ac: \<open>dom a \<inter> dom c = {}\<close>
    and disjoint_ac: \<open>dom b \<inter> dom c = {}\<close>
  shows \<open>(a ++ c = b ++ c) \<longleftrightarrow> a = b\<close>
  using assms
  by (metis (no_types, lifting) Int_Un_distrib Int_commute Un_Int_eq(3)
      disjoint_ac dom_map_add map_add_comm map_le_iff_map_add_commute map_le_restrict_eq)

lemma map_disjoint_dom_cancel_left:
  assumes disjoint_ac: \<open>dom a \<inter> dom b = {}\<close>
    and disjoint_ac: \<open>dom a \<inter> dom c = {}\<close>
  shows \<open>(a ++ b = a ++ c) \<longleftrightarrow> b = c\<close>
  using assms
  by (metis (no_types, lifting) Int_Un_distrib Int_commute Un_Int_eq(3)
      disjoint_ac dom_map_add map_add_comm map_le_iff_map_add_commute map_le_restrict_eq)


section \<open>Predicate Logic\<close>

definition pred_false :: \<open>'a \<Rightarrow> bool\<close> (\<open>\<^bold>F\<close>) where
  \<open>\<^bold>F \<equiv> \<lambda>x. False\<close>

definition pred_true :: \<open>'a \<Rightarrow> bool\<close> (\<open>\<^bold>T\<close>) where
  \<open>\<^bold>T \<equiv> \<lambda>x. True\<close>

definition pred_neg :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> (\<open>\<^bold>\<not> _\<close> [89] 90) where
  \<open>\<^bold>\<not> p \<equiv> \<lambda>x. \<not> p x\<close>

definition pred_conj :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> (infixr \<open>\<^bold>\<and>\<close> 86) where
  \<open>p \<^bold>\<and> q \<equiv> \<lambda>x. p x \<and> q x\<close>

definition pred_disj :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> (infixr \<open>\<^bold>\<or>\<close> 84) where
  \<open>p \<^bold>\<or> q \<equiv> \<lambda>x. p x \<or> q x\<close>

definition pred_impl :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> (infixr \<open>\<^bold>\<longrightarrow>\<close> 82) where
  \<open>p \<^bold>\<longrightarrow> q \<equiv> \<lambda>x. p x \<longrightarrow> q x\<close>


lemma pred_conj_simp:
  \<open>(p \<^bold>\<and> q) x \<longleftrightarrow> p x \<and> q x\<close>
  by (simp add: pred_conj_def)

lemma pred_disj_simp:
  \<open>(p \<^bold>\<or> q) x \<longleftrightarrow> p x \<or> q x\<close>
  by (simp add: pred_disj_def)


lemma pred_conjD: \<open>(A1 \<^bold>\<and> A2) s \<Longrightarrow> A1 \<le> B1 \<Longrightarrow> A2 \<le> B2 \<Longrightarrow> (B1 \<^bold>\<and> B2) s\<close>
  by (metis pred_conj_def predicate1D)

lemma pred_conj_left_imp: \<open>A \<^bold>\<and> B \<le> A\<close>
  by (metis pred_conj_def predicate1I)

lemma pred_conj_right_imp: \<open>A \<^bold>\<and> B \<le> B\<close>
  by (metis pred_conj_def predicate1I)

lemma pred_disj_left_imp: \<open>A \<le> A \<^bold>\<or> B\<close>
  by (metis pred_disj_def predicate1I)

lemma pred_disj_right_imp: \<open>B \<le> A \<^bold>\<or> B\<close>
  by (metis pred_disj_def predicate1I)

lemma pred_abac_eq_abc: \<open>(A \<^bold>\<and> B) \<^bold>\<and> A \<^bold>\<and> C = A \<^bold>\<and> B \<^bold>\<and> C\<close>
  by (force simp add: pred_conj_def)


section \<open> Separation Logic \<close>

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

definition subheapexist :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> where
  \<open>subheapexist P \<equiv> \<lambda>h. \<exists>h1. h1 \<le> h \<and> P h1\<close>

definition sepimp :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> (infixr \<open>\<midarrow>\<^emph>\<close> 85) where
  \<open>P \<midarrow>\<^emph> Q \<equiv> \<lambda>h. \<forall>h1. h \<currency> h1 \<longrightarrow> P h1 \<longrightarrow> Q (h + h1)\<close>

definition sepcoimp :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> (infixr \<open>\<sim>\<^emph>\<close> 85) where
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

lemma sepconj_comm_imp:
  \<open>P \<^emph> Q \<le> Q \<^emph> P\<close>
  by (simp add: sepconj_comm)


definition precise :: \<open>('a \<Rightarrow> bool) \<Rightarrow> bool\<close> where
  \<open>precise P \<equiv> \<forall>h h1. h1\<le>h \<longrightarrow> P h1 \<longrightarrow> (\<forall>h2\<le>h. P h2 \<longrightarrow> h1 = h2)\<close>

definition intuitionistic :: \<open>('a \<Rightarrow> bool) \<Rightarrow> bool\<close> where
  \<open>intuitionistic P \<equiv> \<forall>h h'. P h \<and> h \<le> h' \<longrightarrow> P h'\<close>


lemma strong_sepcoimp_imp_sepconj:
  \<open>(P \<^emph> \<^bold>T) \<^bold>\<and> (P \<sim>\<^emph> Q) \<le> P \<^emph> Q\<close>
  by (force simp add: sepconj_def sepcoimp_def precise_def le_fun_def le_iff_sepadd pred_conj_def pred_true_def)

lemma secoimp_imp_sepconj:
  \<open>P \<^bold>\<and> (P \<sim>\<^emph> Q) \<le> P \<^emph> (Q \<^bold>\<and> emp)\<close>
  unfolding pred_conj_def sepcoimp_def sepconj_def le_fun_def le_bool_def emp_def
  by (metis disjoint_empty_right sep_add_0_right)

lemma sepconj_pdisj_distrib_left: \<open>P \<^emph> (Q1 \<^bold>\<or> Q2) = P \<^emph> Q1 \<^bold>\<or> P \<^emph> Q2\<close>
  by (force simp add: sepconj_def pred_disj_def)

lemma sepcoimp_pconj_distrib_left:
  \<open>P \<sim>\<^emph> (Q \<^bold>\<and> Q') = (P \<sim>\<^emph> Q) \<^bold>\<and> (P \<sim>\<^emph> Q')\<close>
  by (force simp add: pred_conj_def sepcoimp_def)

lemma not_coimp_emp:
  \<open>h \<noteq> 0 \<Longrightarrow> (\<^bold>\<not> (\<^bold>T \<sim>\<^emph> emp)) h\<close>
  apply (clarsimp simp add: pred_true_def pred_neg_def sepcoimp_def emp_def)
  apply (rule_tac x=0 in exI, force)
  done

lemma sepconj_distrib_conj_iff_sepconj_eq_strong_sepcoimp:
  shows \<open>(\<forall>Q Q'. P \<^emph> (Q \<^bold>\<and> Q') = (P \<^emph> Q) \<^bold>\<and> (P \<^emph> Q')) \<longleftrightarrow> (\<forall>Q. P \<^emph> Q = (P \<^emph> \<^bold>T) \<^bold>\<and> (P \<sim>\<^emph> Q))\<close>
  apply (clarsimp simp add: sepconj_def sepcoimp_def precise_def le_fun_def le_iff_sepadd pred_conj_def pred_true_def)
  apply (intro iffI)
   apply (rule allI)
   apply (rule ext)
   apply (rule iffI)
    apply (rule conjI)
     apply blast
    apply clarsimp
    apply (drule_tac x=\<open>Q\<close> in spec)
    apply (drule_tac x=\<open>(=) h2a\<close> in spec)
    apply (drule_tac x=\<open>h1a + h2a\<close> in cong[OF _ refl])
    apply fastforce
   apply fastforce

  apply clarsimp
  apply (rule ext)
  apply (rule iffI)
   apply blast
  apply clarsimp
  apply (frule_tac x=Q in spec, drule_tac x=\<open>h1a + h2a\<close> in cong[OF _ refl])
  apply (drule_tac x=Q' in spec, drule_tac x=\<open>h1a + h2a\<close> in cong[OF _ refl])
  apply metis
  done


lemma sepconj_distrib_conj_imp_sepconj_eq_strong_sepcoimp:
  assumes \<open>\<forall>Q Q'. P \<^emph> (Q \<^bold>\<and> Q') = (P \<^emph> Q) \<^bold>\<and> (P \<^emph> Q')\<close>
  shows \<open>P \<^emph> Q = (P \<^emph> \<^bold>T) \<^bold>\<and> (P \<sim>\<^emph> Q)\<close>
  using assms sepconj_distrib_conj_iff_sepconj_eq_strong_sepcoimp
  by blast

lemma sepconj_middle_monotone_left: \<open>A1 \<^emph> A2 \<le> B \<Longrightarrow> A1 \<^emph> C \<^emph> A2 \<le> C \<^emph> B\<close>
  by (metis sepconj_assoc sepconj_comm sepconj_left_mono)

lemma sepconj_middle_monotone_right: \<open>A \<le> B1 \<^emph> B2 \<Longrightarrow> C \<^emph> A \<le> B1 \<^emph> C \<^emph> B2\<close>
  by (metis sepconj_assoc sepconj_comm sepconj_left_mono)


end



class right_cancel_seplogic = seplogic +
  assumes partial_right_cancel: \<open>\<And>a b c. a \<currency> b \<Longrightarrow> a \<currency> c \<Longrightarrow> (b + a = c + a) = (b = c)\<close>
begin

lemma precise_iff_conj_distrib:
  shows \<open>precise P \<longleftrightarrow> (\<forall>Q Q'. P \<^emph> (Q \<^bold>\<and> Q') = (P \<^emph> Q) \<^bold>\<and> (P \<^emph> Q'))\<close>
proof (rule iffI)
  assume distrib_assm: \<open>\<forall>Q Q'. P \<^emph> (Q \<^bold>\<and> Q') = (P \<^emph> Q) \<^bold>\<and> (P \<^emph> Q')\<close>
  show \<open>precise P\<close>
  proof (clarsimp simp add: precise_def le_iff_sepadd)
    fix h1 h1' h2 h2'
    presume precise_assms:
      \<open>h1 + h1' = h2 + h2'\<close>
      \<open>h1 \<currency> h1'\<close>
      \<open>h2 \<currency> h2'\<close>
      \<open>P h1\<close>
      \<open>P h2\<close>

    have \<open>(P \<^emph> ((=) h1')) (h2+h2')\<close>
      using precise_assms partial_add_commute disjoint_symm sepconj_def
      by auto
    moreover have \<open>(P \<^emph> ((=) h2')) (h2+h2')\<close>
      using precise_assms partial_add_commute disjoint_symm sepconj_def
      by auto
    ultimately have \<open>(P \<^emph> (\<lambda>h. h1' = h \<and> h2' = h)) (h2+h2')\<close>
      using distrib_assm precise_assms
      by (simp add: pred_conj_def)
    then show \<open>h1 = h2\<close>
      using precise_assms disjoint_symm partial_right_cancel
      unfolding sepconj_def
      by fastforce
  qed
next
  presume precise_assm:  \<open>precise P\<close>
  then show \<open>\<forall>Q Q'. P \<^emph> (Q \<^bold>\<and> Q') = (P \<^emph> Q) \<^bold>\<and> (P \<^emph> Q')\<close>
    apply (auto simp add: sepconj_def precise_def pred_conj_def fun_eq_iff le_iff_sepadd)
    apply (metis partial_add_commute partial_right_cancel)
    done
qed

lemma precise_iff_all_sepconj_imp_sepcoimp:
  shows \<open>precise P \<longleftrightarrow> (\<forall>Q. P \<^emph> Q \<le> P \<sim>\<^emph> Q)\<close>
  apply (clarsimp simp add: sepconj_def sepcoimp_def precise_def le_fun_def le_iff_sepadd)
  apply (rule iffI)
   apply (metis partial_right_cancel partial_add_commute)
  apply clarsimp
  apply (rename_tac a b c d)
  apply (drule_tac x=\<open>(=) b\<close> in spec, metis partial_right_cancel disjoint_symm)
  done

lemma precise_sepconj_eq_strong_sepcoimp:
  shows \<open>precise P \<Longrightarrow> P \<^emph> Q = (P \<^emph> \<^bold>T) \<^bold>\<and> (P \<sim>\<^emph> Q)\<close>
  apply (clarsimp simp add: sepconj_def sepcoimp_def precise_def le_fun_def le_iff_sepadd pred_conj_def pred_true_def)
  apply (rule ext)
  apply (rule iffI)
   apply (metis partial_right_cancel partial_add_commute)
  apply metis
  done

end

end