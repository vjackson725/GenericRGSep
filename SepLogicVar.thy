theory SepLogicVar
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
    and ac_eq_bc: \<open>a ++ c = b ++ c\<close>
  shows \<open>a = b\<close>
  using assms
  by (metis (no_types, lifting) Int_Un_distrib Int_commute Un_Int_eq(3) ac_eq_bc
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

lemma strong_sepcoimp_imp_sepconj:
  \<open>(P \<^emph> \<^bold>T) \<^bold>\<and> (P \<sim>\<^emph> Q) \<le> P \<^emph> Q\<close>
  by (force simp add: sepconj_def sepcoimp_def precise_def le_fun_def le_iff_sepadd pred_conj_def pred_true_def)

lemma secoimp_imp_sepconj:
  \<open>P \<^bold>\<and> (P \<sim>\<^emph> Q) \<le> P \<^emph> (Q \<^bold>\<and> emp)\<close>
  unfolding pred_conj_def sepcoimp_def sepconj_def le_fun_def le_bool_def emp_def
  by (metis disjoint_empty_right sep_add_0_right)

lemma sepcoimp_conj_distrib_left:
  \<open>P \<sim>\<^emph> (Q \<^bold>\<and> Q') = (P \<sim>\<^emph> Q) \<^bold>\<and> (P \<sim>\<^emph> Q')\<close>
  by (force simp add: pred_conj_def sepcoimp_def)

lemma not_coimp_emp:
  \<open>h \<noteq> 0 \<Longrightarrow> (\<^bold>\<not> (\<^bold>T \<sim>\<^emph> emp)) h\<close>
  apply (clarsimp simp add: pred_true_def pred_neg_def sepcoimp_def emp_def)
  apply (rule_tac x=0 in exI, force)
  done

lemma sepconj_distrib_conj_eq_strong_sepcoimp:
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

lemma the_varenv_inject:
  \<open>the_varenv a = the_varenv b \<longleftrightarrow> a = b\<close>
  by (metis varenv.exhaust_sel)
lemma the_heap_inject:
  \<open>the_heap a = the_heap b \<longleftrightarrow> a = b\<close>
  by (metis heap.exhaust_sel)
lemma the_resources_inject:
  \<open>the_resources a = the_resources b \<longleftrightarrow> a = b\<close>
  by (metis resources.exhaust_sel)

type_synonym 'v state = \<open>'v varenv \<times> heap \<times> resources\<close>

fun denot_iexpr :: \<open>'v iexpr \<Rightarrow> (('v \<rightharpoonup> nat) \<rightharpoonup> nat)\<close> (\<open>\<lbrakk>_\<rbrakk>\<^sub>I _\<close> [51,51] 51) where
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
| \<open>\<lbrakk>e\<rbrakk>\<^sub>I s = Some p \<Longrightarrow> h p = None \<Longrightarrow> (VarEnv s, Heap h, r), CHeapDel e \<leadsto> None\<close>
| \<open>\<lbrakk>e\<rbrakk>\<^sub>I s = None \<Longrightarrow> (VarEnv s, Heap h, r), CHeapDel e \<leadsto> None\<close>
| \<open>\<lbrakk>b\<rbrakk>\<^sub>B s = Some True \<Longrightarrow> (VarEnv s, h, r), CAssume b \<leadsto> Some (VarEnv s, h, r)\<close>

inductive_cases opsem_ram_comm_CSkipE[elim!]: \<open>s, CSkip \<leadsto> s'\<close>
inductive_cases opsem_ram_comm_CAssignE[elim!]: \<open>s, CAssign x e \<leadsto> s'\<close>
inductive_cases opsem_ram_comm_CHeapRE[elim]: \<open>s, CHeapR x e \<leadsto> s'\<close>
inductive_cases opsem_ram_comm_CHeapWE[elim!]: \<open>s, CHeapW ep e \<leadsto> s'\<close>
inductive_cases opsem_ram_comm_CHeapNewE[elim]: \<open>s, CHeapNew x \<leadsto> s'\<close>
inductive_cases opsem_ram_comm_CHeapDelE[elim]: \<open>s, CHeapDel e \<leadsto> s'\<close>
inductive_cases opsem_ram_comm_CAssumeE[elim!]: \<open>s, CAssume b \<leadsto> s'\<close>

lemma opsem_ram_comm_simps:
  \<open>s, CSkip \<leadsto> os' \<longleftrightarrow> os' = Some s\<close>
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
            (case h p of None \<Rightarrow> os' = None
            | Some x \<Rightarrow> os' = Some (VarEnv v, Heap (h(p := None)), r))))\<close>
    apply (simp split: option.splits)
    apply (rule iffI)
      (* Part 1 *)
     apply (erule opsem_ram_comm_CHeapDelE)
       apply (clarsimp, metis not_Some_eq option.inject)
      apply (force simp add: the_heap_eq_iff[symmetric] split: option.splits)
    apply (metis Heap_always_ex option.simps(3))
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


subsubsection \<open>Seplogic Instances\<close>

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

subsubsection \<open>Right Cancellative Seplogic Instances\<close>

instantiation varenv :: (type) right_cancel_seplogic
begin

instance
proof
  fix a b c :: \<open>'a varenv\<close>
  show \<open>a \<currency> b \<Longrightarrow> a \<currency> c \<Longrightarrow> (b + a = c + a) = (b = c)\<close>
    unfolding disjoint_varenv_def plus_varenv_def
    by (metis inf_commute map_disjoint_dom_cancel_right varenv.expand varenv.inject)
qed

end

instantiation heap :: right_cancel_seplogic
begin

instance
proof
  fix a b c :: heap
  show \<open>a \<currency> b \<Longrightarrow> a \<currency> c \<Longrightarrow> (b + a = c + a) = (b = c)\<close>
    unfolding disjoint_heap_def plus_heap_def
    by (metis heap.expand heap.inject inf_commute map_disjoint_dom_cancel_right)
qed

end

instantiation resources :: right_cancel_seplogic
begin

instance
proof
  fix a b c :: resources
  show \<open>a \<currency> b \<Longrightarrow> a \<currency> c \<Longrightarrow> (b + a = c + a) = (b = c)\<close>
    unfolding disjoint_resources_def plus_resources_def
    by (metis Int_Un_distrib Un_Int_eq(3) inf_commute resources.expand resources.inject)
qed

end

instantiation prod :: (right_cancel_seplogic,right_cancel_seplogic) right_cancel_seplogic
begin

instance
proof
  fix a b c :: \<open>'a \<times> 'b\<close>
  show \<open>a \<currency> b \<Longrightarrow> a \<currency> c \<Longrightarrow> (b + a = c + a) = (b = c)\<close>
    by (simp add: partial_right_cancel prod_eq_iff)
qed

end



lemma varenv_disjoint_map_appendI:
  \<open>VarEnv v1 \<currency> v2 \<Longrightarrow> x \<notin> dom (the_varenv v2) \<Longrightarrow> VarEnv (v1(x := a)) \<currency> v2\<close>
  by (simp add: disjoint_varenv_def Diff_Int_distrib2 subset_singleton_iff)


section \<open>ram_comm Forward predicate transformer\<close>

definition ram_comm_forward :: \<open>'v ram_comm \<Rightarrow> ('v state \<Rightarrow> bool) \<Rightarrow> ('v state \<Rightarrow> bool)\<close> where
  \<open>ram_comm_forward c \<equiv> \<lambda>P. \<lambda>s'. \<exists>s. P s \<and> s, c \<leadsto> Some s'\<close>

lemma ram_comm_step_iff_forward:
  \<open>(s, c \<leadsto> Some s') \<longleftrightarrow> (=) s' \<le> ram_comm_forward c ((=) s)\<close>
  by (simp add: ram_comm_forward_def le_fun_def prod_eq_decompose)

lemma ram_comm_forward_simps:
  \<open>ram_comm_forward CSkip P = P\<close>
  \<open>ram_comm_forward (CAssign x e0) P =
    (\<lambda>(v, h, r). \<exists>v'. v = VarEnv ((the_varenv v')(x := \<lbrakk>e0\<rbrakk>\<^sub>I (the_varenv v'))) \<and> P (v', h, r))\<close>
  \<open>ram_comm_forward (CHeapR x ep) P =
    (\<lambda>(v, h, r). \<exists>v' p.
      \<lbrakk>ep\<rbrakk>\<^sub>I (the_varenv v') = Some p \<and> v = VarEnv ((the_varenv v')(x := the_heap h p)) \<and> P (v', h, r)
    )\<close>
  \<open>ram_comm_forward (CHeapW ep e) P =
    (\<lambda>(v, h, r). \<exists>h' p.
      \<lbrakk>ep\<rbrakk>\<^sub>I (the_varenv v) = Some p \<and> h = Heap ((the_heap h')(p := \<lbrakk>e\<rbrakk>\<^sub>I (the_varenv v))) \<and> P (v, h', r)
    )\<close>
  \<open>ram_comm_forward (CHeapNew x) P =
    (\<lambda>(v', h', r). \<exists>v h p.
      P (VarEnv v, Heap h, r) \<and>
      h p = None \<and>
      v' = VarEnv (v(x \<mapsto> p)) \<and>
      h' = Heap (h(p \<mapsto> undefined))
    )\<close>
  \<open>ram_comm_forward (CHeapDel e) P =
    (\<lambda>(v, h', r).
      \<exists>h p.
        P (v, h, r) \<and>
        \<lbrakk>e\<rbrakk>\<^sub>I the_varenv v = Some p \<and>
        the_heap h p \<noteq> None \<and>
        h' = Heap ((the_heap h)(p := None)))\<close>
  \<open>ram_comm_forward (CAssume be) P = (\<lambda>(s, h, r). P (s, h, r) \<and> (\<lbrakk> be \<rbrakk>\<^sub>B (the_varenv s) = Some True))\<close>
proof -
  {
    fix v' h' r'
    have \<open>
      (\<exists>v h r.
        P (v, h, r) \<and>
        (\<exists>vm. v = VarEnv vm \<and>
          (\<exists>y. \<lbrakk>e\<rbrakk>\<^sub>I vm = Some y) \<and>
          (\<exists>hm. \<forall>x2. (hm x2 = None \<longrightarrow> \<lbrakk>e\<rbrakk>\<^sub>I vm \<noteq> Some x2) \<and>
          ((\<exists>x2a. hm x2 = Some x2a) \<longrightarrow>
            \<lbrakk>e\<rbrakk>\<^sub>I vm = Some x2 \<longrightarrow>
            h = Heap hm \<and> v' = VarEnv vm \<and> h' = Heap (hm(x2 := None)) \<and> r' = r)))) \<longleftrightarrow>
      (\<exists>vm hm p.
        P (VarEnv vm, Heap hm, r') \<and>
        \<lbrakk>e\<rbrakk>\<^sub>I vm = Some p \<and>
          (\<forall>p'. \<lbrakk>e\<rbrakk>\<^sub>I vm = Some p' \<longrightarrow> hm p' \<noteq> None) \<and>
          (\<forall>p'. \<lbrakk>e\<rbrakk>\<^sub>I vm = Some p' \<longrightarrow>
            (\<forall>a. hm p' = Some a \<longrightarrow> v' = VarEnv vm \<and> h' = Heap (hm(p' := None)))))
    \<close> (is \<open>?lhs = _\<close>)
      by blast
    also have \<open>... \<longleftrightarrow>
      (\<exists>vm hm p a.
        P (VarEnv vm, Heap hm, r') \<and>
        \<lbrakk>e\<rbrakk>\<^sub>I vm = Some p \<and>
        hm p = Some a \<and>
        v' = VarEnv vm \<and> h' = Heap (hm(p := None)))
    \<close> (is \<open>_ = ?rhs\<close>)
      by fastforce
    finally have \<open>?lhs = ?rhs\<close> .
  }
  note s0 = this

  show \<open>ram_comm_forward (CHeapDel e) P =
    (\<lambda>(v, h', r). \<exists>h p.
      P (v, h, r) \<and>
      \<lbrakk>e\<rbrakk>\<^sub>I the_varenv v = Some p \<and>
      the_heap h p \<noteq> None \<and>
      h' = Heap ((the_heap h)(p := None)))\<close>
    unfolding ram_comm_forward_def
    by (force simp add: s0 fun_eq_iff opsem_ram_comm_simps split: option.splits)
qed (force simp add: ram_comm_forward_def fun_eq_iff opsem_ram_comm_simps split: option.splits)+

subsection \<open>Healthiness Conditions\<close>

lemma ram_comm_forward_mono:
  \<open>mono (ram_comm_forward c)\<close>
  unfolding mono_def ram_comm_forward_def le_fun_def
  by (simp, metis)

lemma ram_comm_forward_conj:
  \<open>ram_comm_forward c (P \<^bold>\<and> Q) \<le> (ram_comm_forward c P \<^bold>\<and> ram_comm_forward c Q)\<close>
  by (induct c)
     (force split: prod.splits simp add: ram_comm_forward_simps pred_conj_def)+

lemma ram_comm_forward_disj:
  \<open>ram_comm_forward c (P \<^bold>\<or> Q) = (ram_comm_forward c P \<^bold>\<or> ram_comm_forward c Q)\<close>
  by (induct c)
     (force simp add: ram_comm_forward_simps pred_disj_def)+

lemma ram_comm_forward_false:
  \<open>ram_comm_forward c \<^bold>F = \<^bold>F\<close>
  by (induct c)
     (force simp add: ram_comm_forward_simps pred_false_def)+


section \<open>Operational Semantics\<close>

definition transition_labels :: \<open>('l \<times> 'a \<times> 'l) set \<Rightarrow> 'l set\<close> where
  \<open>transition_labels T \<equiv> fst ` T \<union> (snd \<circ> snd) ` T\<close>

lemma transition_labels_include_start:
  \<open>(a,c,b) \<in> T \<Longrightarrow> a \<in> transition_labels T\<close>
  by (force simp add: transition_labels_def)

lemma transition_labels_include_end:
  \<open>(a,c,b) \<in> T \<Longrightarrow> b \<in> transition_labels T\<close>
  by (force simp add: transition_labels_def)

lemmas transition_labels_include_startend =
  transition_labels_include_start
  transition_labels_include_end

lemma transition_labels_empty[simp]:
  \<open>transition_labels {} = {}\<close>
  by (force simp add: transition_labels_def)

lemma transition_labels_insert_eq[simp]:
  \<open>transition_labels (insert t T) = insert (fst t) (insert (snd (snd t)) (transition_labels T))\<close>
  by (force simp add: transition_labels_def)

lemma transition_labels_un_eq[simp]:
  \<open>transition_labels (T1 \<union> T2) = transition_labels T1 \<union> transition_labels T2\<close>
  by (force simp add: transition_labels_def)

lemma transition_labels_disjoint_then_transitions_disjoint:
  \<open>transition_labels T1 \<inter> transition_labels T2 = {} \<Longrightarrow> T1 \<inter> T2 = {}\<close>
  by (force simp add: transition_labels_def)


inductive cfg :: \<open>'v comm \<Rightarrow> ('l \<times> 'v comm \<times> 'l) set \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> bool\<close> where
  cfg_skip: \<open>s \<noteq> e \<Longrightarrow> cfg (CRam c) {(s, CRam c, e)} s e\<close>
| cfg_seq:
  \<open>\<lbrakk> cfg c1 T1 s1 e1
   ; cfg c2 T2 s2 e2
   ; transition_labels T1 \<inter> transition_labels T2 = {}
   ; T = insert (e1, CRam CSkip, s2) (T1 \<union> T2)
   \<rbrakk> \<Longrightarrow> cfg (c1 ;; c2) T s1 e2\<close>
| cfg_ndet:
  \<open>\<lbrakk> cfg c1 T1 s1 e1
   ; cfg c2 T2 s2 e2
   ; transition_labels T1 \<inter> transition_labels T2 = {}
   ; s \<notin> transition_labels T1
   ; s \<notin> transition_labels T2
   ; e \<notin> transition_labels T1
   ; e \<notin> transition_labels T2
   ; s \<noteq> e
   ; T = {(s, CRam CSkip, s1), (s, CRam CSkip, s2), (e1, CRam CSkip, e), (e2, CRam CSkip, e)} \<union> (T1 \<union> T2)
   \<rbrakk> \<Longrightarrow> cfg (c1 \<box> c2) T s e\<close>
| cfg_loop:
  \<open>\<lbrakk> cfg c T' s' e'
   ; s \<notin> transition_labels T'
   ; e \<notin> transition_labels T'
   ; s \<noteq> e
   ; (e', CRam CSkip, s') \<notin> T'
   ; T = {(e', CRam CSkip, s'), (s, CRam CSkip, s'), (e', CRam CSkip, e)} \<union> T'
   \<rbrakk> \<Longrightarrow> cfg (c\<^sup>\<star>) T s e\<close>

inductive_cases cfg_CRamE[elim!]: \<open>cfg (CRam c) T s e\<close>
inductive_cases cfg_CSeqE[elim!]: \<open>cfg (c1 ;; c2) T s e\<close>
inductive_cases cfg_CNDetE[elim!]: \<open>cfg (c1 \<box> c2) T s e\<close>
inductive_cases cfg_CLoopE[elim!]: \<open>cfg (c\<^sup>\<star>) T s e\<close>


lemma cfg_simps:
  \<open>cfg (CRam cr) T s e \<longleftrightarrow> T = {(s, CRam cr, e)} \<and> s \<noteq> e\<close>
  \<open>cfg (c1 ;; c2) T s e \<longleftrightarrow> (\<exists>T1 T2 e1 s2.
    cfg c1 T1 s e1 \<and>
    cfg c2 T2 s2 e \<and>
    transition_labels T1 \<inter> transition_labels T2 = {} \<and>
    T = insert (e1, CRam CSkip, s2) (T1 \<union> T2)
  )\<close>
  \<open>cfg (c1 \<box> c2) T s e \<longleftrightarrow> s \<noteq> e \<and> (\<exists>T1 T2 s1 s2 e1 e2.
    cfg c1 T1 s1 e1 \<and>
    cfg c2 T2 s2 e2 \<and>
    transition_labels T1 \<inter> transition_labels T2 = {} \<and>
    s \<notin> transition_labels T1 \<and>
    e \<notin> transition_labels T1 \<and>
    s \<notin> transition_labels T2 \<and>
    e \<notin> transition_labels T2 \<and>
    T = {(s, CRam CSkip, s1), (s, CRam CSkip, s2), (e1, CRam CSkip, e), (e2, CRam CSkip, e)} \<union> T1 \<union> T2
  )\<close>
  \<open>cfg (c\<^sup>\<star>) T s e \<longleftrightarrow> s \<noteq> e \<and> (\<exists>T' s' e'.
    cfg c T' s' e' \<and>
    s \<notin> transition_labels T' \<and>
    e \<notin> transition_labels T' \<and>
    (e', CRam CSkip, s') \<notin> T' \<and>
    T = {(e', CRam CSkip, s'), (s, CRam CSkip, s'), (e', CRam CSkip, e)} \<union> T'
  )\<close>
     apply (blast intro: cfg.intros)
    apply (blast intro: cfg.intros)

   apply (rule iffI)
    apply (erule cfg_CNDetE, simp, blast)
   apply (blast intro: cfg.intros)

   apply (blast intro: cfg.intros)
  done

lemma cfg_transition_labels_include_start:
  \<open>cfg c T s e \<Longrightarrow> s \<in> transition_labels T\<close>
  by (induct rule: cfg.inducts)
    (force simp add: transition_labels_def)+

lemma cfg_transition_labels_include_end:
  \<open>cfg c T s e \<Longrightarrow> e \<in> transition_labels T\<close>
  by (induct rule: cfg.inducts)
    (force simp add: transition_labels_def)+

lemmas cfg_transition_labels_include_startend =
  cfg_transition_labels_include_start
  cfg_transition_labels_include_end


lemma cfg_transition_labels_start_not_end:
  \<open>cfg c T s e \<Longrightarrow> s \<noteq> e\<close>
proof (induct rule: cfg.inducts)
  case (cfg_seq c1 T1 s1 e1 c2 T2 s2 e2 T)
  then show ?case
    by (meson cfg_transition_labels_include_startend disjoint_iff_not_equal)
qed blast+


definition
  \<open>cfg_iso \<equiv> \<lambda>(Ta,sa,ea) (Tb,sb,eb).
    \<exists>f.
      bij_betw (\<lambda>(la,c,lb). (f la, c, f lb)) Ta Tb \<and>
      bij_betw f (transition_labels Ta) (transition_labels Tb) \<and>
      f sa = sb \<and>
      f ea = eb
  \<close>

lemma cfg_same_label_bij:
  assumes
    \<open>cfg c Ta sa ea\<close>
    \<open>cfg c Tb sb eb\<close>
  shows
    \<open>cfg_iso (Ta,sa,ea) (Tb,sb,eb)\<close>
  unfolding cfg_iso_def
  using assms
proof (induct arbitrary: Tb sb eb)
  case (cfg_skip sa ea ca)
  then show ?case
    apply simp
    apply (rule_tac x=\<open>\<lambda>l. if l = ea then eb else sb\<close> in exI)
    apply (force simp add: bij_betw_def)
    done
next
  case (cfg_seq c1 T1a s1a e1a c2 T2a s2a e2a Ta Tb s1b e2b)

  obtain T1b T2b e1b s2b
    where cfg_b:
       \<open>cfg c1 T1b s1b e1b\<close>
       \<open>cfg c2 T2b s2b e2b\<close>
       \<open>transition_labels T1b \<inter> transition_labels T2b = {}\<close>
       \<open>Tb = insert (e1b, CRam CSkip, s2b) (T1b \<union> T2b)\<close>
    using cfg_seq.prems by blast

  obtain f1
    where iso1:
      \<open>bij_betw (\<lambda>a. case a of (la, c, lb) \<Rightarrow> (f1 la, c, f1 lb)) T1a T1b\<close>
      \<open>bij_betw f1 (transition_labels T1a) (transition_labels T1b)\<close>
      \<open>f1 s1a = s1b\<close>
      \<open>f1 e1a = e1b\<close>
    using cfg_b cfg_seq.hyps by blast

  obtain f2
    where iso2:
      \<open>bij_betw (\<lambda>a. case a of (la, c, lb) \<Rightarrow> (f2 la, c, f2 lb)) T2a T2b\<close>
      \<open>bij_betw f2 (transition_labels T2a) (transition_labels T2b)\<close>
      \<open>f2 s2a = s2b\<close>
      \<open>f2 e2a = e2b\<close>
    using cfg_b cfg_seq.hyps by blast

  show ?case
    using cfg_seq.hyps(1,3,5-) cfg_b iso1 iso2
    apply simp
    apply (rule_tac x=\<open>\<lambda>l. if l \<in> transition_labels T1a then f1 l else f2 l\<close> in exI)
    apply (intro conjI)
       apply (subst bij_betw_cong[
          where g=\<open>\<lambda>t.
            if t = (e1a, CRam CSkip, s2a)
            then (e1b, CRam CSkip, s2b)
            else if t \<in> T1a
            then case t of (la, c, lb) \<Rightarrow> (f1 la, c, f1 lb)
            else case t of (la, c, lb) \<Rightarrow> (f2 la, c, f2 lb)
          \<close>])
        apply clarsimp
        apply (rename_tac lx c ly)
        apply (case_tac \<open>lx \<in> transition_labels T1a\<close>; case_tac \<open>ly \<in> transition_labels T1a\<close>)
           apply (meson transition_labels_include_start cfg_transition_labels_include_start disjoint_iff)
          apply (meson disjoint_iff transition_labels_include_startend)
         apply (meson cfg_transition_labels_include_end transition_labels_include_startend disjoint_iff)
        apply (meson cfg_transition_labels_include_end transition_labels_include_end)

       apply clarsimp
       apply (rule bij_betw_disjoint_insert, rule bij_betw_singleton, force)
         apply (rule bij_betw_disjoint_Un, blast, blast)
          apply (metis transition_labels_disjoint_then_transitions_disjoint)
         apply (metis transition_labels_disjoint_then_transitions_disjoint)
        apply (metis cfg_transition_labels_include_startend transition_labels_include_startend
        Un_iff disjoint_iff)
       apply (metis cfg_transition_labels_include_startend transition_labels_include_startend
        Un_iff disjoint_iff)
      apply (intro bij_betw_insert_ignore, (intro bij_betw_disjoint_Un; blast))
         apply (simp add: cfg_transition_labels_include_start)
        apply (simp add: cfg_transition_labels_include_start)
       apply (simp add: cfg_transition_labels_include_end)
      apply (simp add: cfg_transition_labels_include_end)
     apply (simp add: cfg_transition_labels_include_start)
    apply (metis cfg_transition_labels_include_end disjoint_iff)
    done
next
  case (cfg_ndet c1 T1a s1a e1a c2 T2a s2a e2a sa ea Ta Tb sb eb)

  obtain T1b T2b s1b e1b s2b e2b
    where cfg_b:
      \<open>cfg c1 T1b s1b e1b\<close>
      \<open>cfg c2 T2b s2b e2b\<close>
      \<open>transition_labels T1b \<inter> transition_labels T2b = {}\<close>
      \<open>sb \<notin> transition_labels T1b\<close>
      \<open>sb \<notin> transition_labels T2b\<close>
      \<open>eb \<notin> transition_labels T1b\<close>
      \<open>eb \<notin> transition_labels T2b\<close>
      \<open>sb \<noteq> eb\<close>
      \<open>Tb = {(sb, CRam CSkip, s1b), (sb, CRam CSkip, s2b), (e1b, CRam CSkip, eb), (e2b, CRam CSkip, eb)} \<union>  (T1b \<union> T2b)\<close>
    using cfg_ndet.prems by blast

  obtain f1
    where iso1:
      \<open>bij_betw (\<lambda>a. case a of (la, c, lb) \<Rightarrow> (f1 la, c, f1 lb)) T1a T1b\<close>
      \<open>bij_betw f1 (transition_labels T1a) (transition_labels T1b)\<close>
      \<open>f1 s1a = s1b\<close>
      \<open>f1 e1a = e1b\<close>
    using cfg_b cfg_ndet.hyps by blast

  obtain f2
    where iso2:
      \<open>bij_betw (\<lambda>a. case a of (la, c, lb) \<Rightarrow> (f2 la, c, f2 lb)) T2a T2b\<close>
      \<open>bij_betw f2 (transition_labels T2a) (transition_labels T2b)\<close>
      \<open>f2 s2a = s2b\<close>
      \<open>f2 e2a = e2b\<close>
    using cfg_b cfg_ndet.hyps by blast

  have label_lemmas1:
    \<open>s1a \<noteq> ea\<close> \<open>s1a \<noteq> sa\<close>
    \<open>s2a \<noteq> ea\<close> \<open>s2a \<noteq> sa\<close>
    \<open>e1a \<noteq> sa\<close> \<open>e1a \<noteq> ea\<close>
    \<open>e2a \<noteq> sa\<close> \<open>e2a \<noteq> ea\<close>
    \<open>ea \<noteq> s1a\<close> \<open>sa \<noteq> s1a\<close>
    \<open>ea \<noteq> s2a\<close> \<open>sa \<noteq> s2a\<close>
    \<open>sa \<noteq> e1a\<close> \<open>ea \<noteq> e1a\<close>
    \<open>sa \<noteq> e2a\<close> \<open>ea \<noteq> e2a\<close>

    \<open>s1a \<noteq> s2a\<close>
    \<open>e1a \<noteq> e2a\<close>
    \<open>e2a \<noteq> s1a\<close>
    using cfg_ndet
    by (force simp add: disjoint_iff dest: cfg_transition_labels_include_startend)+

  have label_lemmas2:
    \<open>s2a \<notin> transition_labels T1a\<close>
    \<open>e2a \<notin> transition_labels T1a\<close>
    \<open>s1a \<notin> transition_labels T2a\<close>
    \<open>e1a \<notin> transition_labels T2a\<close>
    \<open>s1a \<in> transition_labels T1a\<close>
    \<open>e1a \<in> transition_labels T1a\<close>
    \<open>s2a \<in> transition_labels T2a\<close>
    \<open>e2a \<in> transition_labels T2a\<close>

    \<open>e1a \<noteq> s1a\<close>
    using cfg_ndet
    by (force simp add: disjoint_iff
        dest: cfg_transition_labels_include_startend cfg_transition_labels_start_not_end)+

  note label_lemmas = label_lemmas1 label_lemmas2

  have transition_lemmas:
  \<open>\<And>c ly. (sa, c, ly) \<notin> T1a\<close>
  \<open>\<And>c ly. (sa, c, ly) \<notin> T2a\<close>
  \<open>\<And>c lx. (lx, c, ea) \<notin> T1a\<close>
  \<open>\<And>c lx. (lx, c, ea) \<notin> T2a\<close>
    using cfg_ndet
    by (force dest: transition_labels_include_startend)+

  show ?case
    using cfg_ndet.hyps(1,3,5-) cfg_b iso1 iso2
    apply simp
    apply (rule_tac x=\<open>\<lambda>l.
      if l = sa then sb
      else if l = ea then eb
      else if l \<in> transition_labels T1a then f1 l else f2 l
    \<close> in exI)
    apply (intro conjI)
         apply (subst bij_betw_cong[
          where g=\<open>\<lambda>t.
            if t = (sa, CRam CSkip, s1a) then (sb, CRam CSkip, s1b)
            else if t = (sa, CRam CSkip, s2a) then (sb, CRam CSkip, s2b)
            else if t = (e1a, CRam CSkip, ea) then (e1b, CRam CSkip, eb)
            else if t = (e2a, CRam CSkip, ea) then (e2b, CRam CSkip, eb)
            else if t \<in> T1a
            then case t of (la, c, lb) \<Rightarrow> (f1 la, c, f1 lb)
            else case t of (la, c, lb) \<Rightarrow> (f2 la, c, f2 lb)
          \<close>])
        apply clarify
        apply (rename_tac lx c ly)
        apply (case_tac \<open>(lx, c, ly) \<notin> T1a \<and> (lx, c, ly) \<notin> T2a\<close>)
         apply (force simp add: label_lemmas transition_lemmas)
        apply (clarsimp simp add: label_lemmas transition_lemmas)
        apply (erule disjE)
         apply (clarsimp simp add: transition_labels_include_startend)
         apply (metis transition_labels_include_startend)
        apply (clarsimp simp add: transition_labels_include_startend disjoint_iff)
        apply (subgoal_tac \<open>lx \<notin> transition_labels T1a \<and> ly \<notin> transition_labels T1a\<close>)
         apply (simp, metis transition_labels_include_startend)
        apply (meson transition_labels_include_startend)

       apply clarsimp
       apply (rule bij_betw_disjoint_insert, rule bij_betw_singleton, blast)
         apply (rule bij_betw_disjoint_insert, rule bij_betw_singleton, blast)
           apply (rule bij_betw_disjoint_insert, rule bij_betw_singleton, blast)
             apply (rule bij_betw_disjoint_insert, rule bij_betw_singleton, blast)
               apply (rule bij_betw_disjoint_Un, blast, blast)
                apply (metis transition_labels_disjoint_then_transitions_disjoint)
               apply (metis transition_labels_disjoint_then_transitions_disjoint)
              apply (force simp add: transition_lemmas)
             apply (force dest: transition_labels_include_end)
            apply (force simp add: label_lemmas transition_lemmas)
           apply (simp, metis cfg_transition_labels_include_end transition_labels_include_end disjoint_iff)
          apply (force simp add: label_lemmas transition_lemmas)
         apply (simp, metis cfg_transition_labels_include_start transition_labels_include_start)
        apply (force simp add: label_lemmas transition_lemmas)
       apply (simp, metis cfg_transition_labels_include_start disjoint_iff transition_labels_include_start)

      apply clarsimp
      apply (rule bij_betw_insert_ignore)
        apply (rule bij_betw_insert_ignore)
          apply (rule bij_betw_disjoint_insert, rule bij_betw_singleton, blast)
            apply (rule bij_betw_insert_ignore)
              apply (rule bij_betw_insert_ignore)
                apply (rule bij_betw_insert_ignore)
                  apply (rule bij_betw_insert_ignore)
                    apply (rule bij_betw_disjoint_insert, rule bij_betw_singleton, blast)
                      apply (rule bij_betw_disjoint_Un, blast, blast)
                       apply blast
                      apply blast
                     apply blast
                    apply blast
                   apply (force simp add: label_lemmas)
                  apply (metis Un_iff cfg_transition_labels_include_end insert_iff)
                 apply blast
                apply blast
               apply (force simp add: label_lemmas)
              apply (metis Un_iff Un_insert_right cfg_transition_labels_include_end)
             apply (force simp add: label_lemmas)
            apply (metis Un_iff Un_insert_left cfg_transition_labels_include_start)
           apply (force simp add: label_lemmas)
          apply (metis Un_iff cfg_transition_labels_include_startend insert_iff)
         apply (force simp add: label_lemmas)
        apply (metis Un_iff Un_insert_right cfg_transition_labels_include_start)
       apply blast
      apply blast

     apply (force simp add: label_lemmas)
    apply (force simp add: label_lemmas)
    done
next
  case (cfg_loop c Ta' sa' ea' sa ea Ta Tb sb eb)

  obtain Tb' sb' eb'
    where cfg_b:
      \<open>cfg c Tb' sb' eb'\<close>
      \<open>sb \<notin> transition_labels Tb'\<close>
      \<open>eb \<notin> transition_labels Tb'\<close>
      \<open>sb \<noteq> eb\<close>
      \<open>(eb', CRam CSkip, sb') \<notin> Tb'\<close>
      \<open>Tb = insert (eb', CRam CSkip, sb') (insert (sb, CRam CSkip, sb') (insert (eb', CRam CSkip, eb) Tb'))\<close>
    using cfg_loop.prems
    by blast

  obtain f
    where cfgiso:
      \<open>bij_betw (\<lambda>a. case a of (la, c, lb) \<Rightarrow> (f la, c, f lb)) Ta' Tb'\<close>
      \<open>bij_betw f (transition_labels Ta') (transition_labels Tb')\<close>
      \<open>f sa' = sb'\<close>
      \<open>f ea' = eb'\<close>
    using cfg_b cfg_loop.hyps
    by blast

  have label_lemmas:
    \<open>sa' \<noteq> ea\<close>
    \<open>ea' \<noteq> sa\<close>
    \<open>sa' \<noteq> sa\<close>
    \<open>ea \<noteq> ea'\<close> \<open>ea' \<noteq> ea\<close>
    using cfg_loop.hyps
    by (force dest: cfg_transition_labels_include_startend)+

  have transition_lemmas:
    \<open>\<And>lx c ly. (lx, c, ly) \<in> Ta' \<Longrightarrow> lx \<noteq> sa\<close>
    \<open>\<And>lx c ly. (lx, c, ly) \<in> Ta' \<Longrightarrow> lx \<noteq> ea\<close>
    \<open>\<And>lx c ly. (lx, c, ly) \<in> Ta' \<Longrightarrow> ly \<noteq> sa\<close>
    \<open>\<And>lx c ly. (lx, c, ly) \<in> Ta' \<Longrightarrow> ly \<noteq> ea\<close>
    using cfg_loop.hyps
    by (force dest: transition_labels_include_startend)+

  show ?case
    using cfg_loop.hyps(1,3,5-) cfg_b cfgiso
    apply simp
    apply (rule_tac x=\<open>\<lambda>l.
      if l = sa then sb
      else if l = ea then eb
      else f l
    \<close> in exI)
    apply (intro conjI)
       apply (subst bij_betw_cong[
          where g=\<open>\<lambda>t.
            if t = (ea', CRam CSkip, sa') then (eb', CRam CSkip, sb')
            else if t = (sa, CRam CSkip, sa') then (sb, CRam CSkip, sb')
            else if t = (ea', CRam CSkip, ea) then (eb', CRam CSkip, eb)
            else case t of (la, c, lb) \<Rightarrow> (f la, c, f lb)
          \<close>])
        apply clarify
        apply (rename_tac lx c ly)
        apply (case_tac \<open>(lx, c, ly) \<notin> Ta'\<close>)
         apply (force simp add: label_lemmas)
        apply (simp add: label_lemmas transition_lemmas)

       apply clarsimp
       apply (rule bij_betw_disjoint_insert, rule bij_betw_singleton, blast)
         apply (rule bij_betw_disjoint_insert, rule bij_betw_singleton, blast)
           apply (rule bij_betw_disjoint_insert, rule bij_betw_singleton, blast)
             apply force
            apply (force dest: transition_lemmas)
           apply (force dest: transition_labels_include_end)
          apply (force simp add: label_lemmas dest: transition_lemmas)
         apply (force dest: cfg_transition_labels_include_end transition_labels_include_start)
        apply (force simp add: label_lemmas)
       apply (force dest: cfg_transition_labels_include_end cfg_transition_labels_include_start)

      apply clarsimp
      apply (rule bij_betw_insert_ignore)
        apply (rule bij_betw_insert_ignore)
          apply (rule bij_betw_disjoint_insert, rule bij_betw_singleton, blast)
            apply (rule bij_betw_insert_ignore)
              apply (rule bij_betw_insert_ignore)
                apply (rule bij_betw_disjoint_insert, rule bij_betw_singleton, blast)
                  apply blast
                 apply (force simp add: cfg_loop.hyps)
                apply (force simp add: cfg_loop.hyps)
               apply (force dest: cfg_transition_labels_include_end)
              apply (force dest: cfg_transition_labels_include_end)
             apply (force dest: cfg_transition_labels_include_start)
            apply (force dest: cfg_transition_labels_include_start)
           apply (metis insertE label_lemmas(2-3))
          apply (force dest: cfg_transition_labels_include_startend)
         apply (force simp add: label_lemmas)
        apply blast
       apply blast
      apply blast
     apply simp
    apply simp
    done
qed


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
  \<open>semantic_proof c G I T \<equiv>
    (\<exists>s e. cfg c T s e) \<and>
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

definition \<open>local_command P c \<equiv> \<forall>Q. ram_comm_forward c (P \<^emph> Q) \<le> (ram_comm_forward c P) \<^emph> Q\<close>

lemma local_commandI:
  \<open>local_command P c \<Longrightarrow> ram_comm_forward c (P \<^emph> Q) \<le> (ram_comm_forward c P) \<^emph> Q\<close>
  by (simp add: local_command_def)

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
    \<open>os = Some s\<close>
    \<open>\<forall>k<length pc0. semantic_proof (Cs k) (Gs k) I T\<close>
    \<open>\<forall>l0 l1 c. (l0, CRam c, l1) \<in> T \<longrightarrow> (\<forall>k. local_command (Gs k l0) c)\<close>
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

    have c_local: \<open>local_command (Gs k (p ! k)) c\<close>
      using CRam_succeed opsem_prog_iter_smallstep_step
      by blast

    show ?thesis
    proof (rule opsem_prog_iter_smallstep_step)
      show \<open>\<forall>k<length p'. semantic_proof (Cs k) (Gs k) I T\<close>
        using opsem_prog_iter_smallstep_step.prems CRam_succeed
        by clarsimp

      show \<open>os'' = Some s''\<close>
        using opsem_prog_iter_smallstep_step.prems
        by simp

      show \<open>\<forall>l0 l1 c. (l0, CRam c, l1) \<in> T \<longrightarrow> (\<forall>k. local_command (Gs k l0) c)\<close>
        using opsem_prog_iter_smallstep_step.prems
        by simp

      have c_predicate_transformer: \<open>ram_comm_forward c (Gs k (p ! k)) \<le> Gs k l'\<close>
        using CRam_succeed opsem_prog_iter_smallstep_step
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

      show \<open>\<forall>l0 l1 c. (l0, CRam c, l1) \<in> T \<longrightarrow> (\<forall>k. local_command (Gs k l0) c)\<close>
        using opsem_prog_iter_smallstep_step.prems
        by simp

      have sem_proof_step:
        \<open>r < length I\<close>
        \<open>Gs k (p ! k) \<le> Gs k l' \<^emph> I ! r\<close>
        using CRelease opsem_prog_iter_smallstep_step.prems
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

      show \<open>\<forall>l0 l1 c. (l0, CRam c, l1) \<in> T \<longrightarrow> (\<forall>k. local_command (Gs k l0) c)\<close>
        using opsem_prog_iter_smallstep_step.prems
        by simp

      have sem_proof_step:
        \<open>r < length I\<close>
        \<open>Gs k (p ! k) \<^emph> I ! r \<le> Gs k l'\<close>
        using CAcquire opsem_prog_iter_smallstep_step.prems
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
qed




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
    \<open>\<And>i P Q. i < length I \<Longrightarrow> I ! i \<^emph> (P \<^bold>\<and> Q)  = (I ! i \<^emph> P) \<^bold>\<and> (I ! i \<^emph> Q)\<close>
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





section \<open>Hoare Logic (Alternative)\<close>

definition altsepconj :: \<open>('v state \<Rightarrow> bool) \<Rightarrow> ('v state \<Rightarrow> bool) \<Rightarrow> ('v state \<Rightarrow> bool)\<close> where
  \<open>altsepconj P Q \<equiv> (P \<^emph> \<^bold>T) \<^bold>\<and> (P \<sim>\<^emph> Q)\<close>


lemma pred_abac_eq_abc: \<open>(A \<^bold>\<and> B) \<^bold>\<and> A \<^bold>\<and> C = A \<^bold>\<and> B \<^bold>\<and> C\<close>
  by (force simp add: pred_conj_def)

lemma altsepconj_conj_distrib_left:
  \<open>altsepconj P (Q \<^bold>\<and> Q') = (altsepconj P Q) \<^bold>\<and> (altsepconj P Q')\<close>
  by (simp add: altsepconj_def sepcoimp_conj_distrib_left pred_abac_eq_abc)

definition logic_prog2 ::
  \<open>'l set \<Rightarrow> ('v state \<Rightarrow> bool) list \<Rightarrow> ('v state \<Rightarrow> bool) \<Rightarrow> 'v comm \<Rightarrow> ('v state \<Rightarrow> bool) \<Rightarrow> bool\<close>
  (\<open>_, _ 2\<turnstile>\<^sub>c \<lbrace> _ \<rbrace> _ \<lbrace> _ \<rbrace>\<close> [80,80,80,80,80] 80)
  where
    \<open>L, I 2\<turnstile>\<^sub>c \<lbrace> P \<rbrace> c \<lbrace> Q \<rbrace> \<equiv> (
      \<exists>G T. \<exists>s e.
        cfg c T s e \<and>
        L = transition_labels T \<and>
        (\<forall>(l,c',l')\<in>T. case c' of
          CRam cr' \<Rightarrow> ram_comm_forward cr' (G l) \<le> G l'
        | CAcquire r \<Rightarrow> r < length I \<and> altsepconj (I ! r) (G l) \<le> G l'
        | CRelease r \<Rightarrow> r < length I \<and> G l \<le> altsepconj (I ! r) (G l')
        ) \<and>
        P = G s \<and>
        G e \<le> Q
    )\<close>

lemma logic_prog2_seq:
  assumes
    \<open>L1 \<inter> L2 = {}\<close>
    \<open>L1, I 2\<turnstile>\<^sub>c \<lbrace> P \<rbrace> c1 \<lbrace> Q \<rbrace>\<close>
    \<open>L2, I 2\<turnstile>\<^sub>c \<lbrace> Q \<rbrace> c2 \<lbrace> R \<rbrace>\<close>
  shows
    \<open>\<exists>L12. L1 \<subseteq> L12 \<and> L2 \<subseteq> L12 \<and> L12, I 2\<turnstile>\<^sub>c \<lbrace> P \<rbrace> c1 ;; c2 \<lbrace> R \<rbrace>\<close>
proof -
  obtain T1 T2 G1 G2 s1 e1 s2 e2
    where unfolded_triples:
      \<open>cfg c1 T1 s1 e1\<close>
      \<open>cfg c2 T2 s2 e2\<close>
      \<open>L1 = transition_labels T1\<close>
      \<open>L2 = transition_labels T2\<close>
      \<open>\<forall>x\<in>T1. case x of (l, CRam cr', l') \<Rightarrow> ram_comm_forward cr' (G1 l) \<le> G1 l'
              | (l, CAcquire r, l') \<Rightarrow> r < length I \<and> altsepconj (I ! r) (G1 l) \<le> G1 l'
              | (l, CRelease r, l') \<Rightarrow> r < length I \<and> G1 l \<le> altsepconj (I ! r) (G1 l')\<close>
      \<open>\<forall>x\<in>T2.
          case x of (l, CRam cr', l') \<Rightarrow> ram_comm_forward cr' (G2 l) \<le> G2 l'
          | (l, CAcquire r, l') \<Rightarrow> r < length I \<and> altsepconj (I ! r) (G2 l) \<le> G2 l'
          | (l, CRelease r, l') \<Rightarrow> r < length I \<and> G2 l \<le> altsepconj (I ! r) (G2 l')\<close>
      \<open>G1 e1 \<le> G2 s2\<close>
      \<open>P = G1 s1\<close>
      \<open>G2 e2 \<le> R\<close>
      \<open>Q = G2 s2\<close>
    using assms
    by (clarsimp simp add: logic_prog2_def)

  have T2_separate_T1:
    \<open>\<And>l. l \<in> transition_labels T2 \<Longrightarrow> l \<notin> transition_labels T1\<close>
    using assms unfolded_triples by auto

  show ?thesis
    using unfolded_triples T2_separate_T1
    apply (clarsimp simp add: logic_prog2_def cfg_simps)
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

lemma logic_prog2_ndet:
  assumes
    \<open>L1 \<inter> L2 = {}\<close>
    \<open>s \<notin> L1\<close> \<open>s \<notin> L2\<close>
    \<open>e \<notin> L1\<close> \<open>e \<notin> L2\<close>
    \<open>s \<noteq> e\<close>
    \<open>L1, I 2\<turnstile>\<^sub>c \<lbrace> P1 \<rbrace> c1 \<lbrace> Q1 \<rbrace>\<close>
    \<open>L2, I 2\<turnstile>\<^sub>c \<lbrace> P2 \<rbrace> c2 \<lbrace> Q2 \<rbrace>\<close>
  shows
    \<open>\<exists>L12. L1 \<subseteq> L12 \<and> L2 \<subseteq> L12 \<and> L12, I 2\<turnstile>\<^sub>c \<lbrace> P1 \<^bold>\<and> P2 \<rbrace> c1 \<box> c2 \<lbrace> Q1 \<^bold>\<or> Q2 \<rbrace>\<close>
proof -
  obtain T1 T2 G1 G2 s1 e1 s2 e2
    where unfolded_triples:
      \<open>cfg c1 T1 s1 e1\<close>
      \<open>cfg c2 T2 s2 e2\<close>
      \<open>L1 = transition_labels T1\<close>
      \<open>L2 = transition_labels T2\<close>
      \<open>\<forall>x\<in>T1. case x of (l, CRam cr', l') \<Rightarrow> ram_comm_forward cr' (G1 l) \<le> G1 l'
              | (l, CAcquire r, l') \<Rightarrow> r < length I \<and> altsepconj (I ! r) (G1 l) \<le> G1 l'
              | (l, CRelease r, l') \<Rightarrow> r < length I \<and> G1 l \<le> altsepconj (I ! r) (G1 l')\<close>
      \<open>\<forall>x\<in>T2.
          case x of (l, CRam cr', l') \<Rightarrow> ram_comm_forward cr' (G2 l) \<le> G2 l'
          | (l, CAcquire r, l') \<Rightarrow> r < length I \<and> altsepconj (I ! r) (G2 l) \<le> G2 l'
          | (l, CRelease r, l') \<Rightarrow> r < length I \<and> G2 l \<le> altsepconj (I ! r) (G2 l')\<close>
      \<open>G1 e1 \<le> Q1\<close>
      \<open>P1 = G1 s1\<close>
      \<open>G2 e2 \<le> Q2\<close>
      \<open>P2 = G2 s2\<close>
    using assms
    by (clarsimp simp add: logic_prog2_def)

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
    apply (clarsimp simp add: logic_prog2_def cfg_simps)
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


lemma logic_prog2_conj:
  assumes
    \<open>L1, I 2\<turnstile>\<^sub>c \<lbrace> P1 \<rbrace> c \<lbrace> Q1 \<rbrace>\<close>
    \<open>L2, I 2\<turnstile>\<^sub>c \<lbrace> P2 \<rbrace> c \<lbrace> Q2 \<rbrace>\<close>
    \<open>L1 \<inter> L2 = {}\<close>
  shows
    \<open>L1, I 2\<turnstile>\<^sub>c \<lbrace> P1 \<^bold>\<and> P2 \<rbrace> c \<lbrace> Q1 \<^bold>\<and> Q2 \<rbrace>\<close>
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
        | (l, CAcquire r, l') \<Rightarrow> r < length I \<and> altsepconj (I ! r) (G1 l) \<le> G1 l'
        | (l, CRelease r, l') \<Rightarrow> r < length I \<and> G1 l \<le> altsepconj (I ! r) (G1 l')\<close>
      \<open>\<forall>x\<in>T2. case x of
          (l, CRam cr', l') \<Rightarrow> ram_comm_forward cr' (G2 l) \<le> G2 l'
        | (l, CAcquire r, l') \<Rightarrow> r < length I \<and> altsepconj (I ! r) (G2 l) \<le> G2 l'
        | (l, CRelease r, l') \<Rightarrow> r < length I \<and> G2 l \<le> altsepconj (I ! r) (G2 l')\<close>
      \<open>G1 e1 \<le> Q1\<close>
      \<open>P1 = G1 s1\<close>
      \<open>G2 e2 \<le> Q2\<close>
      \<open>P2 = G2 s2\<close>
    using assms
    by (clarsimp simp add: logic_prog2_def cfg_simps)

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
    apply (clarsimp simp add: logic_prog2_def cfg_simps)
    apply (rule_tac x=\<open>\<lambda>l. G1 l \<^bold>\<and> G2 (f l)\<close> in exI)
    apply (rule_tac x=T1 in exI)
    apply (rule_tac x=s1 in exI)
    apply (rule_tac x=e1 in exI)
    apply (intro conjI)
        apply force
       apply force
      apply (intro ballI impI)
      apply (drule bspec, blast)
      apply clarsimp
      apply (rename_tac lx cc ly)
      apply (drule_tac x=\<open>(f lx, cc, f ly)\<close> in bspec)
       apply (force dest: bij_betwE)
      apply (clarsimp split: comm.splits)
        apply (force simp add: pred_conj_simp dest!: predicate1D[OF ram_comm_forward_conj])
       apply (simp add: pred_conjD altsepconj_conj_distrib_left)
      apply (simp add: pred_conjD altsepconj_conj_distrib_left)
     apply (simp add: le_fun_def pred_conj_simp)
    apply (simp add: le_fun_def pred_conj_simp)
    done
qed


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
    iffD1[
      OF sepconj_distrib_conj_eq_strong_sepcoimp invariant_sepconj_distrib_conj,
      THEN spec[where x=\<open>G l\<close> for l]]
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
    iffD1[
      OF sepconj_distrib_conj_eq_strong_sepcoimp invariant_sepconj_distrib_conj,
      THEN spec[where x=\<open>G l\<close> for l]]
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