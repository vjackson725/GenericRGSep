theory SepLogic
  imports Util
begin

section \<open>Predicate Logic\<close>

definition pred_false :: \<open>'a \<Rightarrow> bool\<close> (\<open>\<^bold>F\<close>) where
  \<open>\<^bold>F \<equiv> \<lambda>x. False\<close>

definition pred_true :: \<open>'a \<Rightarrow> bool\<close> (\<open>\<^bold>T\<close>) where
  \<open>\<^bold>T \<equiv> \<lambda>x. True\<close>

definition pred_impl :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> (infixr \<open>\<^bold>\<longrightarrow>\<close> 82) where
  \<open>p \<^bold>\<longrightarrow> q \<equiv> \<lambda>x. p x \<longrightarrow> q x\<close>

lemma pred_conj_simp:
  \<open>(p \<sqinter> q) x \<longleftrightarrow> p x \<and> q x\<close>
  by (simp add:)

lemma pred_disj_simp:
  \<open>(p \<squnion> q) x \<longleftrightarrow> p x \<or> q x\<close>
  by (simp add:)


lemma pred_conjD: \<open>(A1 \<sqinter> A2) s \<Longrightarrow> A1 \<le> B1 \<Longrightarrow> A2 \<le> B2 \<Longrightarrow> (B1 \<sqinter> B2) s\<close>
  by blast

lemma pred_abac_eq_abc:
  fixes A B C :: \<open>'a :: lattice\<close>
  shows \<open>(A \<sqinter> B) \<sqinter> A \<sqinter> C = A \<sqinter> B \<sqinter> C\<close>
  by (simp add: inf.absorb1)

section \<open> mfault \<close>

datatype 'a mfault =
  Success (the_success: 'a)
  | Fault

instantiation mfault :: (ord) ord
begin

fun less_eq_mfault :: \<open>'a mfault \<Rightarrow> 'a mfault \<Rightarrow> bool\<close> where
  \<open>less_eq_mfault _ Fault = True\<close>
| \<open>less_eq_mfault Fault (Success b) = False\<close>
| \<open>less_eq_mfault (Success a) (Success b) = (a \<le> b)\<close>

lemma less_eq_mfault_def:
  \<open>a \<le> b =
    (case b of
      Fault \<Rightarrow> True
    | Success b \<Rightarrow>
      (case a of
        Fault \<Rightarrow> False
      | Success a \<Rightarrow> a \<le> b))\<close>
  by (cases a; cases b; force)

fun less_mfault :: \<open>'a mfault \<Rightarrow> 'a mfault \<Rightarrow> bool\<close> where
  \<open>less_mfault Fault _ = False\<close>
| \<open>less_mfault (Success a) Fault = True\<close>
| \<open>less_mfault (Success a) (Success b) = (a < b)\<close>

lemma less_mfault_def:
  \<open>a < b =
    (case a of
      Fault \<Rightarrow> False
    | Success a \<Rightarrow>
      (case b of
        Fault \<Rightarrow> True
      | Success b \<Rightarrow> a < b))\<close>
  by (cases a; cases b; force)

instance proof qed

end

instantiation mfault :: (preorder) preorder
begin

instance proof
  fix x y z :: \<open>'a :: preorder mfault\<close>
  show \<open>(x < y) = (x \<le> y \<and> \<not> y \<le> x)\<close>
    by (simp add: less_eq_mfault_def less_mfault_def mfault.case_eq_if less_le_not_le)
  show \<open>x \<le> x\<close>
    by (simp add: less_eq_mfault_def mfault.case_eq_if)
  show \<open>x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z\<close>
    by (force dest: order_trans simp add: less_eq_mfault_def split: mfault.splits)
qed

end


instantiation mfault :: (order) order_top
begin

definition \<open>top_mfault \<equiv> Fault\<close>

instance proof
  fix x y z :: \<open>'a :: order mfault\<close>
  show \<open>x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y\<close>
    by (simp add: less_eq_mfault_def split: mfault.splits)
  show \<open>x \<le> top\<close>
    by (simp add: top_mfault_def)
qed

end

instantiation mfault :: (linorder) linorder
begin

instance proof
  fix x y z :: \<open>'a :: linorder mfault\<close>
  show \<open>x \<le> y \<or> y \<le> x\<close>
    by (cases x; cases y; force)
qed

end

instantiation mfault :: (order_bot) order_bot
begin

definition \<open>bot_mfault = Success bot\<close>

instance proof
  fix a :: \<open>'a :: order_bot mfault\<close>
  show \<open>\<bottom> \<le> a\<close>
    by (simp add: bot_mfault_def less_eq_mfault_def mfault.case_eq_if)
qed

end


section \<open> Separation Logic \<close>

class disjoint =
  fixes disjoint :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (infix \<open>##\<close> 60)

class disjoint_zero = disjoint + zero +
  assumes zero_disjointL[simp]: \<open>0 ## a\<close>
  assumes zero_disjointR[simp]: \<open>a ## 0\<close>

class sepalg = disjoint_zero + plus + order_bot +
  (* partial commutative monoid *)
  assumes partial_add_assoc:
    \<open>a ## b \<Longrightarrow> b ## c \<Longrightarrow> a ## c \<Longrightarrow> (a + b) + c = a + (b + c)\<close>
  assumes partial_add_commute: \<open>a ## b \<Longrightarrow> a + b = b + a\<close>
  assumes partial_add_0[simp]: \<open>0 + a = a\<close>
  (* separation laws *)
  assumes disjoint_symm: \<open>a ## b = b ## a\<close>
  assumes disjoint_add_rightL: \<open>b ## c \<Longrightarrow> a ## (b + c) \<Longrightarrow> a ## b\<close>
  assumes disjoint_add_right_commute: \<open>a ## c \<Longrightarrow> b ## (a + c) \<Longrightarrow> a ## (b + c)\<close>
  assumes positivity: \<open>a ## b \<Longrightarrow> a + b = c \<Longrightarrow> c ## c \<Longrightarrow> c + c = c \<Longrightarrow> a ## a \<and> a + a = a\<close>
  (* order defn *)
  assumes le_iff_sepadd: \<open>a \<le> b \<longleftrightarrow> (\<exists>c. a ## c \<and> b = a + c)\<close>
begin

lemma disjoint_add_rightR: \<open>b ## c \<Longrightarrow> a ## b + c \<Longrightarrow> a ## c\<close>
  by (metis disjoint_add_rightL disjoint_symm partial_add_commute)

lemma disjoint_add_leftL: \<open>a ## b \<Longrightarrow> a + b ## c \<Longrightarrow> a ## c\<close>
  using disjoint_add_rightL disjoint_symm by blast

lemma disjoint_add_leftR: \<open>a ## b \<Longrightarrow> a + b ## c \<Longrightarrow> b ## c\<close>
  by (metis disjoint_add_leftL disjoint_symm partial_add_commute)

lemma disjoint_add_commuteL: \<open>c ## b \<Longrightarrow> (c + b) ## a \<Longrightarrow> a + b ## c\<close>
  by (simp add: disjoint_add_right_commute disjoint_symm)

lemma le_plus: \<open>a ## b \<Longrightarrow> a \<le> a + b\<close>
  using le_iff_sepadd by auto

lemma le_plus2: \<open>a ## b \<Longrightarrow> b \<le> a + b\<close>
  by (metis le_plus disjoint_symm partial_add_commute)

lemma positivity2: \<open>a ## b \<Longrightarrow> a + b = c \<Longrightarrow> c ## c \<Longrightarrow> c + c = c \<Longrightarrow> b ## b \<and> b + b = b\<close>
  using disjoint_symm partial_add_commute positivity by blast

text \<open>
  From 'Bringing order to the separation logic Jungle'.
  Increasing elements are related to the units of the algebra.
\<close>
definition increasing_elem :: \<open>'a \<Rightarrow> bool\<close> where
  \<open>increasing_elem a \<equiv> \<forall>b c. a ## b \<longrightarrow> a + b = c \<longrightarrow> b \<le> c\<close>

lemma zero_increasing_elem:
  \<open>increasing_elem 0\<close>
  by (simp add: increasing_elem_def)

subsection \<open>partial canonically_ordered_monoid_add lemmas\<close>

lemma zero_le[simp]: \<open>0 \<le> x\<close>
  by (metis le_plus partial_add_0 zero_disjointL)

lemma le_zero_eq[simp]: "n \<le> 0 \<longleftrightarrow> n = 0"
  by (auto intro: order.antisym)

lemma not_less_zero[simp]: "\<not> n < 0"
  by (auto simp: less_le)

lemma zero_less_iff_neq_zero: "0 < n \<longleftrightarrow> n \<noteq> 0"
  by (auto simp: less_le)

text \<open>This theorem is useful with \<open>blast\<close>\<close>
lemma gr_zeroI: "(n = 0 \<Longrightarrow> False) \<Longrightarrow> 0 < n"
  by (rule zero_less_iff_neq_zero[THEN iffD2]) iprover

lemma not_gr_zero[simp]: "\<not> 0 < n \<longleftrightarrow> n = 0"
  by (simp add: zero_less_iff_neq_zero)

lemma gr_implies_not_zero: "m < n \<Longrightarrow> n \<noteq> 0"
  by auto

lemma sepadd_eq_0_iff_both_eq_0[simp]: "x ## y \<Longrightarrow> x + y = 0 \<longleftrightarrow> x = 0 \<and> y = 0"
  by (metis le_plus le_zero_eq partial_add_0)

lemma zero_eq_sepadd_iff_both_eq_0[simp]: "x ## y \<Longrightarrow> 0 = x + y \<longleftrightarrow> x = 0 \<and> y = 0"
  using sepadd_eq_0_iff_both_eq_0[of x y] unfolding eq_commute[of 0] .

lemma partial_add_left_commute:
  \<open>a ## b \<Longrightarrow> b ## c \<Longrightarrow> a ## c \<Longrightarrow> b + (a + c) = a + (b + c)\<close>
  by (metis disjoint_symm partial_add_assoc partial_add_commute)

(*
lemma less_eqE:
  assumes \<open>a \<le> b\<close>
  obtains c where \<open>b = a + c\<close>
  using assms
  by (force simp add: le_iff_sepadd)

lemma lessE:
  assumes \<open>a < b\<close>
  obtains c where \<open>b = a + c\<close> \<open>a ## c\<close> and \<open>c \<noteq> 0\<close>
proof -
  from assms have \<open>a \<le> b\<close> \<open>a \<noteq> b\<close>
    by simp_all
  from \<open>a \<le> b\<close> obtain c where \<open>b = a + c\<close> \<open>a ## c\<close>
    by (force simp add: le_iff_sepadd)
  moreover have \<open>c \<noteq> 0\<close> using \<open>a \<noteq> b\<close> \<open>b = a + c\<close>
    by (metis partial_add_0 partial_add_commute zero_disjointL)
  ultimately show ?thesis
    by (rule that)
qed
*)

lemmas zero_order = zero_le le_zero_eq not_less_zero zero_less_iff_neq_zero not_gr_zero
  \<comment> \<open>This should be attributed with \<open>[iff]\<close>, but then \<open>blast\<close> fails in \<open>Set\<close>.\<close>

subsection \<open>Misc\<close>

lemma sep_add_0_right[simp]: "a + 0 = a"
  by (metis zero_disjointR partial_add_0 partial_add_commute)

subsection \<open>sepdomeq\<close>

definition \<open>sepdomeq a b \<equiv> \<forall>c. a ## c = b ## c\<close>

lemma sepdomeq_reflp:
  \<open>reflp sepdomeq\<close>
  by (simp add: reflpI sepdomeq_def)

lemma sepdomeq_symp:
  \<open>symp sepdomeq\<close>
  by (metis sepdomeq_def sympI)

lemma sepdomeq_transp:
  \<open>transp sepdomeq\<close>
  by (simp add: sepdomeq_def transp_def)

lemma same_sepdom_disjoint_leftD:
  \<open>sepdomeq a b \<Longrightarrow> a ## c \<Longrightarrow> b ## c\<close>
  by (simp add: sepdomeq_def)

lemma sepdomeq_disjoint_rightD:
  \<open>sepdomeq a b \<Longrightarrow> b ## c \<Longrightarrow> a ## c\<close>
  by (simp add: sepdomeq_def)

definition \<open>sepdomsubseteq a b \<equiv> \<forall>c. a ## c \<longrightarrow> b ## c\<close>

lemma sepdomsubseteq_reflp:
  \<open>reflp sepdomsubseteq\<close>
  by (simp add: reflpI sepdomsubseteq_def)

lemma sepdomsubseteq_transp:
  \<open>transp sepdomsubseteq\<close>
  by (simp add: sepdomsubseteq_def transp_def)

lemma sepdomsubseteq_disjointD:
  \<open>sepdomsubseteq a b \<Longrightarrow> a ## c \<Longrightarrow> b ## c\<close>
  by (simp add: sepdomsubseteq_def)


subsection \<open> Seplogic connectives \<close>

definition sepconj :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> (infixl \<open>\<^emph>\<close> 88) where
  \<open>P \<^emph> Q \<equiv> \<lambda>h. \<exists>h1 h2. h1 ## h2 \<and> h = h1 + h2 \<and> P h1 \<and> Q h2\<close>

definition sepimp :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> (infixr \<open>\<midarrow>\<^emph>\<close> 85) where
  \<open>P \<midarrow>\<^emph> Q \<equiv> \<lambda>h. \<forall>h1. h ## h1 \<longrightarrow> P h1 \<longrightarrow> Q (h + h1)\<close>

definition sepcoimp :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> (infixr \<open>\<sim>\<^emph>\<close> 85) where
  \<open>P \<sim>\<^emph> Q \<equiv> \<lambda>h. \<forall>h1 h2. h1 ## h2 \<longrightarrow> h = h1 + h2 \<longrightarrow> P h1 \<longrightarrow> Q h2\<close>

definition septract :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> (infixr \<open>\<midarrow>\<odot>\<close> 86) where
  \<open>P \<midarrow>\<odot> Q \<equiv> \<lambda>h. \<exists>h1. h ## h1 \<and> P h1 \<and> Q (h + h1)\<close>

definition septract_rev :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> (infixr \<open>\<odot>\<midarrow>\<close> 86) where
  \<open>P \<odot>\<midarrow> Q \<equiv> \<lambda>h. \<exists>h'. h ## h' \<and> P (h + h') \<and> Q h'\<close>

lemma septract_reverse: \<open>P \<midarrow>\<odot> Q = Q \<odot>\<midarrow> P\<close>
  by (force simp add: septract_def septract_rev_def)


definition sepconj_mfault ::
  \<open>('a \<Rightarrow> bool) mfault \<Rightarrow> ('a \<Rightarrow> bool) mfault \<Rightarrow> ('a \<Rightarrow> bool) mfault\<close> (infixl \<open>\<^emph>\<^sub>f\<close> 88)
  where
    \<open>P \<^emph>\<^sub>f Q \<equiv>
      case P of
        Fault \<Rightarrow> Fault
      | Success P \<Rightarrow>
        (case Q of
          Fault \<Rightarrow> Fault
        | Success Q \<Rightarrow> Success (\<lambda>h. \<exists>h1 h2. h1 ## h2 \<and> h = h1 + h2 \<and> P h1 \<and> Q h2))\<close>


definition subheapexist :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> where
  \<open>subheapexist P \<equiv> \<lambda>h. \<exists>h1. h1 \<le> h \<and> P h1\<close>


definition emp :: \<open>'a \<Rightarrow> bool\<close> where
  \<open>emp \<equiv> (\<lambda>h. h = 0)\<close>

definition emp_mfault :: \<open>('a \<Rightarrow> bool) mfault\<close> ("emp\<^sub>f") where
  \<open>emp\<^sub>f \<equiv> Success emp\<close>


fun iterated_sepconj :: \<open>('a \<Rightarrow> bool) list \<Rightarrow> ('a \<Rightarrow> bool)\<close> where
  \<open>iterated_sepconj (P # Ps) = P \<^emph> iterated_sepconj Ps\<close>
| \<open>iterated_sepconj [] = emp\<close>



lemma sepconj_assoc: \<open>(P \<^emph> Q) \<^emph> R = P \<^emph> (Q \<^emph> R)\<close>
  apply (clarsimp simp add: sepconj_def ex_simps[symmetric] partial_add_assoc simp del: ex_simps)
  apply (intro ext iffI)
   apply (metis disjoint_add_leftR disjoint_add_right_commute disjoint_symm partial_add_assoc
      partial_add_commute)+
  done

lemma sepconj_comm: \<open>P \<^emph> Q = Q \<^emph> P\<close>
  unfolding sepconj_def
  by (metis disjoint_symm partial_add_commute)

lemma sepconj_left_comm: \<open>Q \<^emph> (P \<^emph> R) = P \<^emph> (Q \<^emph> R)\<close>
  apply (clarsimp simp add: sepconj_def ex_simps[symmetric] partial_add_assoc simp del: ex_simps)
  apply (rule ext)
  apply (metis disjoint_add_rightR disjoint_add_rightL disjoint_add_right_commute
      partial_add_left_commute)
  done

lemmas sepconj_ac = sepconj_assoc sepconj_comm sepconj_left_comm

(*

\<^emph>   < ~ >  \<midarrow>\<^emph>
|           X
\<sim>\<^emph>  < ~ > \<midarrow>\<odot>

*)


lemma septract_sepimp_dual: \<open>P \<midarrow>\<odot> Q = -(P \<midarrow>\<^emph> (-Q))\<close>
  unfolding septract_def sepimp_def
  by force

lemma sepimp_sepcoimp_dual: \<open>P \<sim>\<^emph> Q = -(P \<^emph> (-Q))\<close>
  unfolding sepconj_def sepcoimp_def
  by force

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
  apply (clarsimp simp add: sepcoimp_def sepconj_def)
  apply (intro ext iffI; clarsimp)
   apply (metis disjoint_add_leftR disjoint_add_right_commute disjoint_symm partial_add_assoc
      partial_add_commute)+
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
  \<open>precise P \<equiv> \<forall>h. \<forall>h1\<le>h. P h1 \<longrightarrow> (\<forall>h2\<le>h. P h2 \<longrightarrow> h1 = h2)\<close>

definition precise' :: \<open>('a \<Rightarrow> bool) \<Rightarrow> bool\<close> where
  \<open>precise' P \<equiv> \<forall>h1. P h1 \<longrightarrow> (\<forall>h2. P h2 \<longrightarrow>
                    (\<exists>h1' h2'. h1 ## h1' \<and> h2 ## h2' \<and> h1 + h1' = h2 + h2') \<longrightarrow> h1 = h2)\<close>

definition intuitionistic :: \<open>('a \<Rightarrow> bool) \<Rightarrow> bool\<close> where
  \<open>intuitionistic P \<equiv> \<forall>h h'. P h \<and> h \<le> h' \<longrightarrow> P h'\<close>


lemma strong_sepcoimp_imp_sepconj:
  \<open>(P \<^emph> \<^bold>T) \<sqinter> (P \<sim>\<^emph> Q) \<le> P \<^emph> Q\<close>
  by (force simp add: sepconj_def sepcoimp_def precise_def le_fun_def pred_true_def)

lemma secoimp_imp_sepconj:
  \<open>P \<sqinter> (P \<sim>\<^emph> Q) \<le> P \<^emph> (Q \<sqinter> emp)\<close>
  unfolding sepcoimp_def sepconj_def le_fun_def le_bool_def emp_def
  by force

lemma sepconj_pdisj_distrib_left: \<open>P \<^emph> (Q1 \<squnion> Q2) = P \<^emph> Q1 \<squnion> P \<^emph> Q2\<close>
  by (force simp add: sepconj_def)

lemma sepcoimp_pconj_distrib_left:
  \<open>P \<sim>\<^emph> (Q \<sqinter> Q') = (P \<sim>\<^emph> Q) \<sqinter> (P \<sim>\<^emph> Q')\<close>
  by (force simp add: sepcoimp_def)

lemma not_coimp_emp:
  \<open>h \<noteq> 0 \<Longrightarrow> (- (\<^bold>T \<sim>\<^emph> emp)) h\<close>
  apply (clarsimp simp add: pred_true_def sepcoimp_def emp_def)
  apply (rule_tac x=0 in exI, force)
  done

lemma sepconj_distrib_conj_iff_sepconj_eq_strong_sepcoimp:
  shows \<open>(\<forall>Q Q'. P \<^emph> (Q \<sqinter> Q') = (P \<^emph> Q) \<sqinter> (P \<^emph> Q')) \<longleftrightarrow> (\<forall>Q. P \<^emph> Q = (P \<^emph> \<^bold>T) \<sqinter> (P \<sim>\<^emph> Q))\<close>
  apply (clarsimp simp add: sepconj_def sepcoimp_def precise_def le_fun_def pred_true_def)
  apply (intro iffI)
  subgoal
    apply (rule allI)
    apply (rule ext)
    apply (rule iffI)
     apply simp
     apply (rule conjI)
      apply blast
     apply clarsimp
     apply (drule_tac x=\<open>Q\<close> in spec)
     apply (drule_tac x=\<open>(=) h2a\<close> in spec)
     apply (drule_tac x=\<open>h1a + h2a\<close> in cong[OF _ refl])
     apply fastforce
    apply fastforce
    done
  apply (simp add: fun_eq_iff, blast)
  done


lemma sepconj_distrib_conj_imp_sepconj_eq_strong_sepcoimp:
  assumes \<open>\<forall>Q Q'. P \<^emph> (Q \<sqinter> Q') = (P \<^emph> Q) \<sqinter> (P \<^emph> Q')\<close>
  shows \<open>P \<^emph> Q = (P \<^emph> \<^bold>T) \<sqinter> (P \<sim>\<^emph> Q)\<close>
  using assms sepconj_distrib_conj_iff_sepconj_eq_strong_sepcoimp
  by blast

lemma sepconj_middle_monotone_left: \<open>A1 \<^emph> A2 \<le> B \<Longrightarrow> A1 \<^emph> C \<^emph> A2 \<le> C \<^emph> B\<close>
  by (metis sepconj_assoc sepconj_comm sepconj_left_mono)

lemma sepconj_middle_monotone_right: \<open>A \<le> B1 \<^emph> B2 \<Longrightarrow> C \<^emph> A \<le> B1 \<^emph> C \<^emph> B2\<close>
  by (metis sepconj_assoc sepconj_comm sepconj_left_mono)


definition supported :: \<open>('a \<Rightarrow> bool) \<Rightarrow> bool\<close> where
  \<open>supported P \<equiv> \<forall>s. P s \<longrightarrow> (\<exists>hp. P hp \<and> hp \<le> s \<and> (\<forall>s'. hp \<le> s' \<longrightarrow> s' \<le> s \<longrightarrow> P s'))\<close>

lemma precise_to_supported:
  \<open>precise P \<Longrightarrow> supported (P \<^emph> \<^bold>T)\<close>
  by (metis order.eq_iff supported_def)


lemma le_iff_sepadd:
  \<open>a \<le> b \<longleftrightarrow> (\<exists>c. b = a + c)\<close>
  nitpick[card=2]
  oops

lemma precise_to_intuitionistic:
  fixes P :: \<open>'a \<Rightarrow> bool\<close>
  shows \<open>precise' P \<Longrightarrow> intuitionistic (P \<^emph> \<^bold>T)\<close>
  apply (simp add: sepconj_def pred_true_def precise'_def intuitionistic_def)
  apply clarsimp
  oops

lemma supported_intuitionistic_to_precise:
  \<open>supported P \<Longrightarrow> intuitionistic P \<Longrightarrow> precise (P \<sqinter> - (P \<^emph> (-emp)))\<close>
  nitpick[card=4]
  oops
  (* not actualy true *)

end

section \<open>Strongly Separated Separation Logic\<close>

class strong_separated_seplogic = sepalg +
  assumes only_zero_self_sep: \<open>a ## a \<Longrightarrow> a = 0\<close>
begin


lemma selfsep_iff: \<open>a ## a \<longleftrightarrow> a = 0\<close>
  using only_zero_self_sep zero_disjointL by blast

end

section \<open>Disjointness Separation Algebra\<close>

class disjoint_seplogic = sepalg +
  assumes disjointness: \<open>a ## a \<Longrightarrow> a + a = b \<Longrightarrow> a = b\<close>

section \<open>Cross-Split Separation Algebra\<close>

class crosssplit_sepalg = sepalg +
  assumes cross_split:
  \<open>a ## b \<Longrightarrow> c ## d \<Longrightarrow> a + b = z \<Longrightarrow> c + d = z \<Longrightarrow>
    \<exists>ac ad bc bd.
      ac ## ad \<and> bc ## bd \<and> ac ## bc \<and> ad ## bd \<and>
      ac + ad = a \<and> bc + bd = b \<and> ac + bc = c \<and> ad + bd = d\<close>

section \<open>Right Cancellative Separation Logic\<close>

class right_cancel_sepalg = sepalg +
  assumes partial_right_cancel: \<open>\<And>a b c. a ## c \<Longrightarrow> b ## c \<Longrightarrow> (a + c = b + c) = (a = b)\<close>
begin

lemma partial_right_cancel2:
  \<open>c ## a \<Longrightarrow> c ## b \<Longrightarrow> (a + c = b + c) = (a = b)\<close>
  using partial_right_cancel disjoint_symm
  by force

lemma partial_left_cancel:
  \<open>a ## c \<Longrightarrow> b ## c \<Longrightarrow> (c + a = c + b) = (a = b)\<close>
  by (metis partial_add_commute partial_right_cancel)

lemma partial_left_cancel2:
  \<open>c ## a \<Longrightarrow> c ## b \<Longrightarrow> (c + a = c + b) = (a = b)\<close>
  using partial_left_cancel disjoint_symm
  by force

lemma weak_emp:
  \<open>a ## a \<and> a + a = a \<longleftrightarrow> a = 0\<close>
  by (metis sep_add_0_right zero_disjointR partial_left_cancel2)

lemma strong_positivity:
  \<open>a ## b \<Longrightarrow> c ## c \<Longrightarrow> a + b = c \<Longrightarrow> c + c = c \<Longrightarrow> a = b \<and> b = c\<close>
  using weak_emp by force


lemma precise_iff_conj_distrib:
  shows \<open>precise' P \<longleftrightarrow> (\<forall>Q Q'. P \<^emph> (Q \<sqinter> Q') = (P \<^emph> Q) \<sqinter> (P \<^emph> Q'))\<close>
proof (rule iffI)
  assume distrib_assm: \<open>\<forall>Q Q'. P \<^emph> (Q \<sqinter> Q') = (P \<^emph> Q) \<sqinter> (P \<^emph> Q')\<close>
  show \<open>precise' P\<close>
  proof (clarsimp simp add: precise'_def)
    fix h1 h1' h2 h2'
    assume precise_assms:
      \<open>h1 + h1' = h2 + h2'\<close>
      \<open>h1 ## h1'\<close>
      \<open>h2 ## h2'\<close>
      \<open>P h1\<close>
      \<open>P h2\<close>

    have \<open>(P \<^emph> ((=) h1')) (h2+h2')\<close>
      using precise_assms partial_add_commute disjoint_symm sepconj_def
      by auto
    moreover have \<open>(P \<^emph> ((=) h2')) (h2+h2')\<close>
      using precise_assms partial_add_commute disjoint_symm sepconj_def
      by auto
    ultimately have \<open>(P \<^emph> ((=) h1' \<sqinter> (=) h2')) (h2+h2')\<close>
      using distrib_assm precise_assms
      by simp
    then show \<open>h1 = h2\<close>
      using precise_assms disjoint_symm partial_right_cancel
      unfolding sepconj_def
      by fastforce
  qed
next
  assume precise_assm: \<open>precise' P\<close>
  then show \<open>\<forall>Q Q'. P \<^emph> (Q \<sqinter> Q') = (P \<^emph> Q) \<sqinter> (P \<^emph> Q')\<close>
    by (simp add: sepconj_def precise'_def fun_eq_iff, blast dest: partial_left_cancel2)
qed


lemma precise_iff_all_sepconj_imp_sepcoimp:
  shows \<open>precise' P \<longleftrightarrow> (\<forall>Q. P \<^emph> Q \<le> P \<sim>\<^emph> Q)\<close>
  apply (clarsimp simp add: sepconj_def sepcoimp_def precise'_def le_fun_def)
  apply (rule iffI)
   apply (metis partial_left_cancel2)
  apply (metis le_less order.irrefl partial_right_cancel)
  done

lemma precise_sepconj_eq_strong_sepcoimp:
  shows \<open>precise' P \<Longrightarrow> P \<^emph> Q = (P \<^emph> \<^bold>T) \<sqinter> (P \<sim>\<^emph> Q)\<close>
  apply (clarsimp simp add: sepconj_def sepcoimp_def precise'_def le_fun_def pred_true_def)
  apply (rule ext)
  apply (rule iffI)
  apply (blast dest: partial_left_cancel2)
  apply blast
  done


lemma \<open>(a \<^emph> \<top>) \<sqinter> (b \<^emph> \<top>) \<le> ((a \<^emph> b) \<squnion> (a \<sqinter> b)) \<^emph> \<top>\<close>
  nitpick[card=4]
  oops

lemma \<open>((a \<^emph> b) \<squnion> (a \<sqinter> b)) \<^emph> \<top> \<le> (a \<^emph> \<top>) \<sqinter> (b \<^emph> \<top>)\<close>
proof -
  have F1: \<open>((a \<^emph> b) \<squnion> (a \<sqinter> b)) \<^emph> \<top> = (a \<^emph> b) \<^emph> \<top> \<squnion> (a \<sqinter> b) \<^emph> \<top>\<close>
    by (simp add: sepconj_comm sepconj_pdisj_distrib_left)
  moreover have \<open>a \<^emph> b \<^emph> \<top> \<le> (a \<^emph> \<top>) \<sqinter> (b \<^emph> \<top>)\<close>
    by (metis le_infI sepconj_comm sepconj_middle_monotone_left top_greatest)
  moreover have \<open>(a \<sqinter> b) \<^emph> \<top> \<le> (a \<^emph> \<top>) \<sqinter> (b \<^emph> \<top>)\<close>
    by (simp add: sepconj_left_mono)
  ultimately show ?thesis
    by simp
qed

end

class avoiding_sepalg = sepalg +
  assumes exists_greatest_avoiding:
    \<open>\<exists>a'. a' \<le> a \<and> a' ## b \<and> (\<forall>a''. a'' \<le> a \<longrightarrow> a'' ## b \<longrightarrow> a'' \<le> a')\<close>
begin

subsection \<open> sep_restrict \<close>

definition \<open>sep_restrict a b \<equiv> GREATEST a'. a' \<le> a \<and> sepdomeq a' b\<close>

lemma sep_avoid_equality:
  \<open>x \<le> a \<Longrightarrow> sepdomeq x b \<Longrightarrow> (\<And>y. y \<le> a \<Longrightarrow> sepdomeq y b \<Longrightarrow> y \<le> x) \<Longrightarrow> sep_restrict a b = x\<close>
  by (force simp add: sep_restrict_def intro: Greatest_equality)

lemma sep_avoidI2_order:
  \<open>x \<le> a \<Longrightarrow> sepdomeq x b \<Longrightarrow>
    (\<And>y. y \<le> a \<Longrightarrow> sepdomeq y b \<Longrightarrow> y \<le> x) \<Longrightarrow>
    (\<And>x. x \<le> a \<Longrightarrow> sepdomeq x b \<Longrightarrow> \<forall>y. y \<le> a \<longrightarrow> sepdomeq y b \<longrightarrow> y \<le> x \<Longrightarrow> Q x) \<Longrightarrow>
    Q (sep_restrict a b)\<close>
  unfolding sep_restrict_def
  by (blast intro!: GreatestI2_order)

(*
lemma sep_restrict_exists:
  \<open>\<exists>b. b \<le> a \<and> sepdomeq b c \<and> (\<forall>b'. b' \<le> a \<longrightarrow> sepdomeq b' c \<longrightarrow> b' \<le> b)\<close>
  unfolding sepdomeq_def
  sorry

lemma sep_restrict_unique:
  \<open>\<exists>!b. b \<le> a \<and> sepdomeq b c \<and> (\<forall>b'. b' \<le> a \<longrightarrow> sepdomeq b' c \<longrightarrow> b' \<le> b)\<close>
  using order.antisym sep_restrict_exists by fastforce
*)

lemma sep_restrict_unique:
  \<open>x \<le> a \<Longrightarrow> sepdomeq x c \<Longrightarrow> (\<forall>b'\<le>a. sepdomeq b' c \<longrightarrow> b' \<le> x) \<Longrightarrow>
    (\<forall>y. y \<le> a \<and> sepdomeq y c \<and> (\<forall>b'\<le>a. sepdomeq b' c \<longrightarrow> b' \<le> y)\<longrightarrow> y = x)\<close>
  by (simp add: order.eq_iff)

lemma sep_avoid_decreasing: \<open>sep_restrict a b \<le> a\<close>
  sledgehammer
  sorry

lemma sep_avoid_disjoint: \<open>sep_restrict a b ## c \<Longrightarrow> b ## c\<close>
  sledgehammer
  sorry

lemma sep_avoid_ge:
  \<open>b \<le> a \<Longrightarrow> b ## c \<Longrightarrow> b \<le> sep_avoid a c\<close>
  by (metis sep_avoid_equality sep_avoid_unique)

lemma sep_avoid_idem[simp]:
  \<open>sep_avoid (sep_avoid a b) b = sep_avoid a b\<close>
  using sep_avoid_disjoint sep_avoid_equality by blast

lemma sep_avoid_monoL:
  \<open>a \<le> b \<Longrightarrow> sep_avoid a c \<le> sep_avoid b c\<close>
  by (meson order.trans sep_avoid_disjoint sep_avoid_decreasing sep_avoid_ge)

lemma sep_avoid_antimonoR:
  \<open>b \<le> c \<Longrightarrow> sep_avoid a c \<le> sep_avoid a b\<close>
  by (metis disjoint_add_rightL le_iff_sepadd sep_avoid_decreasing sep_avoid_disjoint sep_avoid_ge)

lemma sep_avoid_idem_strong:
  \<open>b \<le> c \<Longrightarrow> sep_avoid (sep_avoid a b) c = sep_avoid a c\<close>
  by (meson order.antisym sep_avoid_antimonoR sep_avoid_decreasing
      sep_avoid_disjoint sep_avoid_ge sep_avoid_monoL)

lemma sep_avoid_idem_strong2:
  \<open>b \<le> c \<Longrightarrow> sep_avoid (sep_avoid a c) b = sep_avoid a c\<close>
  by (metis order.antisym sep_avoid_antimonoR sep_avoid_decreasing sep_avoid_idem)

lemma sep_avoid_commute:
  \<open>sep_avoid (sep_avoid a b) c = sep_avoid (sep_avoid a c) b\<close>
  by (rule order.antisym; metis disjoint_add_rightL disjoint_symm le_iff_sepadd sep_avoid_decreasing
      sep_avoid_disjoint sep_avoid_ge sep_avoid_monoL)

subsection \<open> sep_avoid \<close>

definition \<open>sep_avoid a b \<equiv> GREATEST a'. a' \<le> a \<and> a' ## b\<close>

lemma sep_avoid_equality:
  \<open>x \<le> a \<Longrightarrow> x ## b \<Longrightarrow> (\<And>y. y \<le> a \<Longrightarrow> y ## b \<Longrightarrow> y \<le> x) \<Longrightarrow> sep_avoid a b = x\<close>
  by (force simp add: sep_avoid_def intro: Greatest_equality)

lemma sep_avoidI2_order:
  \<open>x \<le> a \<Longrightarrow> x ## b \<Longrightarrow>
    (\<And>y. y \<le> a \<Longrightarrow> y ## b \<Longrightarrow> y \<le> x) \<Longrightarrow>
    (\<And>x. x \<le> a \<Longrightarrow> x ## b \<Longrightarrow> \<forall>y. y \<le> a \<longrightarrow> y ## b \<longrightarrow> y \<le> x \<Longrightarrow> Q x) \<Longrightarrow>
    Q (sep_avoid a b)\<close>
  unfolding sep_avoid_def
  by (blast intro!: GreatestI2_order)

lemma sep_avoid_ex1:
  \<open>\<exists>!b. b \<le> a \<and> b ## c \<and> (\<forall>b'. b' \<le> a \<longrightarrow> b' ## c \<longrightarrow> b' \<le> b)\<close>
  by (meson order.antisym exists_greatest_avoiding)

lemma sep_avoid_decreasing: \<open>sep_avoid a b \<le> a\<close>
  using exists_greatest_avoiding sep_avoid_equality by blast

lemma sep_avoid_disjoint: \<open>sep_avoid a b ## b\<close>
  using exists_greatest_avoiding sep_avoid_equality by blast

lemma sep_avoid_ge:
  \<open>b \<le> a \<Longrightarrow> b ## c \<Longrightarrow> b \<le> sep_avoid a c\<close>
  by (metis sep_avoid_equality sep_avoid_unique)

lemma sep_avoid_idem[simp]:
  \<open>sep_avoid (sep_avoid a b) b = sep_avoid a b\<close>
  using sep_avoid_disjoint sep_avoid_equality by blast

lemma sep_avoid_monoL:
  \<open>a \<le> b \<Longrightarrow> sep_avoid a c \<le> sep_avoid b c\<close>
  by (meson order.trans sep_avoid_disjoint sep_avoid_decreasing sep_avoid_ge)

lemma sep_avoid_antimonoR:
  \<open>b \<le> c \<Longrightarrow> sep_avoid a c \<le> sep_avoid a b\<close>
  by (metis disjoint_add_rightL le_iff_sepadd sep_avoid_decreasing sep_avoid_disjoint sep_avoid_ge)

lemma sep_avoid_idem_strong:
  \<open>b \<le> c \<Longrightarrow> sep_avoid (sep_avoid a b) c = sep_avoid a c\<close>
  by (meson order.antisym sep_avoid_antimonoR sep_avoid_decreasing
      sep_avoid_disjoint sep_avoid_ge sep_avoid_monoL)

lemma sep_avoid_idem_strong2:
  \<open>b \<le> c \<Longrightarrow> sep_avoid (sep_avoid a c) b = sep_avoid a c\<close>
  by (metis order.antisym sep_avoid_antimonoR sep_avoid_decreasing sep_avoid_idem)

lemma sep_avoid_commute:
  \<open>sep_avoid (sep_avoid a b) c = sep_avoid (sep_avoid a c) b\<close>
  by (rule order.antisym; metis disjoint_add_rightL disjoint_symm le_iff_sepadd sep_avoid_decreasing
      sep_avoid_disjoint sep_avoid_ge sep_avoid_monoL)


subclass crosssplit_sepalg
  apply standard
  apply (rule_tac x=\<open>sep_avoid a d + sep_avoid c b\<close> in exI)
  apply (rule_tac x=\<open>sep_avoid a c + sep_avoid d b\<close> in exI)
  apply (rule_tac x=\<open>sep_avoid b d + sep_avoid c a\<close> in exI)
  apply (rule_tac x=\<open>sep_avoid b c + sep_avoid d a\<close> in exI)
  apply clarsimp
  oops

end


section \<open>A cancellative Separation Algebra\<close>

class cancel_sepalg = sepalg + minus +
  assumes sepadd_diff_cancel_left'[simp]: "a ## b \<Longrightarrow> (a + b) - a = b"
  assumes diff_diff_sepadd[simp]: "b ## c \<Longrightarrow> a - b - c = a - (b + c)"
  (* seplogic specific *)
  assumes restricted_by_disjoint: \<open>b ## (a - b)\<close>
  assumes state_minus_basic_split: \<open>(a - b) + (a - (a - b)) = a\<close>
  assumes state_minus_generic_split:
    \<open>a1 ## a2 \<Longrightarrow> sepdomeq (a1 + a2) b \<Longrightarrow> b = (b - a1) + (b - a2)\<close>
(*
  assumes unique_disjoint_sup:
    \<open>\<exists>!c. c ## b \<and> c \<le> a \<and> (\<forall>c'. c' ## b \<longrightarrow> c' \<le> a \<longrightarrow> c' \<le> c)\<close>
*)
begin

subclass right_cancel_sepalg
  apply standard
  apply (metis disjoint_symm partial_add_commute sepadd_diff_cancel_left')
  done

subsection \<open>partial cancel_comm_monoid_add lemmas\<close>

lemma sepadd_diff_cancel_right'[simp]: "a ## b \<Longrightarrow> (a + b) - b = a"
  by (metis sepadd_diff_cancel_left' disjoint_symm partial_add_commute)

lemma sepadd_diff_cancel_left [simp]: "c ## a \<Longrightarrow> c ## b \<Longrightarrow> (c + a) - (c + b) = a - b"
  by (metis diff_diff_sepadd sepadd_diff_cancel_left')

lemma sepadd_diff_cancel_right [simp]: "a ## c \<Longrightarrow> b ## c \<Longrightarrow> (a + c) - (b + c) = a - b"
  by (metis sepadd_diff_cancel_left disjoint_symm partial_add_commute)

lemma diff_right_commute: "b ## c \<Longrightarrow> a - c - b = a - b - c"
  by (simp add: disjoint_symm partial_add_commute)

subsection \<open>partial cancel_comm_monoid_add lemmas\<close>

lemma diff_zero[simp]: "a - 0 = a"
  using sepadd_diff_cancel_right'[of a 0] by simp

lemma diff_cancel[simp]: "a - a = 0"
  using sepadd_diff_cancel_left' zero_disjointR by fastforce

lemma sepadd_implies_diff:
  \<open>c ## b \<Longrightarrow> c + b = a \<Longrightarrow> c = a - b\<close>
  by force

lemma sepadd_cancel_right_right[simp]: "a ## b \<Longrightarrow> a = a + b \<longleftrightarrow> b = 0"
  using sepadd_diff_cancel_left' by fastforce

lemma sepadd_cancel_right_left[simp]: "b ## a \<Longrightarrow> a = b + a \<longleftrightarrow> b = 0"
  by (simp add: disjoint_symm partial_add_commute)

lemma sepadd_cancel_left_right[simp]: "a ## b \<Longrightarrow> a + b = a \<longleftrightarrow> b = 0"
  by (auto dest: sym)

lemma sepadd_cancel_left_left[simp]: "b ## a \<Longrightarrow> b + a = a \<longleftrightarrow> b = 0"
  by (auto dest: sym)

subsection \<open>partial comm_monoid_diff\<close>

lemma zero_diff[simp]: "0 - a = 0"
  by (metis le_plus le_zero_eq restricted_by_disjoint state_minus_basic_split)

lemma diff_add_zero[simp]: "a ## b \<Longrightarrow> a - (a + b) = 0"
  by (metis diff_cancel diff_diff_sepadd zero_diff)

subsection \<open>ordered_ab_semigroup_add\<close>

(*
lemma sepadd_left_mono: "c ## a \<Longrightarrow> c ## b \<Longrightarrow> a \<le> b \<Longrightarrow> c + a \<le> c + b"
  using le_iff_sepadd partial_add_assoc by auto

lemma sepadd_right_mono: "a ## c \<Longrightarrow> b ## c \<Longrightarrow> a \<le> b \<Longrightarrow> a + c \<le> b + c"
  by (metis disjoint_symm partial_add_commute sepadd_left_mono)

lemma sepadd_mono:
  assumes \<open>a ## c\<close> \<open>b ## d\<close> \<open>a \<le> b\<close> \<open>c \<le> d\<close>
  shows \<open>a + c \<le> b + d\<close>
proof -
  have \<open>b ## c\<close>
    using assms le_iff_sepadd by force
  then show ?thesis
    using assms sepadd_left_mono[of b c d] sepadd_right_mono[of a c b]
    by simp
qed

subsection \<open>partial ordered_cancel_ab_semigroup_add\<close>

lemma sepadd_strict_left_mono: "c ## a \<Longrightarrow> c ## b \<Longrightarrow> a < b \<Longrightarrow> c + a < c + b"
  by (simp add: order.strict_iff_order partial_left_cancel2 sepadd_left_mono)

lemma sepadd_strict_right_mono: "a ## c \<Longrightarrow> b ## c \<Longrightarrow> a < b \<Longrightarrow> a + c < b + c"
  by (metis disjoint_symm partial_add_commute sepadd_strict_left_mono)

lemma sepadd_less_le_mono:
  assumes \<open>a ## c\<close> \<open>b ## d\<close> \<open>a < b\<close> \<open>c \<le> d\<close>
  shows \<open>a + c < b + d\<close>
proof -
  have \<open>b ## c\<close>
    using assms le_iff_sepadd by fastforce
  then show ?thesis
    using assms sepadd_left_mono[of b c d] sepadd_strict_right_mono[of a c b]
      order.strict_trans1
    by force
qed

lemma sepadd_le_less_mono: "a ## c \<Longrightarrow> b ## d \<Longrightarrow> a \<le> b \<Longrightarrow> c < d \<Longrightarrow> a + c < b + d"
  by (metis order.strict_iff_order sepadd_less_le_mono sepadd_strict_left_mono)

subsection \<open>partial ordered_ab_semigroup_add_imp_le\<close>

lemma sepadd_le_imp_le_left: "c ## a \<Longrightarrow> c ## b \<Longrightarrow> c + a \<le> c + b \<Longrightarrow> a \<le> b"
  by (simp add: le_iff_sepadd, metis disjoint_add_left partial_add_assoc
      sepadd_diff_cancel_left')

lemma sepadd_less_imp_less_left:
  \<open>c ## a \<Longrightarrow> c ## b \<Longrightarrow> c + a < c + b \<Longrightarrow> a < b\<close>
  by (force dest: sepadd_le_imp_le_left order.antisym simp add: less_le_not_le)

lemma sepadd_less_imp_less_right: "a ## c \<Longrightarrow> b ## c \<Longrightarrow> a + c < b + c \<Longrightarrow> a < b"
  by (simp add: disjoint_symm partial_add_commute sepadd_less_imp_less_left)

lemma sepadd_less_cancel_left [simp]: "a ## c \<Longrightarrow> b ## c \<Longrightarrow> c + a < c + b \<longleftrightarrow> a < b"
  by (meson disjoint_symm sepadd_less_imp_less_left sepadd_strict_left_mono)

lemma sepadd_less_cancel_right [simp]: "a ## c \<Longrightarrow> b ## c \<Longrightarrow> a + c < b + c \<longleftrightarrow> a < b"
  by (metis partial_add_commute sepadd_less_cancel_left)

lemma add_le_cancel_left [simp]: "c ## a \<Longrightarrow> c ## b \<Longrightarrow> c + a \<le> c + b \<longleftrightarrow> a \<le> b"
  using sepadd_le_imp_le_left sepadd_left_mono by blast

lemma add_le_cancel_right [simp]: "a ## c \<Longrightarrow> b ## c \<Longrightarrow> a + c \<le> b + c \<longleftrightarrow> a \<le> b"
  by (metis disjoint_symm partial_add_commute sepadd_le_imp_le_left sepadd_right_mono)

lemma add_le_imp_le_right: "a ## c \<Longrightarrow> b ## c \<Longrightarrow> a + c \<le> b + c \<Longrightarrow> a \<le> b"
  by simp

lemma max_add_distrib_left: "x ## z \<Longrightarrow> y ## z \<Longrightarrow> max x y + z = max (x + z) (y + z)"
  unfolding max_def by auto

lemma min_add_distrib_left: "x ## z \<Longrightarrow> y ## z \<Longrightarrow> min x y + z = min (x + z) (y + z)"
  unfolding min_def by auto

lemma max_add_distrib_right: "x ## y \<Longrightarrow> x ## z \<Longrightarrow> x + max y z = max (x + y) (x + z)"
  unfolding max_def by auto

lemma min_add_distrib_right: "x ## y \<Longrightarrow> x ## z \<Longrightarrow> x + min y z = min (x + y) (x + z)"
  unfolding min_def by auto

subsection \<open>partial ordered_comm_monoid_add\<close>

lemma sepadd_nonpos_nonpos: "a \<le> 0 \<Longrightarrow> b \<le> 0 \<Longrightarrow> a + b \<le> 0"
  by simp

(*
lemma sepadd_nonneg_eq_0_iff: "0 \<le> x \<Longrightarrow> 0 \<le> y \<Longrightarrow> x + y = 0 \<longleftrightarrow> x = 0 \<and> y = 0"
  oops
*)

lemma sepadd_nonpos_eq_0_iff: "x \<le> 0 \<Longrightarrow> y \<le> 0 \<Longrightarrow> x + y = 0 \<longleftrightarrow> x = 0 \<and> y = 0"
  by simp

lemma sepadd_increasing: "a ## c \<Longrightarrow> 0 \<le> a \<Longrightarrow> b \<le> c \<Longrightarrow> b \<le> a + c"
  using sepadd_mono [of 0 b a c] by simp

lemma sepadd_increasing2: "a ## c \<Longrightarrow> 0 \<le> c \<Longrightarrow> b \<le> a \<Longrightarrow> b \<le> a + c"
  using sepadd_mono[of 0 b c a]
  by (simp add: sepadd_increasing partial_add_commute disjoint_symm)

lemma sepadd_decreasing: "a ## c \<Longrightarrow> a \<le> 0 \<Longrightarrow> c \<le> b \<Longrightarrow> a + c \<le> b"
  using sepadd_mono[of a c 0 b] by simp

lemma sepadd_decreasing2: "c \<le> 0 \<Longrightarrow> a \<le> b \<Longrightarrow> a + c \<le> b"
  using sepadd_mono[of a c b 0] by simp

lemma sepadd_pos_nonneg: "a ## b \<Longrightarrow> 0 < a \<Longrightarrow> 0 \<le> b \<Longrightarrow> 0 < a + b"
  using less_le_trans[of 0 a "a + b"] by (simp add: sepadd_increasing2)

lemma sepadd_pos_pos: "a ## b \<Longrightarrow> 0 < a \<Longrightarrow> 0 < b \<Longrightarrow> 0 < a + b"
  by (intro sepadd_pos_nonneg less_imp_le)

lemma sepadd_nonneg_pos: "a ## b \<Longrightarrow> 0 \<le> a \<Longrightarrow> 0 < b \<Longrightarrow> 0 < a + b"
  using sepadd_pos_nonneg[of b a] by (simp add: partial_add_commute disjoint_symm)

lemma sepadd_neg_nonpos: "a ## b \<Longrightarrow> a < 0 \<Longrightarrow> b \<le> 0 \<Longrightarrow> a + b < 0"
  using le_less_trans[of "a + b" a 0] by (simp add: add_decreasing2)

lemma sepadd_neg_neg: "a ## b \<Longrightarrow> a < 0 \<Longrightarrow> b < 0 \<Longrightarrow> a + b < 0"
  by (intro sepadd_neg_nonpos less_imp_le)

lemma sepadd_nonpos_neg: "a ## b \<Longrightarrow> a \<le> 0 \<Longrightarrow> b < 0 \<Longrightarrow> a + b < 0"
  using sepadd_neg_nonpos[of b a] by (simp add: partial_add_commute)

subsection \<open>new laws\<close>

lemma symmdiff_disjoint:\<open>(a - b) ## (b - a)\<close>
  by (metis disjoint_add_left disjoint_symm restricted_by_disjoint
      state_minus_basic_split)

lemma restricted_state_a_substate: \<open>a - b \<le> a\<close>
  by (metis le_plus restricted_by_disjoint state_minus_basic_split)

lemma minus_expansion1: \<open>a - b = a - (a - (a - b))\<close>
  by (metis restricted_by_disjoint state_minus_basic_split sepadd_diff_cancel_right')

lemma subtract_less_zero: \<open>a' \<le> a \<Longrightarrow> a' - a = 0\<close>
  by (metis diff_cancel diff_diff_sepadd le_iff_sepadd le_zero_eq restricted_state_a_substate)
*)
end

end