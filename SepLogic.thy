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

subsection \<open> Common Notions \<close>


class disjoint =
  fixes disjoint :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (infix \<open>##\<close> 60)

class disjoint_zero = disjoint + zero +
  assumes zero_disjointL[simp]: \<open>0 ## a\<close>
  assumes zero_disjointR[simp]: \<open>a ## 0\<close>

find_theorems \<open>?a + ?c \<le> ?b + ?d\<close>

subsection \<open> Permission Algebras \<close>

class perm_alg = disjoint + plus + order +
  (* ordered partial commutative monoid *)
  assumes partial_add_assoc: \<open>a ## b \<Longrightarrow> b ## c \<Longrightarrow> a ## c \<Longrightarrow> (a + b) + c = a + (b + c)\<close>
  assumes partial_add_commute: \<open>a ## b \<Longrightarrow> a + b = b + a\<close>
  (* separation laws *)
  assumes disjoint_symm: \<open>a ## b \<Longrightarrow> b ## a\<close>
  assumes disjoint_add_rightL: \<open>b ## c \<Longrightarrow> a ## (b + c) \<Longrightarrow> a ## b\<close>
  assumes disjoint_add_right_commute: \<open>a ## c \<Longrightarrow> b ## (a + c) \<Longrightarrow> a ## (b + c)\<close>
  assumes positivity: \<open>a ## b \<Longrightarrow> a + b = c \<Longrightarrow> c ## c \<Longrightarrow> c + c = c \<Longrightarrow> a ## a \<and> a + a = a\<close>
  assumes less_iff_sepadd: \<open>a < b \<longleftrightarrow> a \<noteq> b \<and> (\<exists>c. a ## c \<and> b = a + c)\<close>
begin

lemma disjoint_symm_iff: \<open>a ## b \<longleftrightarrow> b ## a\<close>
  using disjoint_symm by blast

lemma le_plus: \<open>a ## b \<Longrightarrow> a \<le> a + b\<close>
  by (metis less_iff_sepadd nless_le order.refl)

lemma le_plus2: \<open>a ## b \<Longrightarrow> b \<le> a + b\<close>
  by (metis le_plus disjoint_symm partial_add_commute)

lemma common_subresource_selfsep:
  \<open>a ## b \<Longrightarrow> ab \<le> a \<Longrightarrow> ab \<le> b \<Longrightarrow> ab ## ab\<close>
  by (metis disjoint_add_rightL disjoint_symm order.order_iff_strict less_iff_sepadd)

lemma disjoint_add_rightR: \<open>b ## c \<Longrightarrow> a ## b + c \<Longrightarrow> a ## c\<close>
  by (metis disjoint_add_rightL disjoint_symm partial_add_commute)

lemma disjoint_add_leftL: \<open>a ## b \<Longrightarrow> a + b ## c \<Longrightarrow> a ## c\<close>
  using disjoint_add_rightL disjoint_symm by blast

lemma disjoint_add_leftR: \<open>a ## b \<Longrightarrow> a + b ## c \<Longrightarrow> b ## c\<close>
  by (metis disjoint_add_leftL disjoint_symm partial_add_commute)

lemma disjoint_add_commuteL: \<open>c ## b \<Longrightarrow> c + b ## a \<Longrightarrow> a + b ## c\<close>
  by (simp add: disjoint_add_right_commute disjoint_symm)

lemma positivity2: \<open>a ## b \<Longrightarrow> a + b = c \<Longrightarrow> c ## c \<Longrightarrow> c + c = c \<Longrightarrow> b ## b \<and> b + b = b\<close>
  using disjoint_symm partial_add_commute positivity by blast

lemma partial_add_left_commute:
  \<open>a ## b \<Longrightarrow> b ## c \<Longrightarrow> a ## c \<Longrightarrow> b + (a + c) = a + (b + c)\<close>
  by (metis disjoint_symm partial_add_assoc partial_add_commute)

lemma disjoint_preservation:
  \<open>a' \<le> a \<Longrightarrow> a ## b \<Longrightarrow> a' ## b\<close>
  by (metis disjoint_add_leftL order.order_iff_strict less_iff_sepadd)

lemma partial_add_double_assoc:
  \<open>a ## c \<Longrightarrow> b ## d \<Longrightarrow> c ## d \<Longrightarrow> b ## c + d \<Longrightarrow> a ## b + (c + d) \<Longrightarrow> a + b + (c + d) = (a + c) + (b + d)\<close>
  by (metis disjoint_add_rightR disjoint_add_rightL disjoint_add_right_commute partial_add_assoc
      partial_add_left_commute)


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

end

subsection \<open> Separation Algebras \<close>

class sep_alg = perm_alg + disjoint_zero + order_bot +
  assumes partial_add_0[simp]: \<open>0 + a = a\<close>
begin

lemma le_iff_sepadd: \<open>a \<le> b \<longleftrightarrow> (\<exists>c. a ## c \<and> b = a + c)\<close>
  by (metis order.order_iff_strict less_iff_sepadd partial_add_0 partial_add_commute zero_disjointR)

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

lemmas zero_order = zero_le le_zero_eq not_less_zero zero_less_iff_neq_zero not_gr_zero

subsection \<open>Misc\<close>

lemma sep_add_0_right[simp]: "a + 0 = a"
  by (metis zero_disjointR partial_add_0 partial_add_commute)

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

section \<open>Strongly Separated Separation Algebra\<close>

class strong_separated_sep_alg = sep_alg +
  assumes only_zero_self_sep: \<open>a ## a \<Longrightarrow> a = 0\<close>
begin

lemma selfsep_iff: \<open>a ## a \<longleftrightarrow> a = 0\<close>
  using only_zero_self_sep zero_disjointL by blast

end

section \<open>Disjointness Separation Algebra\<close>

class disjoint_perm_alg = perm_alg +
  assumes disjointness: \<open>a ## a \<Longrightarrow> a + a = b \<Longrightarrow> a = b\<close>

class disjoint_sep_alg = sep_alg + disjoint_perm_alg

section \<open>Cross-Split Separation Algebra\<close>

class crosssplit_perm_alg = perm_alg +
  assumes cross_split:
  \<open>a ## b \<Longrightarrow> c ## d \<Longrightarrow> a + b = z \<Longrightarrow> c + d = z \<Longrightarrow>
    \<exists>ac ad bc bd.
      ac ## ad \<and> bc ## bd \<and> ac ## bc \<and> ad ## bd \<and>
      ac + ad = a \<and> bc + bd = b \<and> ac + bc = c \<and> ad + bd = d\<close>

class crosssplit_sep_alg = sep_alg + crosssplit_perm_alg

section \<open>Right Cancellative Separation Logic\<close>

class right_cancel_perm_alg = perm_alg +
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

end

class right_cancel_sep_alg = right_cancel_perm_alg + sep_alg
begin

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


subsection \<open> Halving \<close>

class halving_perm_alg = perm_alg +
  fixes half :: \<open>'a \<Rightarrow> 'a\<close>
  assumes half_additive_split: \<open>\<And>a. half a + half a = a\<close>
  assumes half_self_disjoint: \<open>\<And>a. half a ## half a\<close>
begin

lemma half_plus: \<open>half (a + b) = half a + half b\<close>
  oops

lemma half_disjoint_preservation_left: \<open>a ## b \<Longrightarrow> half a ## b\<close>
  by (metis disjoint_add_leftR half_additive_split half_self_disjoint)

lemma half_disjoint_preservation_right: \<open>a ## b \<Longrightarrow> a ## half b\<close>
  using half_disjoint_preservation_left disjoint_symm by blast

lemma half_disjoint_preservation: \<open>a ## b \<Longrightarrow> half a ## half b\<close>
  by (simp add: half_disjoint_preservation_left half_disjoint_preservation_right)


lemma half_disjoint_distribL:
  \<open>a ## c \<Longrightarrow> a + c ## b \<Longrightarrow> a + half c ## b + half c\<close>
  by (metis disjoint_add_leftL disjoint_add_right_commute disjoint_symm half_additive_split
      half_self_disjoint partial_add_assoc)

lemma half_disjoint_distribR:
  \<open>b ## c \<Longrightarrow> a ## b + c \<Longrightarrow> a + half c ## b + half c\<close>
  using half_disjoint_distribL disjoint_symm by blast

lemma half_eq_full_imp_self_additive:
  \<open>half a = a \<Longrightarrow> a + a = a\<close>
  by (metis half_additive_split)

end

class halving_sep_alg = sep_alg + halving_perm_alg

section \<open> Disjoint Parts Algebra \<close>

class disjoint_parts_perm_alg = perm_alg +
  assumes disjointness_left_plusI: \<open>a ## b \<Longrightarrow> a ## c \<Longrightarrow> b ## c \<Longrightarrow> a + b ## c\<close>
begin

lemmas disjointness_left_plusI' =
  disjointness_left_plusI
  disjointness_left_plusI[OF disjoint_symm]
  disjointness_left_plusI[OF _ disjoint_symm]
  disjointness_left_plusI[OF _ _ disjoint_symm]
  disjointness_left_plusI[OF _ disjoint_symm disjoint_symm]
  disjointness_left_plusI[OF disjoint_symm _ disjoint_symm]
  disjointness_left_plusI[OF disjoint_symm disjoint_symm]
  disjointness_left_plusI[OF disjoint_symm disjoint_symm disjoint_symm]

lemma disjointness_right_plusI:
  \<open>a ## b \<Longrightarrow> a ## c \<Longrightarrow> b ## c \<Longrightarrow> a ## b + c\<close>
  using disjointness_left_plusI disjoint_symm by auto

lemmas disjointness_right_plusI' =
  disjointness_right_plusI
  disjointness_right_plusI[OF disjoint_symm]
  disjointness_right_plusI[OF _ disjoint_symm]
  disjointness_right_plusI[OF _ _ disjoint_symm]
  disjointness_right_plusI[OF _ disjoint_symm disjoint_symm]
  disjointness_right_plusI[OF disjoint_symm _ disjoint_symm]
  disjointness_right_plusI[OF disjoint_symm disjoint_symm]
  disjointness_right_plusI[OF disjoint_symm disjoint_symm disjoint_symm]

lemma disjointness_left_plus_eq:
  \<open>a ## b \<Longrightarrow> a + b ## c \<longleftrightarrow> a ## c \<and> b ## c\<close>
  by (metis disjointness_left_plusI disjoint_add_leftL disjoint_add_leftR)

lemma disjointness_right_plus_eq:
  \<open>b ## c \<Longrightarrow> a ## b + c \<longleftrightarrow> a ## b \<and> a ## c\<close>
  by (metis disjointness_right_plusI disjoint_add_rightL disjoint_add_rightR)

lemma partial_add_double_assoc2:
  \<open>a ## b \<Longrightarrow> a ## c \<Longrightarrow> a ## d \<Longrightarrow> b ## c \<Longrightarrow> b ## d \<Longrightarrow> c ## d \<Longrightarrow> a + b + (c + d) = (a + c) + (b + d)\<close>
  by (meson disjointness_right_plusI partial_add_double_assoc)

end

class disjoint_parts_sep_alg = sep_alg + disjoint_parts_perm_alg


class disjoint_halving_cancel_perm_alg = halving_perm_alg + disjoint_perm_alg + right_cancel_perm_alg
begin

subclass disjoint_parts_perm_alg
  by (standard, metis disjoint_add_rightL disjointness half_additive_split half_self_disjoint
      partial_add_assoc partial_right_cancel2)

end

end