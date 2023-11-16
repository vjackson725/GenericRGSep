theory SepLogic
  imports Util
begin

thm less_induct

section \<open>Predicate Logic\<close>

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

subsection \<open> Permission Algebras \<close>

class perm_alg = disjoint + plus + order +
  (* ordered partial commutative monoid *)
  assumes partial_add_assoc: \<open>a ## b \<Longrightarrow> b ## c \<Longrightarrow> a ## c \<Longrightarrow> (a + b) + c = a + (b + c)\<close>
  assumes partial_add_commute: \<open>a ## b \<Longrightarrow> a + b = b + a\<close>
  (* separation laws *)
  assumes disjoint_sym: \<open>a ## b \<Longrightarrow> b ## a\<close>
  assumes disjoint_add_rightL: \<open>b ## c \<Longrightarrow> a ## b + c \<Longrightarrow> a ## b\<close>
  assumes disjoint_add_right_commute: \<open>a ## c \<Longrightarrow> b ## a + c \<Longrightarrow> a ## (b + c)\<close>
  assumes positivity: \<open>a ## b \<Longrightarrow> a + b = c \<Longrightarrow> c ## c \<Longrightarrow> c + c = c \<Longrightarrow> a + a = a\<close>
  assumes less_iff_sepadd: \<open>a < b \<longleftrightarrow> a \<noteq> b \<and> (\<exists>c. a ## c \<and> b = a + c)\<close>
begin

lemma le_iff_sepadd_weak: \<open>a \<le> b \<longleftrightarrow> a = b \<or> (\<exists>c. a ## c \<and> b = a + c)\<close>
  using le_less less_iff_sepadd by auto

lemma disjoint_sym_iff: \<open>a ## b \<longleftrightarrow> b ## a\<close>
  using disjoint_sym by blast

lemma partial_le_plus[simp]: \<open>a ## b \<Longrightarrow> a \<le> a + b\<close>
  by (metis less_iff_sepadd nless_le order.refl)

lemma partial_le_plus2[simp]: \<open>a ## b \<Longrightarrow> b \<le> a + b\<close>
  by (metis partial_le_plus disjoint_sym partial_add_commute)

(* TODO: think about decreasing and increasing elements from
    'Bringing order to the separation logic Jungle'.
  All our elements are increasing, I think, because of the above two rules.
*)

lemma common_subresource_selfsep:
  \<open>a ## b \<Longrightarrow> ab \<le> a \<Longrightarrow> ab \<le> b \<Longrightarrow> ab ## ab\<close>
  by (metis disjoint_add_rightL disjoint_sym order.order_iff_strict less_iff_sepadd)

lemma disjoint_add_rightR: \<open>b ## c \<Longrightarrow> a ## b + c \<Longrightarrow> a ## c\<close>
  by (metis disjoint_add_rightL disjoint_sym partial_add_commute)

lemma disjoint_add_leftL: \<open>a ## b \<Longrightarrow> a + b ## c \<Longrightarrow> a ## c\<close>
  using disjoint_add_rightL disjoint_sym by blast

lemma disjoint_add_leftR: \<open>a ## b \<Longrightarrow> a + b ## c \<Longrightarrow> b ## c\<close>
  by (metis disjoint_add_leftL disjoint_sym partial_add_commute)

lemma disjoint_add_commuteL: \<open>c ## b \<Longrightarrow> c + b ## a \<Longrightarrow> a + b ## c\<close>
  by (simp add: disjoint_add_right_commute disjoint_sym)

lemma disjoint_add_swap:
  \<open>b ## c \<Longrightarrow> a ## b + c \<Longrightarrow> a + b ## c\<close>
  using disjoint_add_commuteL disjoint_sym_iff partial_add_commute by auto

lemma disjoint_add_swap2:
  \<open>a ## b \<Longrightarrow> a + b ## c \<Longrightarrow> a ## b + c\<close>
  by (metis disjoint_add_commuteL disjoint_add_leftR disjoint_sym partial_add_commute)

lemma weak_positivity: \<open>a ## b \<Longrightarrow> a + b = c \<Longrightarrow> c ## c \<Longrightarrow> a ## a\<close>
  by (meson disjoint_add_rightL disjoint_sym)

lemma weak_positivityR: \<open>a ## b \<Longrightarrow> a + b = c \<Longrightarrow> c ## c \<Longrightarrow> b ## b\<close>
  using disjoint_sym partial_add_commute weak_positivity by blast

lemma positivityR: \<open>a ## b \<Longrightarrow> a + b = c \<Longrightarrow> c ## c \<Longrightarrow> c + c = c \<Longrightarrow> b + b = b\<close>
  using disjoint_sym partial_add_commute positivity by blast

lemma partial_add_left_commute:
  \<open>a ## b \<Longrightarrow> b ## c \<Longrightarrow> a ## c \<Longrightarrow> b + (a + c) = a + (b + c)\<close>
  by (metis disjoint_sym partial_add_assoc partial_add_commute)

lemma disjoint_preservation:
  \<open>a' \<le> a \<Longrightarrow> a ## b \<Longrightarrow> a' ## b\<close>
  by (metis disjoint_add_leftL order.order_iff_strict less_iff_sepadd)

lemma disjoint_preservation2:
  \<open>b' \<le> b \<Longrightarrow> a ## b \<Longrightarrow> a ## b'\<close>
  using disjoint_preservation disjoint_sym by blast

lemma partial_add_assoc2:
  \<open>a ## b \<Longrightarrow> a + b ## c \<Longrightarrow> (a + b) + c = a + (b + c)\<close>
  using disjoint_add_leftL disjoint_add_leftR partial_add_assoc by blast

lemma partial_add_assoc3:
  \<open>b ## c \<Longrightarrow> a ## b + c \<Longrightarrow> (a + b) + c = a + (b + c)\<close>
  by (meson disjoint_add_rightR disjoint_add_rightL partial_add_assoc)

lemma partial_add_double_assoc:
  \<open>a ## c \<Longrightarrow> b ## d \<Longrightarrow> c ## d \<Longrightarrow> b ## c + d \<Longrightarrow> a ## b + (c + d) \<Longrightarrow> a + b + (c + d) = (a + c) + (b + d)\<close>
  by (metis disjoint_add_rightR disjoint_add_rightL disjoint_add_right_commute partial_add_assoc
      partial_add_left_commute)

lemma sepadd_left_mono:
  \<open>a ## b \<Longrightarrow> a ## c \<Longrightarrow> b \<le> c \<Longrightarrow> a + b \<le> a + c\<close>
  by (simp add: le_iff_sepadd_weak,
      metis disjoint_add_rightR disjoint_add_swap partial_add_assoc)

lemma sepadd_right_mono: \<open>a ## c \<Longrightarrow> b ## c \<Longrightarrow> a \<le> b \<Longrightarrow> a + c \<le> b + c\<close>
  by (metis disjoint_sym_iff partial_add_commute sepadd_left_mono)

subsection \<open> unit_sepadd \<close>

definition \<open>unit_sepadd a \<equiv> a ## a \<and> (\<forall>b. a ## b \<longrightarrow> a + b = b)\<close>

lemma below_unit_impl_unit:
  \<open>a \<le> b \<Longrightarrow> unit_sepadd b \<Longrightarrow> unit_sepadd a\<close>
  unfolding unit_sepadd_def
  by (metis disjoint_add_rightL order.antisym le_iff_sepadd_weak)

lemma units_least: \<open>unit_sepadd x \<Longrightarrow> x ## y \<Longrightarrow> x \<le> y\<close>
  using le_iff_sepadd_weak unit_sepadd_def by auto

lemma almost_units_are_nondisjoint_to_everything:
  \<open>(\<forall>b. a ## b \<longrightarrow> a + b = b) \<Longrightarrow> \<not> a ## a \<Longrightarrow> \<not> a ## b\<close>
  by (metis disjoint_add_leftL disjoint_sym)

lemma units_separate_to_units: \<open>x ## y \<Longrightarrow> unit_sepadd (x + y) \<Longrightarrow> unit_sepadd x\<close>
  using below_unit_impl_unit partial_le_plus by blast

lemma unit_sepadd_left: \<open>unit_sepadd u \<Longrightarrow> u ## a \<Longrightarrow> u + a = a\<close>
  using unit_sepadd_def by auto

lemma unit_sepadd_right: \<open>unit_sepadd u \<Longrightarrow> a ## u \<Longrightarrow> a + u = a\<close>
  by (metis disjoint_sym partial_add_commute unit_sepadd_left)

lemma add_unit_sepadd_add_iff_parts_unit_sepadd[simp]:
  \<open>x ## y \<Longrightarrow> unit_sepadd (x + y) \<longleftrightarrow> unit_sepadd x \<and> unit_sepadd y\<close>
  by (metis unit_sepadd_def units_separate_to_units)

subsection \<open> zero_sepadd \<close>

definition \<open>zero_sepadd a \<equiv> a ## a \<and> (\<forall>b. a ## b \<longrightarrow> a + b = a)\<close>

lemma above_zero_impl_zero:
  \<open>a \<le> b \<Longrightarrow> zero_sepadd a \<Longrightarrow> zero_sepadd b\<close>
  unfolding zero_sepadd_def
  using le_iff_sepadd_weak by force

(* obvious, but a nice dual to the unit case *)
lemma zeros_add_to_zero: \<open>x ## y \<Longrightarrow> zero_sepadd x \<Longrightarrow> zero_sepadd (x + y)\<close>
  by (simp add: zero_sepadd_def)

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

lemma sepconj_iff: \<open>(P \<^emph> Q) r = (\<exists>h1 h2. h1 ## h2 \<and> r = h1 + h2 \<and> P h1 \<and> Q h2)\<close>
  by (simp add: sepconj_def)

definition sepimp :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> (infixr \<open>\<midarrow>\<^emph>\<close> 65) where
  \<open>P \<midarrow>\<^emph> Q \<equiv> \<lambda>h. \<forall>h1. h ## h1 \<longrightarrow> P h1 \<longrightarrow> Q (h + h1)\<close>

definition sepcoimp :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> (infixr \<open>\<sim>\<^emph>\<close> 65) where
  \<open>P \<sim>\<^emph> Q \<equiv> \<lambda>h. \<forall>h1 h2. h1 ## h2 \<longrightarrow> h = h1 + h2 \<longrightarrow> P h1 \<longrightarrow> Q h2\<close>

definition septract :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> (infixr \<open>\<midarrow>\<odot>\<close> 67) where
  \<open>P \<midarrow>\<odot> Q \<equiv> \<lambda>h. \<exists>h1. h ## h1 \<and> P h1 \<and> Q (h + h1)\<close>

definition septract_rev :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> (infixr \<open>\<odot>\<midarrow>\<close> 67) where
  \<open>P \<odot>\<midarrow> Q \<equiv> \<lambda>h. \<exists>h'. h ## h' \<and> P (h + h') \<and> Q h'\<close>

definition subheapexist :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> where
  \<open>subheapexist P \<equiv> \<lambda>h. \<exists>h1. h1 \<le> h \<and> P h1\<close>

subsection \<open> Seplogic connective properties \<close>

lemma septract_reverse: \<open>P \<midarrow>\<odot> Q = Q \<odot>\<midarrow> P\<close>
  by (force simp add: septract_def septract_rev_def)

lemma sepconj_assoc: \<open>(P \<^emph> Q) \<^emph> R = P \<^emph> (Q \<^emph> R)\<close>
  apply (clarsimp simp add: sepconj_def ex_simps[symmetric] partial_add_assoc simp del: ex_simps)
  apply (intro ext iffI)
   apply (metis disjoint_add_leftR disjoint_add_right_commute disjoint_sym partial_add_assoc
      partial_add_commute)+
  done

lemma sepconj_comm: \<open>P \<^emph> Q = Q \<^emph> P\<close>
  unfolding sepconj_def
  by (metis disjoint_sym partial_add_commute)

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
  using disjoint_sym partial_add_commute by fastforce

lemma sepcoimp_curry: \<open>P \<sim>\<^emph> Q \<sim>\<^emph> R = P \<^emph> Q \<sim>\<^emph> R\<close>
  apply (clarsimp simp add: sepcoimp_def sepconj_def)
  apply (intro ext iffI; clarsimp)
   apply (metis disjoint_add_leftR disjoint_add_right_commute disjoint_sym partial_add_assoc
      partial_add_commute)+
  done

lemma sepconj_mono[intro]:
  \<open>P \<le> P' \<Longrightarrow> Q \<le> Q' \<Longrightarrow> P \<^emph> Q \<le> P' \<^emph> Q'\<close>
  using sepconj_def by auto

lemma sepconj_monoL[intro]:
  \<open>P \<le> Q \<Longrightarrow> P \<^emph> R \<le> Q \<^emph> R\<close>
  using sepconj_def by auto

lemma sepconj_monoR[intro]:
  \<open>Q \<le> R \<Longrightarrow> P \<^emph> Q \<le> P \<^emph> R\<close>
  using sepconj_def by auto

lemma sepconj_comm_imp:
  \<open>P \<^emph> Q \<le> Q \<^emph> P\<close>
  by (simp add: sepconj_comm)

lemma sepimp_sepconjL:
  \<open>P \<^emph> Q \<midarrow>\<^emph> R = P \<midarrow>\<^emph> Q \<midarrow>\<^emph> R\<close>
  apply (clarsimp simp add: sepconj_def sepimp_def fun_eq_iff)
  apply (rule iffI)
   apply (metis disjoint_add_rightR disjoint_add_right_commute disjoint_sym partial_add_assoc
      partial_add_commute)+
  done

lemma sepimp_conjR:
  \<open>P \<midarrow>\<^emph> Q \<sqinter> R = (P \<midarrow>\<^emph> Q) \<sqinter> (P \<midarrow>\<^emph> R)\<close>
  by (force simp add: sepimp_def fun_eq_iff)

section \<open> Precision \<close>

definition precise :: \<open>('a \<Rightarrow> bool) \<Rightarrow> bool\<close> where
  \<open>precise P \<equiv> \<forall>h1 h1' h2 h2'.
                  P h1 \<longrightarrow> P h2 \<longrightarrow> h1 ## h1' \<longrightarrow> h2 ## h2' \<longrightarrow> h1 + h1' = h2 + h2' \<longrightarrow>
                  h1 = h2\<close>

(* TODO: rename intuitionistic to bring it in line with the seplogic jungle paper *)
definition intuitionistic :: \<open>('a \<Rightarrow> bool) \<Rightarrow> bool\<close> where
  \<open>intuitionistic P \<equiv> \<forall>h h'. P h \<and> h \<le> h' \<longrightarrow> P h'\<close>

lemma precise_to_intuitionistic:
  \<open>precise P \<Longrightarrow> intuitionistic (P \<^emph> \<top>)\<close>
  apply (simp add: sepconj_def precise_def intuitionistic_def)
  apply (metis le_iff_sepadd_weak order_eq_iff order_trans)
  done

lemma strong_sepcoimp_imp_sepconj:
  \<open>(P \<^emph> \<top>) \<sqinter> (P \<sim>\<^emph> Q) \<le> P \<^emph> Q\<close>
  by (force simp add: sepconj_def sepcoimp_def precise_def le_fun_def)

lemma sepconj_pdisj_distrib_left: \<open>P \<^emph> (Q1 \<squnion> Q2) = P \<^emph> Q1 \<squnion> P \<^emph> Q2\<close>
  by (force simp add: sepconj_def)

lemma sepcoimp_pconj_distrib_left:
  \<open>P \<sim>\<^emph> (Q \<sqinter> Q') = (P \<sim>\<^emph> Q) \<sqinter> (P \<sim>\<^emph> Q')\<close>
  by (force simp add: sepcoimp_def)

lemma sepconj_distrib_conj_iff_sepconj_eq_strong_sepcoimp:
  shows \<open>(\<forall>Q Q'. P \<^emph> (Q \<sqinter> Q') = (P \<^emph> Q) \<sqinter> (P \<^emph> Q')) \<longleftrightarrow> (\<forall>Q. P \<^emph> Q = (P \<^emph> \<top>) \<sqinter> (P \<sim>\<^emph> Q))\<close>
  apply (clarsimp simp add: sepconj_def sepcoimp_def precise_def le_fun_def)
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
  shows \<open>P \<^emph> Q = (P \<^emph> \<top>) \<sqinter> (P \<sim>\<^emph> Q)\<close>
  using assms sepconj_distrib_conj_iff_sepconj_eq_strong_sepcoimp
  by blast


lemma sepconj_middle_monotone_lhsR: \<open>A1 \<^emph> A2 \<le> B \<Longrightarrow> C \<le> D \<Longrightarrow> A1 \<^emph> C \<^emph> A2 \<le> B \<^emph> D\<close>
  by (metis sepconj_assoc sepconj_comm sepconj_mono)

lemma sepconj_middle_monotone_lhsL: \<open>A1 \<^emph> A2 \<le> B \<Longrightarrow> C \<le> D \<Longrightarrow> A1 \<^emph> C \<^emph> A2 \<le> D \<^emph> B\<close>
  by (metis sepconj_assoc sepconj_comm sepconj_mono)

lemma sepconj_middle_monotone_rhsR: \<open>A \<le> B1 \<^emph> B2 \<Longrightarrow> C \<le> D \<Longrightarrow> A \<^emph> C \<le> B1 \<^emph> D \<^emph> B2\<close>
  by (metis sepconj_assoc sepconj_comm sepconj_mono)

lemma sepconj_middle_monotone_rhsL: \<open>A \<le> B1 \<^emph> B2 \<Longrightarrow> C \<le> D \<Longrightarrow> C \<^emph> A \<le> B1 \<^emph> D \<^emph> B2\<close>
  using sepconj_comm sepconj_middle_monotone_rhsR by presburger


lemma sepconj_middle_monotone_lhsR2: \<open>A1 \<^emph> A2 \<le> B \<Longrightarrow> A1 \<^emph> C \<^emph> A2 \<le> B \<^emph> C\<close>
  by (simp add: sepconj_middle_monotone_lhsR)

lemma sepconj_middle_monotone_lhsL2: \<open>A1 \<^emph> A2 \<le> B \<Longrightarrow> A1 \<^emph> C \<^emph> A2 \<le> C \<^emph> B\<close>
  by (simp add: sepconj_middle_monotone_lhsL)

lemma sepconj_middle_monotone_rhsR2: \<open>A \<le> B1 \<^emph> B2 \<Longrightarrow> A \<^emph> C \<le> B1 \<^emph> C \<^emph> B2\<close>
  by (simp add: sepconj_middle_monotone_rhsR)

lemma sepconj_middle_monotone_rhsL2: \<open>A \<le> B1 \<^emph> B2 \<Longrightarrow> C \<^emph> A \<le> B1 \<^emph> C \<^emph> B2\<close>
  by (simp add: sepconj_middle_monotone_rhsL)


definition supported :: \<open>('a \<Rightarrow> bool) \<Rightarrow> bool\<close> where
  \<open>supported P \<equiv> \<forall>s. P s \<longrightarrow> (\<exists>hp. P hp \<and> hp \<le> s \<and> (\<forall>s'. hp \<le> s' \<longrightarrow> s' \<le> s \<longrightarrow> P s'))\<close>

lemma precise_to_supported:
  \<open>precise P \<Longrightarrow> supported (P \<^emph> \<top>)\<close>
  by (metis order.eq_iff supported_def)

end

subsection \<open> Multi-unit Separation Algebras \<close>

class multiunit_sep_alg = perm_alg +
  fixes unitof :: \<open>'a \<Rightarrow> 'a\<close>
  assumes unitof_disjoint[simp,intro!]: \<open>unitof a ## a\<close>
  assumes unitof_is_unit[simp]: \<open>\<And>a b. unitof a ## b \<Longrightarrow> unitof a + b = b\<close>
begin

lemma unitof_disjoint2[simp,intro!]: \<open>a ## unitof a\<close>
  by (simp add: disjoint_sym)

lemma unitof_inherits_disjointness: \<open>a ## b \<Longrightarrow> unitof a ## b\<close>
  by (metis disjoint_add_leftL unitof_disjoint unitof_is_unit)

lemma unitof_is_unit2[simp]: \<open>b ## unitof a \<Longrightarrow> unitof a + b = b\<close>
  by (simp add: disjoint_sym_iff)

lemma unitof_is_unitR[simp]: \<open>unitof a ## b \<Longrightarrow> b + unitof a = b\<close>
  using partial_add_commute unitof_is_unit by presburger

lemma unitof_is_unitR2[simp]: \<open>b ## unitof a \<Longrightarrow> b + unitof a = b\<close>
  by (simp add: disjoint_sym_iff)

lemma unitof_idem[simp]: \<open>unitof (unitof a) = unitof a\<close>
  by (metis unitof_disjoint unitof_is_unit unitof_is_unitR2)

lemma unitof_is_unit_sepadd: \<open>unit_sepadd (unitof a)\<close>
  by (simp add: unit_sepadd_def unitof_inherits_disjointness)

lemma le_iff_sepadd: \<open>a \<le> b \<longleftrightarrow> (\<exists>c. a ## c \<and> b = a + c)\<close>
  by (metis unitof_disjoint2 le_iff_sepadd_weak unitof_is_unitR2)

subsection \<open>partial canonically_ordered_monoid_add lemmas\<close>

lemma unitof_le[simp]: \<open>unitof x \<le> x\<close>
  using partial_le_plus unitof_disjoint by fastforce

lemma le_unitof_eq[simp]: \<open>x \<le> unitof x \<longleftrightarrow> x = unitof x\<close>
  by (auto intro: order.antisym)

lemma not_less_unitof[simp]: \<open>\<not> x < unitof x\<close>
  by (auto simp: less_le)

lemma unitof_less_iff_neq_unitof: \<open>unitof x < x \<longleftrightarrow> x \<noteq> unitof x\<close>
  by (metis antisym_conv2 unitof_le)

lemma gr_unitofI: "(x = unitof x \<Longrightarrow> False) \<Longrightarrow> unitof x < x"
  using unitof_less_iff_neq_unitof by blast

lemma not_gr_unitof[simp]: "\<not> unitof x < x \<longleftrightarrow> x = unitof x"
  by (simp add: unitof_less_iff_neq_unitof)

lemma gr_implies_not_unitof: "m < x \<Longrightarrow> x \<noteq> unitof x"
  by (metis disjoint_preservation dual_order.strict_iff_not partial_le_plus2 unitof_disjoint
      unitof_is_unitR2)

lemma unitof_unit_sepadd:
  \<open>unit_sepadd x \<Longrightarrow> unitof x = x\<close>
  by (metis unit_sepadd_def unitof_disjoint2 unitof_is_unitR2)

lemma sepadd_eq_unitof_iff_both_eq_unitof[simp]:
  \<open>x ## y \<Longrightarrow> x + y = unitof (x + y) \<longleftrightarrow> x = unitof x \<and> y = unitof y\<close>
  by (metis gr_implies_not_unitof dual_order.not_eq_order_implies_strict partial_le_plus2
      unitof_is_unitR2)

lemma unitof_eq_sepadd_iff_both_eq_unitof[simp]:
  \<open>x ## y \<Longrightarrow> unitof (x + y) = x + y \<longleftrightarrow> x = unitof x \<and> y = unitof y\<close>
  by (metis sepadd_eq_unitof_iff_both_eq_unitof)

lemma disjoint_same_unit:
  \<open>a ## b \<Longrightarrow> unitof a = unitof b\<close>
  by (metis disjoint_sym_iff unitof_inherits_disjointness unitof_is_unit2 unitof_is_unitR2)

lemma common_disjoint_same_unit:
  \<open>a ## c \<Longrightarrow> b ## c \<Longrightarrow> unitof a = unitof b\<close>
  by (metis disjoint_sym_iff unitof_inherits_disjointness unitof_is_unit2 unitof_is_unitR2)

lemmas unitof_order = unitof_le le_unitof_eq not_less_unitof unitof_less_iff_neq_unitof not_gr_unitof

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


definition emp :: \<open>'a \<Rightarrow> bool\<close> where
  \<open>emp \<equiv> unit_sepadd\<close>

definition emp_mfault :: \<open>('a \<Rightarrow> bool) mfault\<close> ("emp\<^sub>f") where
  \<open>emp\<^sub>f \<equiv> Success emp\<close>

fun iterated_sepconj :: \<open>('a \<Rightarrow> bool) list \<Rightarrow> ('a \<Rightarrow> bool)\<close> where
  \<open>iterated_sepconj (P # Ps) = P \<^emph> iterated_sepconj Ps\<close>
| \<open>iterated_sepconj [] = emp\<close>

lemma emp_sepconj_unit[simp]: \<open>emp \<^emph> P = P\<close>
  apply (simp add: emp_def sepconj_def unit_sepadd_def fun_eq_iff)
  apply (metis disjoint_sym partial_add_commute unitof_disjoint unitof_is_unitR2)
  done

lemma emp_sepconj_unit_right[simp]: \<open>P \<^emph> emp = P\<close>
  using emp_sepconj_unit sepconj_comm by force

lemma secoimp_imp_sepconj:
  \<open>P \<sqinter> (P \<sim>\<^emph> Q) \<le> P \<^emph> (Q \<sqinter> emp)\<close>
  apply (simp add: sepcoimp_def sepconj_def le_fun_def emp_def unit_sepadd_def)
  apply (metis unit_sepadd_def unitof_disjoint2 unitof_is_unitR2 unitof_is_unit_sepadd)
  done

lemma not_coimp_emp:
  \<open>\<not> unit_sepadd h \<Longrightarrow> (- (\<top> \<sim>\<^emph> emp)) h\<close>
  by (force simp add: sepcoimp_def emp_def)

lemma supported_intuitionistic_to_precise:
  \<open>supported P \<Longrightarrow> intuitionistic P \<Longrightarrow> precise (P \<sqinter> - (P \<^emph> (-emp)))\<close>
  nitpick[card=4]
  oops

end

subsection \<open> Separation Algebras (with a single unit) \<close>

class sep_alg = multiunit_sep_alg + disjoint_zero + order_bot +
  assumes sepadd_0[simp]: \<open>0 + a = a\<close>
begin

lemma sepadd_0_right[simp]: "a + 0 = a"
  by (metis zero_disjointR sepadd_0 partial_add_commute)

lemma unitof_zero[simp]: \<open>unitof a = 0\<close>
  by (metis sepadd_0 unitof_is_unitR zero_disjointR)

lemma zero_only_unit[simp]:
  \<open>unit_sepadd x \<longleftrightarrow> x = 0\<close>
  by (metis unitof_is_unit_sepadd unitof_unit_sepadd unitof_zero)

subsection \<open>partial canonically_ordered_monoid_add lemmas\<close>

lemma zero_le[simp]: \<open>0 \<le> x\<close>
  using unitof_le by force

lemma le_zero_eq[simp]: "n \<le> 0 \<longleftrightarrow> n = 0"
  using le_unitof_eq by force

lemma not_less_zero[simp]: "\<not> n < 0"
  by (auto simp: less_le)

lemma zero_less_iff_neq_zero: "0 < n \<longleftrightarrow> n \<noteq> 0"
  by (auto simp: less_le)

lemma gr_zeroI: "(n = 0 \<Longrightarrow> False) \<Longrightarrow> 0 < n"
  using zero_less_iff_neq_zero by auto

lemma not_gr_zero[simp]: "\<not> 0 < n \<longleftrightarrow> n = 0"
  by (simp add: zero_less_iff_neq_zero)

lemma gr_implies_not_zero: \<open>m < n \<Longrightarrow> n \<noteq> 0\<close>
  by auto

lemma sepadd_eq_0_iff_both_eq_0[simp]: \<open>x ## y \<Longrightarrow> x + y = 0 \<longleftrightarrow> x = 0 \<and> y = 0\<close>
  by (metis partial_le_plus le_zero_eq sepadd_0)

lemma zero_eq_sepadd_iff_both_eq_0[simp]: \<open>x ## y \<Longrightarrow> 0 = x + y \<longleftrightarrow> x = 0 \<and> y = 0\<close>
  using sepadd_eq_0_iff_both_eq_0 by fastforce

lemmas zero_order = zero_le le_zero_eq not_less_zero zero_less_iff_neq_zero not_gr_zero

paragraph \<open> Separation Logic \<close>

lemma not_coimp_emp0:
  \<open>h \<noteq> 0 \<Longrightarrow> (- (\<top> \<sim>\<^emph> emp)) h\<close>
  apply (clarsimp simp add: sepcoimp_def emp_def)
  apply (rule_tac x=0 in exI, force)
  done

end

section \<open> Permission/Separation Algebra Subclasses \<close>

section \<open> compatibility \<close>

context perm_alg
begin

definition compatible :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> where
  \<open>compatible \<equiv> (##)\<^sup>*\<^sup>*\<close>

lemma compatible_refl[intro!]:
  \<open>compatible a a\<close>
  by (simp add: compatible_def)

lemma compatible_refl_iff[simp]:
  \<open>compatible a a \<longleftrightarrow> True\<close>
  by (simp add: compatible_def)

lemma compatible_sym:
  assumes \<open>compatible a b\<close>
  shows \<open>compatible b a\<close>
proof -
  have \<open>(##)\<^sup>*\<^sup>* = ((##)\<inverse>\<inverse>)\<^sup>*\<^sup>*\<close>
    by (metis disjoint_sym sympI symp_conv_conversep_eq)
  also have \<open>... = (##)\<^sup>*\<^sup>*\<inverse>\<inverse>\<close>
    by (simp add: rtranclp_conversep)
  finally show ?thesis
    by (metis assms compatible_def conversep_iff)
qed

lemma compatible_trans:
  \<open>compatible a b \<Longrightarrow> compatible b c \<Longrightarrow> compatible a c\<close>
  by (simp add: compatible_def)

lemma disjoint_is_compatible:
  \<open>a ## b \<Longrightarrow> compatible a b\<close>
  by (simp add: compatible_def)

lemma trans_disjoint_is_compatible:
  \<open>a ## b \<Longrightarrow> b ## c \<Longrightarrow> compatible a c\<close>
  by (simp add: compatible_def)

lemma disjoint_units_identical:
  \<open>a ## b \<Longrightarrow> unit_sepadd a \<Longrightarrow> unit_sepadd b \<Longrightarrow> a = b\<close>
  by (metis disjoint_sym partial_add_commute unit_sepadd_def)

lemma trans_disjoint_units_identical:
  \<open>a ## b \<Longrightarrow> b ## c \<Longrightarrow> unit_sepadd a \<Longrightarrow> unit_sepadd c \<Longrightarrow> a = c\<close>
  by (metis disjoint_units_identical disjoint_add_leftL unit_sepadd_def)

lemma trans_compatible_units_identical:
  \<open>compatible b z \<Longrightarrow> a ## b \<Longrightarrow> unit_sepadd a \<Longrightarrow> unit_sepadd z \<Longrightarrow> a = z\<close>
  unfolding compatible_def
  apply (induct rule: converse_rtranclp_induct)
  apply (force dest: disjoint_units_identical)
  apply (metis disjoint_add_leftL unit_sepadd_def)
  done

lemma compatible_units_identical:
  \<open>compatible a z \<Longrightarrow> unit_sepadd a \<Longrightarrow> unit_sepadd z \<Longrightarrow> a = z\<close>
  by (metis compatible_def converse_rtranclpE trans_compatible_units_identical)

lemma implies_compatible_then_rtranscl_implies_compatible:
  \<open>\<forall>x y. r x y \<longrightarrow> compatible x y \<Longrightarrow> r\<^sup>*\<^sup>* x y \<Longrightarrow> compatible x y\<close>
  using implies_rel_then_rtranscl_implies_rel[of r _ _ compatible]
    compatible_trans
  by blast

lemma implies_compatible_then_rtranscl_implies_compatible2:
  \<open>r \<le> compatible \<Longrightarrow> r\<^sup>*\<^sup>* \<le> compatible\<close>
  using implies_rel_then_rtranscl_implies_rel[of r _ _ compatible]
    compatible_trans
  by blast

end

(* almost a sep_alg, in that if there was a unit, it would be a sep-algebra *)
class allcompatible_perm_alg = perm_alg +
  assumes all_compatible: \<open>compatible a b\<close>
begin

lemma all_units_eq:
  \<open>unit_sepadd a \<Longrightarrow> unit_sepadd b \<Longrightarrow> a = b\<close>
  by (simp add: all_compatible compatible_units_identical)

end

context multiunit_sep_alg
begin

lemma same_unit_compatible:
  \<open>unitof a = unitof b \<Longrightarrow> compatible a b\<close>
  by (metis trans_disjoint_is_compatible unitof_disjoint unitof_disjoint2)

lemma compatible_then_same_unit:
  \<open>compatible a b \<Longrightarrow> unitof a = unitof b\<close>
  by (metis compatible_def trans_compatible_units_identical unitof_disjoint unitof_disjoint2
      unitof_is_unit_sepadd rtranclp.rtrancl_into_rtrancl)

end

(* compatible multiunit sep algebras collapse *)
class allcompatible_multiunit_sep_alg = allcompatible_perm_alg + multiunit_sep_alg
begin

lemma exactly_one_unit: \<open>\<exists>!u. unit_sepadd u\<close>
  using all_compatible compatible_units_identical unitof_is_unit_sepadd by blast

definition \<open>the_unit \<equiv> The unit_sepadd\<close>

lemma the_unit_is_a_unit:
  \<open>unit_sepadd the_unit\<close>
  unfolding the_unit_def
  by (rule theI', simp add: exactly_one_unit)

lemma is_sep_alg:
  \<open>class.sep_alg the_unit (\<le>) (<) the_unit (##) (+) (\<lambda>_. the_unit)\<close>
  apply standard
      apply (metis exactly_one_unit unitof_is_unit_sepadd unitof_le the_unit_is_a_unit)
     apply (metis exactly_one_unit unitof_disjoint unitof_is_unit_sepadd the_unit_is_a_unit)
    apply (metis exactly_one_unit unitof_disjoint2 unitof_is_unit_sepadd the_unit_is_a_unit)
   apply (metis exactly_one_unit unitof_disjoint2 unitof_is_unit2 unitof_is_unit_sepadd
      the_unit_is_a_unit)
  apply (metis exactly_one_unit unitof_disjoint2 unitof_is_unit2 unitof_is_unit_sepadd
      the_unit_is_a_unit)
  done

end

context sep_alg
begin

subclass allcompatible_perm_alg
  by standard
    (simp add: same_unit_compatible)

end

subsection \<open>Strongly Separated Separation Algebra\<close>

class strong_sep_perm_alg = perm_alg +
  assumes selfsep_implies_unit: \<open>a ## a \<Longrightarrow> unit_sepadd a\<close>
begin

lemma selfsep_iff:
  \<open>a ## a \<longleftrightarrow> unit_sepadd a\<close>
  using selfsep_implies_unit unit_sepadd_def by blast

end

class strong_sep_multiunit_sep_alg = multiunit_sep_alg + strong_sep_perm_alg
begin

lemma mu_selfsep_iff: \<open>a ## a \<longleftrightarrow> unitof a = a\<close>
  by (metis selfsep_iff unitof_disjoint unitof_unit_sepadd)

lemma mu_selfsep_implies_unit: \<open>a ## a \<Longrightarrow> unitof a = a\<close>
  by (metis mu_selfsep_iff)

end

class strong_separated_sep_alg = sep_alg + strong_sep_multiunit_sep_alg
begin

lemma sepalg_selfsep_iff: \<open>a ## a \<longleftrightarrow> a = 0\<close>
  by (simp add: selfsep_iff)

lemma sepalg_selfsep_implies_unit: \<open>a ## a \<Longrightarrow> a = 0\<close>
  by (metis sepalg_selfsep_iff)

end

subsection \<open> Disjoint Parts Algebra \<close>

class disjoint_parts_perm_alg = perm_alg +
  assumes disjointness_left_plusI: \<open>a ## b \<Longrightarrow> a ## c \<Longrightarrow> b ## c \<Longrightarrow> a + b ## c\<close>
begin

lemmas disjointness_left_plusI' =
  disjointness_left_plusI
  disjointness_left_plusI[OF disjoint_sym]
  disjointness_left_plusI[OF _ disjoint_sym]
  disjointness_left_plusI[OF _ _ disjoint_sym]
  disjointness_left_plusI[OF _ disjoint_sym disjoint_sym]
  disjointness_left_plusI[OF disjoint_sym _ disjoint_sym]
  disjointness_left_plusI[OF disjoint_sym disjoint_sym]
  disjointness_left_plusI[OF disjoint_sym disjoint_sym disjoint_sym]

lemma disjointness_right_plusI:
  \<open>a ## b \<Longrightarrow> a ## c \<Longrightarrow> b ## c \<Longrightarrow> a ## b + c\<close>
  using disjointness_left_plusI disjoint_sym by auto

lemmas disjointness_right_plusI' =
  disjointness_right_plusI
  disjointness_right_plusI[OF disjoint_sym]
  disjointness_right_plusI[OF _ disjoint_sym]
  disjointness_right_plusI[OF _ _ disjoint_sym]
  disjointness_right_plusI[OF _ disjoint_sym disjoint_sym]
  disjointness_right_plusI[OF disjoint_sym _ disjoint_sym]
  disjointness_right_plusI[OF disjoint_sym disjoint_sym]
  disjointness_right_plusI[OF disjoint_sym disjoint_sym disjoint_sym]

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

class disjoint_parts_multiunit_sep_alg = multiunit_sep_alg + disjoint_parts_perm_alg

class disjoint_parts_sep_alg = sep_alg + disjoint_parts_multiunit_sep_alg

subsection \<open> weak glb / lub \<close>

context perm_alg
begin

definition
  \<open>glb_exists a b \<equiv> \<exists>ab. ab \<le> a \<and> ab \<le> b \<and> (\<forall>ab'. ab' \<le> a \<longrightarrow> ab' \<le> b \<longrightarrow> ab' \<le> ab)\<close>

definition \<open>glb a b \<equiv> (GREATEST ab. ab \<le> a \<and> ab \<le> b)\<close>

definition
  \<open>lub_exists a b \<equiv> \<exists>ab. a \<le> ab \<and> b \<le> ab \<and> (\<forall>ab'. a \<le> ab' \<longrightarrow> b \<le> ab' \<longrightarrow> ab \<le> ab')\<close>

definition \<open>lub a b \<equiv> (LEAST ab. a \<le> ab \<and> b \<le> ab)\<close>


lemma lub_glb_distrib_weak:
  assumes
    \<open>glb_exists b c\<close>
    \<open>lub_exists a (glb b c)\<close>
    \<open>lub_exists a b\<close>
    \<open>lub_exists a c\<close>
    \<open>glb_exists (lub a b) (lub a c)\<close>
  shows
    \<open>lub a (glb b c) \<le> glb (lub a b) (lub a c)\<close>
  using assms
  unfolding glb_exists_def lub_exists_def lub_def glb_def
  by (clarsimp simp add: Greatest_equality Least_equality)

lemma lub_glb_distrib_strong:
  assumes
    \<open>glb_exists b c\<close>
    \<open>lub_exists a (glb b c)\<close>
    \<open>lub_exists a b\<close>
    \<open>lub_exists a c\<close>
    \<open>glb_exists (lub a b) (lub a c)\<close>
  shows
    \<open>glb (lub a b) (lub a c) \<le> lub a (glb b c)\<close>
  text \<open> not true \<close>
  nitpick
  oops

lemma glb_lub_distrib_weak:
  assumes
    \<open>glb_exists a b\<close>
    \<open>glb_exists a c\<close>
    \<open>lub_exists (glb a b) (glb a c)\<close>
    \<open>lub_exists b c\<close>
    \<open>glb_exists a (lub b c)\<close>
  shows
  \<open>lub (glb a b) (glb a c) \<le> glb a (lub b c)\<close>
  using assms
  unfolding glb_exists_def lub_exists_def lub_def glb_def
  by (force simp add: Greatest_equality Least_equality)

lemma glb_lub_distrib_strong:
  assumes
    \<open>glb_exists a b\<close>
    \<open>glb_exists a c\<close>
    \<open>lub_exists (glb a b) (glb a c)\<close>
    \<open>lub_exists b c\<close>
    \<open>glb_exists a (lub b c)\<close>
  shows
  \<open>glb a (lub b c) \<le> lub (glb a b) (glb a c)\<close>
  text \<open> not true! \<close>
  oops

paragraph \<open> with addition \<close>

lemma \<open>a ## b \<Longrightarrow> lub_exists a b \<Longrightarrow> lub a b \<le> a + b\<close>
  unfolding lub_exists_def lub_def
  by (auto simp add: Least_equality)

lemma \<open>a ## b \<Longrightarrow> lub_exists a b \<Longrightarrow> lub a b \<ge> a + b\<close>
  text \<open> not true! \<close>
  oops


lemma add_glb_distrib_weak:
  assumes
    \<open>glb_exists b c\<close>
    \<open>a ## (glb b c)\<close>
    \<open>a ## b\<close>
    \<open>a ## c\<close>
    \<open>glb_exists (a + b) (a + c)\<close>
  shows
    \<open>a + (glb b c) \<le> glb (a + b) (a + c)\<close>
  using assms
  unfolding glb_exists_def glb_def
  by (clarsimp simp add: Greatest_equality, metis sepadd_left_mono)

lemma add_glb_distrib_strong:
  assumes
    \<open>glb_exists b c\<close>
    \<open>a ## (glb b c)\<close>
    \<open>a ## b\<close>
    \<open>a ## c\<close>
    \<open>glb_exists (a + b) (a + c)\<close>
  shows
    \<open>glb (a + b) (a + c) \<le> a + (glb b c)\<close>
  text \<open> not true \<close>
  nitpick
  oops

lemma glb_add_distrib_weak:
  assumes
    \<open>glb_exists a b\<close>
    \<open>glb_exists a c\<close>
    \<open>(glb a b) ## (glb a c)\<close>
    \<open>b ## c\<close>
    \<open>glb_exists a (b + c)\<close>
  shows
    \<open>(glb a b) + (glb a c) \<le> glb a (b + c)\<close>
  text \<open> not true \<close>
  nitpick
  oops

lemma glb_add_distrib_strong:
  assumes
    \<open>glb_exists a b\<close>
    \<open>glb_exists a c\<close>
    \<open>(glb a b) ## (glb a c)\<close>
    \<open>b ## c\<close>
    \<open>glb_exists a (b + c)\<close>
  shows
  \<open>glb a (b + c) \<le> (glb a b) + (glb a c)\<close>
  text \<open> not true \<close>
  nitpick
  oops

end

subsection \<open> Separation Algebras with glb \<close>

class inf_perm_alg = perm_alg + inf +
  assumes sepinf_leqL[intro]: \<open>compatible a b \<Longrightarrow> a \<sqinter> b \<le> a\<close>
    and sepinf_leqR[intro]: \<open>compatible a b \<Longrightarrow> a \<sqinter> b \<le> b\<close>
    and sepinf_least[intro]: \<open>compatible a b \<Longrightarrow> c \<le> a \<Longrightarrow> c \<le> b \<Longrightarrow> c \<le> a \<sqinter> b\<close>
begin

lemma sepinf_disjointL: \<open>a ## b \<Longrightarrow> compatible a c \<Longrightarrow> a \<sqinter> c ## b\<close>
  using disjoint_preservation by blast

lemma sepinf_disjointR: \<open>a ## b \<Longrightarrow> compatible b c \<Longrightarrow> a ## b \<sqinter> c\<close>
  using disjoint_preservation2 by blast

lemma sepinf_preserves_compatibleL:
  \<open>compatible a b \<Longrightarrow> compatible a c \<Longrightarrow> compatible (a \<sqinter> b) c\<close>
  by (metis converse_rtranclpE compatible_def compatible_trans disjoint_sym_iff le_iff_sepadd_weak
      sepinf_least trans_disjoint_is_compatible sepinf_disjointL)

lemma sepinf_preserves_compatibleL2:
  \<open>compatible a b \<Longrightarrow> compatible b c \<Longrightarrow> compatible (a \<sqinter> b) c\<close>
  using compatible_trans sepinf_preserves_compatibleL by blast

lemma sepinf_preserves_compatibleL3:
  \<open>compatible a c \<Longrightarrow> compatible b c \<Longrightarrow> compatible (a \<sqinter> b) c\<close>
  by (meson compatible_sym compatible_trans sepinf_preserves_compatibleL)

lemma sepinf_preserves_compatibleR:
  \<open>compatible b c \<Longrightarrow> compatible a b \<Longrightarrow> compatible a (b \<sqinter> c)\<close>
  by (metis converse_rtranclpE compatible_def compatible_trans disjoint_sym_iff le_iff_sepadd_weak
      sepinf_least trans_disjoint_is_compatible sepinf_disjointL)

lemma sepinf_preserves_compatibleR2:
  \<open>compatible b c \<Longrightarrow> compatible a c \<Longrightarrow> compatible a (b \<sqinter> c)\<close>
  by (meson compatible_sym sepinf_preserves_compatibleL2)

lemma sepinf_preserves_compatibleR3:
  \<open>compatible a b \<Longrightarrow> compatible a c \<Longrightarrow> compatible a (b \<sqinter> c)\<close>
  by (meson compatible_sym sepinf_preserves_compatibleL3)


lemma sepinf_idem[simp]: \<open>a \<sqinter> a = a\<close>
  by (simp add: order_antisym sepinf_least sepinf_leqR)

lemma sepinf_assoc[simp]:
  \<open>compatible a b \<Longrightarrow> compatible b c \<Longrightarrow> a \<sqinter> (b \<sqinter> c) = a \<sqinter> b \<sqinter> c\<close>
  apply (subgoal_tac \<open>compatible (a \<sqinter> b) c\<close>)
   prefer 2
   apply (metis converse_rtranclpE compatible_def disjoint_preservation disjoint_sym sepinf_idem 
      sepinf_leqL trans_disjoint_is_compatible rtranclp_trans)
  apply (subgoal_tac \<open>compatible a (b \<sqinter> c)\<close>)
   prefer 2
   apply (metis converse_rtranclpE compatible_def disjoint_preservation disjoint_sym sepinf_idem 
      sepinf_leqL trans_disjoint_is_compatible rtranclp_trans)
  apply (meson order.antisym order.trans sepinf_least sepinf_leqL sepinf_leqR; fail)
  done

lemma disjoint_sepinf_of_add_impl_disjoint_sepinf_part:
  \<open>a ## b \<Longrightarrow>
    compatible a c \<Longrightarrow>
    compatible (a + b) c \<Longrightarrow>
    (a + b) \<sqinter> c ## y \<Longrightarrow>
    a \<sqinter> c ## y\<close>
  by (meson disjoint_preservation order.trans partial_le_plus sepinf_least sepinf_leqL sepinf_leqR)

lemma sepinf_of_unit_is_unit:
  \<open>compatible a b \<Longrightarrow> unit_sepadd a \<Longrightarrow> unit_sepadd (a \<sqinter> b)\<close>
  using below_unit_impl_unit by blast

lemma sepinf_of_unit_eq_that_unit[simp]:
  \<open>compatible a b \<Longrightarrow> unit_sepadd a \<Longrightarrow> a \<sqinter> b = a\<close>
  by (meson sepinf_of_unit_is_unit compatible_refl disjoint_preservation sepinf_leqL
      trans_compatible_units_identical unit_sepadd_def)

lemma sepinf_of_unit_eq_that_unit2[simp]:
  \<open>compatible a b \<Longrightarrow> unit_sepadd b \<Longrightarrow> a \<sqinter> b = b\<close>
  by (metis disjoint_preservation2 order.antisym partial_le_plus sepinf_leqR unit_sepadd_def)

end


class allcompatible_inf_perm_alg = inf_perm_alg + allcompatible_perm_alg
begin

subclass semilattice_inf
  by standard
    (simp add: all_compatible sepinf_leqL sepinf_leqR sepinf_least)+

end

class inf_multiunit_sep_alg = multiunit_sep_alg + inf_perm_alg

class inf_sep_alg = sep_alg + inf_multiunit_sep_alg
begin

subclass allcompatible_inf_perm_alg
  by standard

end

subsubsection \<open> distributive glb/add \<close>

(* TODO: generalise this to non-compatible algebras *)
class distrib_perm_alg = allcompatible_inf_perm_alg +
  assumes inf_add_distrib1:
    \<open>\<And>x a b. a ## b \<Longrightarrow> x \<sqinter> (a + b) = (x \<sqinter> a) + (x \<sqinter> b)\<close>
begin

lemma left_inf_preserves_disjoint:
  \<open>a ## b \<Longrightarrow> (x \<sqinter> a) ## (x \<sqinter> b)\<close>
  by (meson disjoint_preservation disjoint_sym inf.cobounded2)

lemma inf_add_distrib2:
    \<open>\<And>x a b. a ## b \<Longrightarrow> (a + b) \<sqinter> x = (a \<sqinter> x) + (b \<sqinter> x)\<close>
  by (simp add: inf_add_distrib1 inf_commute)

end

(* multiunit algebras collapse to a sep alg *)

class distrib_sep_alg = sep_alg + distrib_perm_alg

subsection \<open>Trivial Self-disjointness Separation Algebra\<close>

class trivial_selfdisjoint_perm_alg = perm_alg +
  assumes disjointness: \<open>a ## a \<Longrightarrow> a + a = b \<Longrightarrow> a = b\<close>

class trivial_selfdisjoint_multiunit_sep_alg = multiunit_sep_alg + trivial_selfdisjoint_perm_alg

class trivial_selfdisjoint_sep_alg = sep_alg + trivial_selfdisjoint_multiunit_sep_alg

subsection \<open>Cross-Split Separation Algebra\<close>

class crosssplit_perm_alg = perm_alg +
  assumes cross_split:
  \<open>a ## b \<Longrightarrow> c ## d \<Longrightarrow> a + b = z \<Longrightarrow> c + d = z \<Longrightarrow>
    \<exists>ac ad bc bd.
      ac ## ad \<and> bc ## bd \<and> ac ## bc \<and> ad ## bd \<and>
      ac + ad = a \<and> bc + bd = b \<and> ac + bc = c \<and> ad + bd = d\<close>

class crosssplit_multiunit_sep_alg = multiunit_sep_alg + crosssplit_perm_alg

class crosssplit_sep_alg = sep_alg + crosssplit_multiunit_sep_alg

subsection \<open>Cancellative Separation Logic\<close>

class cancel_perm_alg = perm_alg +
  assumes partial_right_cancel[simp]: \<open>\<And>a b c. a ## c \<Longrightarrow> b ## c \<Longrightarrow> (a + c = b + c) = (a = b)\<close>
begin

lemma partial_right_cancel2[simp]:
  \<open>c ## a \<Longrightarrow> c ## b \<Longrightarrow> (a + c = b + c) = (a = b)\<close>
  using partial_right_cancel disjoint_sym
  by force

lemma partial_left_cancel[simp]:
  \<open>a ## c \<Longrightarrow> b ## c \<Longrightarrow> (c + a = c + b) = (a = b)\<close>
  by (metis partial_add_commute partial_right_cancel)

lemma partial_left_cancel2[simp]:
  \<open>c ## a \<Longrightarrow> c ## b \<Longrightarrow> (c + a = c + b) = (a = b)\<close>
  using partial_left_cancel disjoint_sym
  by force

lemmas partial_right_cancelD = iffD1[OF partial_right_cancel, rotated 2]
lemmas partial_right_cancel2D = iffD1[OF partial_right_cancel2, rotated 2]
lemmas partial_left_cancelD = iffD1[OF partial_left_cancel, rotated 2]
lemmas partial_left_cancel2D = iffD1[OF partial_left_cancel2, rotated 2]

lemma cancel_right_to_unit:
  assumes
    \<open>a ## b\<close>
    \<open>a + b = b\<close>
  shows \<open>unit_sepadd a\<close>
  unfolding unit_sepadd_def
proof (intro conjI allI impI)
  show Daa: \<open>a ## a\<close>
    using assms
    by (metis disjoint_add_rightL)

  fix c
  assume D0:
    \<open>a ## c\<close>

  have E1: \<open>a = a + a\<close>
  proof -
    have \<open>b ## a + a\<close>
      using assms
      by (simp add: disjoint_add_swap disjoint_sym)
    moreover have \<open>b + a = b + (a + a)\<close>
      using assms
      by (metis partial_add_assoc3 partial_add_commute disjoint_add_swap disjoint_sym)
    ultimately show ?thesis
      using assms
      by (simp add: disjoint_sym_iff)
  qed

  have D1: \<open>c + a ## a\<close>
    using assms D0 E1 Daa
    by (metis disjoint_add_commuteL)

  have \<open>a + c = a + (c + a)\<close>
    using assms D0 E1 Daa
    by (metis partial_add_assoc partial_add_commute)
  then show \<open>a + c = c\<close>
    using D0 D1
    by (metis partial_left_cancelD disjoint_sym partial_add_commute)
qed

lemma cancel_left_to_unit:
  \<open>a ## b \<Longrightarrow> a + b = a \<Longrightarrow> unit_sepadd b\<close>
  by (metis cancel_right_to_unit disjoint_sym partial_add_commute)

paragraph \<open> Seplogic \<close>

lemma precise_iff_conj_distrib:
  fixes P :: \<open>'a \<Rightarrow> bool\<close>
  shows \<open>precise P \<longleftrightarrow> (\<forall>Q Q'. P \<^emph> (Q \<sqinter> Q') = (P \<^emph> Q) \<sqinter> (P \<^emph> Q'))\<close>
proof (rule iffI)
  assume distrib_assm: \<open>\<forall>Q Q'. P \<^emph> (Q \<sqinter> Q') = (P \<^emph> Q) \<sqinter> (P \<^emph> Q')\<close>
  show \<open>precise P\<close>
  proof (clarsimp simp add: precise_def)
    fix h1 h1' h2 h2'
    assume precise_assms:
      \<open>h1 + h1' = h2 + h2'\<close>
      \<open>h1 ## h1'\<close>
      \<open>h2 ## h2'\<close>
      \<open>P h1\<close>
      \<open>P h2\<close>

    have \<open>(P \<^emph> ((=) h1')) (h2+h2')\<close>
      using precise_assms partial_add_commute disjoint_sym sepconj_def
      by (metis (mono_tags, lifting))
    moreover have \<open>(P \<^emph> ((=) h2')) (h2+h2')\<close>
      using precise_assms partial_add_commute disjoint_sym sepconj_def
      by (metis (mono_tags, lifting))
    ultimately have \<open>(P \<^emph> ((=) h1' \<sqinter> (=) h2')) (h2+h2')\<close>
      using distrib_assm precise_assms
      by simp
    then show \<open>h1 = h2\<close>
      using precise_assms disjoint_sym
      by (force dest: partial_right_cancelD simp add: sepconj_def)
  qed
next
  assume precise_assm: \<open>precise P\<close>
  then show \<open>\<forall>Q Q'. P \<^emph> (Q \<sqinter> Q') = (P \<^emph> Q) \<sqinter> (P \<^emph> Q')\<close>
    by (simp add: sepconj_def precise_def fun_eq_iff, blast dest: partial_left_cancel2)
qed

lemma precise_iff_all_sepconj_imp_sepcoimp:
  shows \<open>precise P \<longleftrightarrow> (\<forall>Q. P \<^emph> Q \<le> P \<sim>\<^emph> Q)\<close>
  apply (clarsimp simp add: sepconj_def sepcoimp_def precise_def le_fun_def)
  apply (rule iffI)
   apply (metis partial_left_cancel2)
  apply (metis le_less order.irrefl partial_right_cancel)
  done

lemma precise_sepconj_eq_strong_sepcoimp:
  shows \<open>precise P \<Longrightarrow> P \<^emph> Q = (P \<^emph> \<top>) \<sqinter> (P \<sim>\<^emph> Q)\<close>
  apply (clarsimp simp add: sepconj_def sepcoimp_def precise_def le_fun_def)
  apply (rule ext)
  apply (rule iffI)
  apply (blast dest: partial_left_cancel2)
  apply blast
  done

end

class cancel_multiunit_sep_alg = cancel_perm_alg + multiunit_sep_alg
begin

lemma selfsep_selfadd_iff_unit:
  \<open>a ## a \<and> a + a = a \<longleftrightarrow> unit_sepadd a\<close>
  by (metis partial_right_cancelD unitof_disjoint2 unitof_inherits_disjointness unitof_is_unit2
      unitof_is_unit_sepadd unitof_unit_sepadd)

lemma strong_positivity:
  \<open>a ## b \<Longrightarrow> c ## c \<Longrightarrow> a + b = c \<Longrightarrow> c + c = c \<Longrightarrow> a = b \<and> b = c\<close>
  by (metis partial_right_cancelD positivity unit_sepadd_def weak_positivity
      selfsep_selfadd_iff_unit)

lemma \<open>(a \<^emph> \<top>) \<sqinter> (b \<^emph> \<top>) \<le> ((a \<^emph> b) \<squnion> (a \<sqinter> b)) \<^emph> \<top>\<close>
  nitpick[card=4]
  oops

lemma \<open>((a \<^emph> b) \<squnion> (a \<sqinter> b)) \<^emph> \<top> \<le> (a \<^emph> \<top>) \<sqinter> (b \<^emph> \<top>)\<close>
proof -
  have F1: \<open>((a \<^emph> b) \<squnion> (a \<sqinter> b)) \<^emph> \<top> = (a \<^emph> b) \<^emph> \<top> \<squnion> (a \<sqinter> b) \<^emph> \<top>\<close>
    by (simp add: sepconj_comm sepconj_pdisj_distrib_left)
  moreover have \<open>a \<^emph> b \<^emph> \<top> \<le> (a \<^emph> \<top>) \<sqinter> (b \<^emph> \<top>)\<close>
    by (metis le_infI sepconj_comm sepconj_middle_monotone_lhsL2 top_greatest)
  moreover have \<open>(a \<sqinter> b) \<^emph> \<top> \<le> (a \<^emph> \<top>) \<sqinter> (b \<^emph> \<top>)\<close>
    by (simp add: sepconj_monoL)
  ultimately show ?thesis
    by simp
qed

end

class cancel_sep_alg = cancel_multiunit_sep_alg + sep_alg

subsection \<open>No-unit perm alg\<close>

text \<open>
  Here we create a perm_alg without any unit.
  Such an algebra is necessary to prove permission heaps are cancellative.
\<close>
class no_unit_perm_alg = perm_alg +
  assumes no_units: \<open>\<not> unit_sepadd a\<close>

class cancel_no_unit_perm_alg = no_unit_perm_alg + cancel_perm_alg
begin

lemma no_unit_cancel_rightD[dest]:
  \<open>a ## b \<Longrightarrow> a + b = b \<Longrightarrow> False\<close>
  using cancel_right_to_unit no_units by blast

lemma no_unit_cancel_leftD[dest]:
  \<open>a ## b \<Longrightarrow> a + b = a \<Longrightarrow> False\<close>
  using cancel_left_to_unit no_units by blast

end

subsection \<open> Halving separation algebra \<close>

class halving_perm_alg = perm_alg +
  fixes half :: \<open>'a \<Rightarrow> 'a\<close>
  assumes half_additive_split: \<open>\<And>a. half a + half a = a\<close>
  assumes half_self_disjoint: \<open>\<And>a. half a ## half a\<close>
  assumes half_sepadd_distrib: \<open>\<And>a b. a ## b \<Longrightarrow> half (a + b) = half a + half b\<close>
begin

lemma half_disjoint_preservation_left: \<open>a ## b \<Longrightarrow> half a ## b\<close>
  by (metis disjoint_add_leftR half_additive_split half_self_disjoint)

lemma half_disjoint_preservation_right: \<open>a ## b \<Longrightarrow> a ## half b\<close>
  using half_disjoint_preservation_left disjoint_sym by blast

lemma half_disjoint_preservation: \<open>a ## b \<Longrightarrow> half a ## half b\<close>
  by (simp add: half_disjoint_preservation_left half_disjoint_preservation_right)


lemma half_disjoint_distribL:
  \<open>a ## c \<Longrightarrow> a + c ## b \<Longrightarrow> a + half c ## b + half c\<close>
  by (metis disjoint_add_leftL disjoint_add_right_commute disjoint_sym half_additive_split
      half_self_disjoint partial_add_assoc)

lemma half_disjoint_distribR:
  \<open>b ## c \<Longrightarrow> a ## b + c \<Longrightarrow> a + half c ## b + half c\<close>
  using half_disjoint_distribL disjoint_sym by blast

lemma half_eq_full_imp_self_additive:
  \<open>half a = a \<Longrightarrow> a + a = a\<close>
  by (metis half_additive_split)

end

class halving_multiunit_sep_alg = multiunit_sep_alg + halving_perm_alg

class halving_sep_alg = sep_alg + halving_multiunit_sep_alg


section \<open> Trivial self-disjoint + halving (very boring) \<close>

class trivial_halving_perm_alg = trivial_selfdisjoint_perm_alg + halving_perm_alg
begin

lemma trivial_half[simp]: \<open>half a = a\<close>
  by (simp add: disjointness half_additive_split half_self_disjoint)

end



section \<open> Instances \<close>

instantiation prod :: (multiunit_sep_alg,multiunit_sep_alg) perm_alg
begin

definition plus_prod  :: \<open>'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b\<close> where
  \<open>plus_prod a b \<equiv> (fst a + fst b, snd a + snd b)\<close>
declare plus_prod_def[simp]

definition disjoint_prod  :: \<open>'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool\<close> where
  \<open>disjoint_prod a b \<equiv> (fst a ## fst b \<and> snd a ## snd b)\<close>
declare disjoint_prod_def[simp]

definition less_eq_prod  :: \<open>'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool\<close> where
  \<open>less_eq_prod a b \<equiv> fst a \<le> fst b \<and> snd a \<le> snd b\<close>
declare less_eq_prod_def[simp]

definition less_prod  :: \<open>'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool\<close> where
  \<open>less_prod a b \<equiv> fst a < fst b \<and> snd a \<le> snd b \<or> fst a \<le> fst b \<and> snd a < snd b\<close>
declare less_prod_def[simp]

instance
  apply standard
            apply force
           apply force
          apply (force simp add: partial_add_assoc)
         apply (force dest: partial_add_commute)
        apply (force simp add: partial_add_assoc)
       apply (force simp add: disjoint_sym_iff partial_add_commute)
      apply (force simp add: disjoint_sym)
     apply (force dest: disjoint_add_rightL)
    apply (force dest: disjoint_add_right_commute)
   apply (force dest: positivity)
  apply (clarsimp simp add: less_iff_sepadd)
  apply (simp add: le_iff_sepadd_weak, metis disjoint_sym_iff unitof_disjoint unitof_is_unitR2)
  done

end

instantiation prod :: (multiunit_sep_alg,multiunit_sep_alg) multiunit_sep_alg
begin

definition unitof_prod  :: \<open>'a \<times> 'b \<Rightarrow> 'a \<times> 'b\<close> where
  \<open>unitof a \<equiv> (unitof (fst a), unitof (snd a))\<close>
declare unitof_prod_def[simp]

instance
  by standard force+

end

instantiation prod  :: (sep_alg,sep_alg) sep_alg
begin

definition zero_prod  :: \<open>'a \<times> 'b\<close> where
  \<open>zero_prod \<equiv> (0, 0)\<close>
declare zero_prod_def[simp]

definition bot_prod  :: \<open>'a \<times> 'b\<close> where
  \<open>bot_prod \<equiv> (\<bottom>, \<bottom>)\<close>
declare bot_prod_def[simp]

instance
  by standard force+

end


instantiation unit :: perm_alg
begin

definition plus_unit :: \<open>unit \<Rightarrow> unit \<Rightarrow> unit\<close> where
  \<open>plus_unit a b \<equiv> ()\<close>
declare plus_unit_def[simp]

definition disjoint_unit :: \<open>unit \<Rightarrow> unit \<Rightarrow> bool\<close> where
  \<open>disjoint_unit a b \<equiv> True\<close>
declare disjoint_unit_def[simp]

instance
  by standard simp+

end

instantiation unit :: multiunit_sep_alg
begin

definition unitof_unit :: \<open>unit \<Rightarrow> unit\<close> where
  \<open>unitof_unit \<equiv> \<lambda>_. ()\<close>
declare unitof_unit_def[simp]

instance
  by standard simp+

end

instantiation unit :: sep_alg
begin

definition zero_unit :: \<open>unit\<close> where
  \<open>zero_unit \<equiv> ()\<close>
declare zero_unit_def[simp]

definition bot_unit :: \<open>unit\<close> where
  \<open>bot_unit \<equiv> ()\<close>
declare bot_unit_def[simp]

instance
  by standard simp+

end

end