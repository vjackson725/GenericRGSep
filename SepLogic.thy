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
  assumes disjoint_add_right_commute: \<open>b ## c \<Longrightarrow> a ## b + c \<Longrightarrow> b ## a + c\<close>
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

lemma partial_le_part_left: \<open>a ## b \<Longrightarrow> a + b \<le> c \<Longrightarrow> a \<le> c\<close>
  using order.trans partial_le_plus by blast

lemma partial_le_part_right: \<open>a ## b \<Longrightarrow> a + b \<le> c \<Longrightarrow> b \<le> c\<close>
  using order.trans partial_le_plus2 by blast

(* TODO: think about decreasing and increasing elements from
    'Bringing order to the separation logic Jungle'.
  All our elements are increasing, I think, because of the above two rules.
*)

lemma common_subresource_selfsep:
  \<open>a ## b \<Longrightarrow> ab \<le> a \<Longrightarrow> ab \<le> b \<Longrightarrow> ab ## ab\<close>
  by (metis disjoint_add_rightL disjoint_sym order.order_iff_strict less_iff_sepadd)

lemma selfdisjoint_over_selfdisjoint:
  \<open>a ## a \<Longrightarrow> \<forall>x\<le>a. x ## x\<close>
  using common_subresource_selfsep by blast

lemma disjoint_add_rightR: \<open>b ## c \<Longrightarrow> a ## b + c \<Longrightarrow> a ## c\<close>
  by (metis disjoint_add_rightL disjoint_sym partial_add_commute)

lemma disjoint_add_leftL: \<open>a ## b \<Longrightarrow> a + b ## c \<Longrightarrow> a ## c\<close>
  using disjoint_add_rightL disjoint_sym by blast

lemma disjoint_add_leftR: \<open>a ## b \<Longrightarrow> a + b ## c \<Longrightarrow> b ## c\<close>
  by (metis disjoint_add_leftL disjoint_sym partial_add_commute)

lemma disjoint_add_right_commute2:
  \<open>b ## c \<Longrightarrow> a ## b + c \<Longrightarrow> c ## b + a\<close>
  by (metis disjoint_add_rightR disjoint_add_right_commute disjoint_sym partial_add_commute)

lemma disjoint_add_left_commute:
  \<open>a ## b \<Longrightarrow> a + b ## c \<Longrightarrow> c + b ## a\<close>
  by (simp add: disjoint_sym_iff disjoint_add_right_commute)

lemma disjoint_add_left_commute2:
  \<open>a ## b \<Longrightarrow> a + b ## c \<Longrightarrow> a + c ## b\<close>
  by (metis disjoint_add_leftR disjoint_add_left_commute partial_add_commute)

lemma disjoint_add_swap:
  \<open>b ## c \<Longrightarrow> a ## b + c \<Longrightarrow> a + b ## c\<close>
  by (simp add: disjoint_sym_iff disjoint_add_right_commute partial_add_commute)

lemma disjoint_add_swap2:
  \<open>a ## b \<Longrightarrow> a + b ## c \<Longrightarrow> a ## b + c\<close>
  by (simp add: disjoint_add_right_commute2 disjoint_sym_iff partial_add_commute)

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

subsection \<open> sepadd_unit \<close>

definition \<open>sepadd_unit a \<equiv> a ## a \<and> (\<forall>b. a ## b \<longrightarrow> a + b = b)\<close>

abbreviation \<open>sepadd_units \<equiv> Collect sepadd_unit\<close>

text \<open> sepadd_unit antimono \<close>
lemma below_unit_impl_unit:
  \<open>a \<le> b \<Longrightarrow> sepadd_unit b \<Longrightarrow> sepadd_unit a\<close>
  unfolding sepadd_unit_def
  by (metis disjoint_add_rightL order.antisym le_iff_sepadd_weak)

lemma le_unit_iff_eq:
  \<open>sepadd_unit b \<Longrightarrow> a \<le> b \<longleftrightarrow> b = a\<close>
  unfolding sepadd_unit_def
  by (metis disjoint_add_rightL order.antisym le_iff_sepadd_weak)

lemma units_least: \<open>sepadd_unit x \<Longrightarrow> x ## y \<Longrightarrow> x \<le> y\<close>
  using le_iff_sepadd_weak sepadd_unit_def by auto

lemma almost_units_are_nondisjoint_to_everything:
  \<open>(\<forall>b. a ## b \<longrightarrow> a + b = b) \<Longrightarrow> \<not> a ## a \<Longrightarrow> \<not> a ## b\<close>
  by (metis disjoint_add_leftL disjoint_sym)

lemma units_separate_to_units: \<open>x ## y \<Longrightarrow> sepadd_unit (x + y) \<Longrightarrow> sepadd_unit x\<close>
  using below_unit_impl_unit partial_le_plus by blast

lemma sepadd_unit_idem_add[simp]: \<open>sepadd_unit u \<Longrightarrow> u + u = u\<close>
  using sepadd_unit_def by auto

lemma sepadd_unit_left: \<open>sepadd_unit u \<Longrightarrow> u ## a \<Longrightarrow> u + a = a\<close>
  using sepadd_unit_def by auto

lemma sepadd_unit_right: \<open>sepadd_unit u \<Longrightarrow> a ## u \<Longrightarrow> a + u = a\<close>
  by (metis disjoint_sym partial_add_commute sepadd_unit_left)

lemma sepadd_unit_selfsep[dest, simp]: \<open>sepadd_unit u \<Longrightarrow> u ## u\<close>
  by (simp add: sepadd_unit_def)

lemma add_sepadd_unit_add_iff_parts_sepadd_unit[simp]:
  \<open>x ## y \<Longrightarrow> sepadd_unit (x + y) \<longleftrightarrow> sepadd_unit x \<and> sepadd_unit y\<close>
  by (metis sepadd_unit_def units_separate_to_units)

lemma disjoint_units_identical:
  \<open>a ## b \<Longrightarrow> sepadd_unit a \<Longrightarrow> sepadd_unit b \<Longrightarrow> a = b\<close>
  by (metis disjoint_sym partial_add_commute sepadd_unit_def)

lemma trans_disjoint_units_identical:
  \<open>a ## b \<Longrightarrow> b ## c \<Longrightarrow> sepadd_unit a \<Longrightarrow> sepadd_unit c \<Longrightarrow> a = c\<close>
  by (metis disjoint_units_identical disjoint_add_leftL sepadd_unit_def)

lemma sepadd_unit_disjoint_trans[dest]:
  \<open>sepadd_unit a \<Longrightarrow> a ## b \<Longrightarrow> b ## c \<Longrightarrow> a ## c\<close>
  by (metis disjoint_add_leftL sepadd_unit_def)


subsection \<open> zero_sepadd \<close>

definition \<open>sepadd_zero a \<equiv> a ## a \<and> (\<forall>b. a ## b \<longrightarrow> a + b = a)\<close>

text \<open> sepadd_zero antimono \<close>
lemma above_zero_impl_zero:
  \<open>a \<le> b \<Longrightarrow> sepadd_zero a \<Longrightarrow> sepadd_zero b\<close>
  unfolding sepadd_zero_def
  using le_iff_sepadd_weak by force

(* obvious, but a nice dual to the unit case *)
lemma zeros_add_to_zero: \<open>x ## y \<Longrightarrow> sepadd_zero x \<Longrightarrow> sepadd_zero (x + y)\<close>
  by (simp add: sepadd_zero_def)


subsection \<open> duplicable \<close>

text \<open>
  Duplicable elements. These are related to the logical content of a separation algebra (as
  contrasted with the resource content.)
\<close>

definition \<open>sepadd_dup a \<equiv> a ## a \<and> a + a = a\<close>

lemma units_are_dup: \<open>sepadd_unit a \<Longrightarrow> sepadd_dup a\<close>
  by (simp add: sepadd_dup_def)

lemma zeros_are_dup: \<open>sepadd_zero a \<Longrightarrow> sepadd_dup a\<close>
  by (simp add: sepadd_dup_def sepadd_zero_def)

lemma sepadd_dup_antimono:
  \<open>a \<le> b \<Longrightarrow> sepadd_dup b \<Longrightarrow> sepadd_dup a\<close>
  apply (clarsimp simp add: sepadd_dup_def)
  apply (rule conjI)
   apply (force dest: common_subresource_selfsep)
  apply (metis le_iff_sepadd_weak positivity)
  done


subsection \<open> core \<close>

text \<open>
  Here we introduce the notion of a core, the greatest duplicable element below an element.

  Iris uses this notion to algebraise shared invariant predicates. Note that our version is weaker
  than Iris'; we do not have that \<open>has_core\<close> is monotone (or even antimonotone). This is because
  there can be several non-comparible duplicable elements sitting below a or b.
  When all non-empty subsets of duplicable elements have a lub which is itself duplicable,
  \<open>has_core\<close> is monotone. (See glb/lub section.)
\<close>

definition \<open>core_rel a ca \<equiv> ca \<le> a \<and> sepadd_dup ca \<and> (\<forall>y\<le>a. sepadd_dup y \<longrightarrow> y \<le> ca)\<close>

abbreviation \<open>has_core a \<equiv> Ex (core_rel a)\<close>
abbreviation \<open>the_core a \<equiv> The (core_rel a)\<close>

(* simp doesn't like rewriting core_rel under an Ex in goal position. *)
lemma has_core_def:
  \<open>has_core a \<longleftrightarrow> (\<exists>ca. ca \<le> a \<and> sepadd_dup ca \<and> (\<forall>y\<le>a. sepadd_dup y \<longrightarrow> y \<le> ca))\<close>
  using core_rel_def by presburger

lemma the_core_core_rel_eq[simp]:
  \<open>core_rel a ca \<Longrightarrow> the_core a = ca\<close>
  using core_rel_def order.antisym
  using leD by auto

lemma has_core_the_core_eq:
  \<open>has_core a \<Longrightarrow> P (the_core a) \<longleftrightarrow> (\<forall>ca. core_rel a ca \<longrightarrow> P ca)\<close>
  using the_core_core_rel_eq by blast

lemma core_dup_self[simp]:
  \<open>sepadd_dup a \<Longrightarrow> the_core a = a\<close>
  by (simp add: core_rel_def)

lemma core_idem:
  \<open>has_core a \<Longrightarrow> the_core (the_core a) = the_core a\<close>
  by (clarsimp simp add: core_rel_def)

lemma core_disjoint:
  \<open>has_core a \<Longrightarrow> the_core a ## a\<close>
  apply (clarsimp simp add: core_rel_def)
  apply (metis disjoint_add_swap2 le_iff_sepadd_weak sepadd_dup_def)
  done

lemma core_plus_same[simp]:
  \<open>has_core a \<Longrightarrow> the_core a + a = a\<close>
  apply (clarsimp simp add: core_rel_def)
  apply (metis le_iff_sepadd_weak partial_add_assoc2 sepadd_dup_def)
  done

lemma core_plus_sameR[simp]:
  \<open>has_core a \<Longrightarrow> a + the_core a = a\<close>
  using core_disjoint core_plus_same partial_add_commute
  by auto

lemma the_core_le_impl:
  \<open>has_core a \<Longrightarrow> has_core b \<Longrightarrow> a \<le> b \<Longrightarrow> the_core a \<le> the_core b\<close>
  by (clarsimp simp add: core_rel_def)

text \<open>
  As every duplicable element is its own core, the monotonicity criterion is equivalent to
  the property that every element above a duplicable element (e.g. 0) has a unique greatest
  duplicable element below it.
\<close>
lemma has_core_mono_iff:
  \<open>(\<forall>a b. a \<le> b \<longrightarrow> has_core a \<longrightarrow> has_core b) \<longleftrightarrow>
    (\<forall>x. sepadd_dup x \<longrightarrow> (\<forall>a\<ge>x. has_core a))\<close>
  by (metis core_rel_def order.trans eq_refl)


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

lemma sepcoimp_sepimp_dual: \<open>P \<^emph> Q = -(P \<sim>\<^emph> -Q)\<close>
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
  \<open>precise P \<equiv> \<forall>h. \<forall>h1\<le>h. \<forall>h2\<le>h. P h1 \<longrightarrow> P h2 \<longrightarrow> h1 = h2\<close>

text \<open>
  The following predicates are equivalent to precision in a cancellative algebra,
  but incomparable in a more generic setting.
\<close>

definition precise2 :: \<open>('a \<Rightarrow> bool) \<Rightarrow> bool\<close> where
  \<open>precise2 P \<equiv> (\<forall>Q. P \<^emph> Q \<le> P \<sim>\<^emph> Q)\<close>

lemma sepconj_imp_sepcoimp_then_sepconj_conj_distrib:
  \<open>(\<forall>Q. P \<^emph> Q \<le> P \<sim>\<^emph> Q) \<Longrightarrow> (\<forall>Q Q'. P \<^emph> (Q \<sqinter> Q') = (P \<^emph> Q) \<sqinter> (P \<^emph> Q'))\<close>
  by (simp add: precise_def sepconj_def sepcoimp_def fun_eq_iff le_fun_def, blast)

lemma sepconj_conj_distrib_then_sepconj_imp_sepcoimp:
  \<open>(\<forall>Q Q'. P \<^emph> (Q \<sqinter> Q') = (P \<^emph> Q) \<sqinter> (P \<^emph> Q')) \<Longrightarrow> (\<forall>Q. P \<^emph> Q \<le> P \<sim>\<^emph> Q)\<close>
  apply (clarsimp simp add: precise_def sepconj_def sepcoimp_def fun_eq_iff le_fun_def)
  apply (rename_tac h1 h1' h2 h2')
  apply (drule_tac x=\<open>(=) h1'\<close> in spec, drule_tac x=\<open>(=) h2'\<close> in spec)
  apply blast
  done

lemma sepconj_conj_distrib_iff_sepconj_imp_sepcoimp:
  \<open>(\<forall>Q Q'. P \<^emph> (Q \<sqinter> Q') = (P \<^emph> Q) \<sqinter> (P \<^emph> Q')) \<longleftrightarrow> (\<forall>Q. P \<^emph> Q \<le> P \<sim>\<^emph> Q)\<close>
  using sepconj_conj_distrib_then_sepconj_imp_sepcoimp
    sepconj_imp_sepcoimp_then_sepconj_conj_distrib
  by blast

lemma sepconj_imp_sepcoimp_iff_sepconj_eq_strong_sepcoimp:
  \<open>(\<forall>Q. P \<^emph> Q \<le> P \<sim>\<^emph> Q) \<longleftrightarrow> (\<forall>Q. P \<^emph> Q = (P \<^emph> \<top>) \<sqinter> (P \<sim>\<^emph> Q))\<close>
  apply (clarsimp simp add: sepconj_def sepcoimp_def precise_def le_fun_def fun_eq_iff)
  apply (intro iffI allI conjI impI; (elim exE conjE)?)
     apply blast
    apply blast
   apply blast
  apply clarsimp
  apply (rename_tac h2 h2' h1 h1')
  apply (drule_tac x=\<open>(=) h2'\<close> in spec)
  apply blast
  done

lemma sepconj_conj_distrib_iff_sepconj_eq_strong_sepcoimp:
  \<open>(\<forall>Q Q'. P \<^emph> (Q \<sqinter> Q') = (P \<^emph> Q) \<sqinter> (P \<^emph> Q')) \<longleftrightarrow> (\<forall>Q. P \<^emph> Q = (P \<^emph> \<top>) \<sqinter> (P \<sim>\<^emph> Q))\<close>
  by (meson sepconj_conj_distrib_iff_sepconj_imp_sepcoimp
      sepconj_imp_sepcoimp_iff_sepconj_eq_strong_sepcoimp)

lemmas sepconj_conj_distrib_then_sepconj_eq_strong_sepcoimp =
  iffD1[OF sepconj_conj_distrib_iff_sepconj_eq_strong_sepcoimp]

lemmas sepconj_eq_strong_sepcoimp_then_sepconj_conj_distrib =
  iffD2[OF sepconj_conj_distrib_iff_sepconj_eq_strong_sepcoimp]

section \<open> Intuitionistic \<close>

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

section \<open> Supported \<close>

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

lemma unitof_is_sepadd_unit: \<open>sepadd_unit (unitof a)\<close>
  by (simp add: sepadd_unit_def unitof_inherits_disjointness)

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

lemma unitof_sepadd_unit:
  \<open>sepadd_unit x \<Longrightarrow> unitof x = x\<close>
  by (metis sepadd_unit_def unitof_disjoint2 unitof_is_unitR2)

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
  \<open>emp \<equiv> sepadd_unit\<close>

definition emp_mfault :: \<open>('a \<Rightarrow> bool) mfault\<close> ("emp\<^sub>f") where
  \<open>emp\<^sub>f \<equiv> Success emp\<close>

fun iterated_sepconj :: \<open>('a \<Rightarrow> bool) list \<Rightarrow> ('a \<Rightarrow> bool)\<close> where
  \<open>iterated_sepconj (P # Ps) = P \<^emph> iterated_sepconj Ps\<close>
| \<open>iterated_sepconj [] = emp\<close>

lemma emp_sepconj_unit[simp]: \<open>emp \<^emph> P = P\<close>
  apply (simp add: emp_def sepconj_def sepadd_unit_def fun_eq_iff)
  apply (metis disjoint_sym partial_add_commute unitof_disjoint unitof_is_unitR2)
  done

lemma emp_sepconj_unit_right[simp]: \<open>P \<^emph> emp = P\<close>
  using emp_sepconj_unit sepconj_comm by force

lemma secoimp_imp_sepconj:
  \<open>P \<sqinter> (P \<sim>\<^emph> Q) \<le> P \<^emph> (Q \<sqinter> emp)\<close>
  apply (simp add: sepcoimp_def sepconj_def le_fun_def emp_def sepadd_unit_def)
  apply (metis sepadd_unit_def unitof_disjoint2 unitof_is_unitR2 unitof_is_sepadd_unit)
  done

lemma not_coimp_emp:
  \<open>\<not> sepadd_unit h \<Longrightarrow> (- (\<top> \<sim>\<^emph> emp)) h\<close>
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
  \<open>sepadd_unit x \<longleftrightarrow> x = 0\<close>
  by (metis unitof_is_sepadd_unit unitof_sepadd_unit unitof_zero)

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

section \<open> Compatibility \<close>

context perm_alg
begin

definition compatible :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> where
  \<open>compatible \<equiv> ((\<le>) \<squnion> (\<ge>))\<^sup>*\<^sup>*\<close>

lemmas compatible_induct[consumes 1] =
  rtranclp_induct[of \<open>(\<le>) \<squnion> (\<ge>)\<close>, simplified compatible_def[symmetric], simplified]

lemmas converse_compatible_induct[consumes 1] =
  converse_rtranclp_induct[of \<open>(\<le>) \<squnion> (\<ge>)\<close>, simplified compatible_def[symmetric], simplified]

lemmas compatibleE =
  rtranclE[of \<open>(\<le>) \<squnion> (\<ge>)\<close>, simplified compatible_def[symmetric], simplified]

lemmas converse_compatibleE =
  converse_rtranclpE[of \<open>(\<le>) \<squnion> (\<ge>)\<close>, simplified compatible_def[symmetric], simplified]

lemmas compatible_trans =
  rtranclp_trans[of \<open>(\<le>) \<squnion> (\<ge>)\<close>, simplified compatible_def[symmetric], simplified]

lemma compatible_refl[intro!, simp]:
  \<open>compatible a a\<close>
  by (simp add: compatible_def)

lemma compatible_sym:
  assumes \<open>compatible a b\<close>
  shows \<open>compatible b a\<close>
proof -
  have \<open>((\<le>) \<squnion> (\<ge>))\<^sup>*\<^sup>* = (((\<le>) \<squnion> (\<ge>))\<inverse>\<inverse>)\<^sup>*\<^sup>*\<close>
    by (force intro!: arg_cong[of _ _ rtranclp])
  also have \<open>... = ((\<le>) \<squnion> (\<ge>))\<^sup>*\<^sup>*\<inverse>\<inverse>\<close>
    by (simp add: rtranclp_conversep)
  finally show ?thesis
    by (metis assms compatible_def conversep_iff)
qed

lemma le_is_compatible[intro]:
  \<open>a \<le> b \<Longrightarrow> compatible a b\<close>
  by (simp add: compatible_def r_into_rtranclp)

lemma ge_is_compatible[intro]:
  \<open>a \<ge> b \<Longrightarrow> compatible a b\<close>
  by (simp add: compatible_def r_into_rtranclp)

lemma trans_le_le_is_compatible[intro]:
  \<open>a \<le> b \<Longrightarrow> b \<le> c \<Longrightarrow> compatible a c\<close>
  using le_is_compatible by force

lemma trans_ge_ge_is_compatible[intro]:
  \<open>b \<le> a \<Longrightarrow> c \<le> b \<Longrightarrow> compatible a c\<close>
  using ge_is_compatible by force

lemma trans_ge_le_is_compatible[intro]:
  \<open>b \<le> a \<Longrightarrow> b \<le> c \<Longrightarrow> compatible a c\<close>
  using compatible_trans by blast

lemma trans_le_ge_is_compatible[intro]:
  \<open>a \<le> b \<Longrightarrow> c \<le> b \<Longrightarrow> compatible a c\<close>
  using compatible_trans by blast

subsection \<open> Relation to other relations \<close>

lemma disjoint_rtrancl_implies_compatible:
  \<open>(##)\<^sup>*\<^sup>* x y \<Longrightarrow> compatible x y\<close>
  apply (induct rule: rtranclp_induct)
   apply force
  apply (metis compatible_trans partial_le_plus partial_le_plus2 trans_le_ge_is_compatible)
  done

lemma compatible_eq_strict_compatible:
  \<open>compatible = ((<) \<squnion> (>))\<^sup>*\<^sup>*\<close>
proof -
  have \<open>compatible = ((=) \<squnion> (<) \<squnion> (>))\<^sup>*\<^sup>*\<close>
    by (force simp add: compatible_def intro: arg_cong[of _ _ rtranclp])
  also have \<open>... = ((<) \<squnion> (>))\<^sup>*\<^sup>*\<close>
    by (metis rtranclp_reflclp sup_assoc sup_commute)
  finally show ?thesis .
qed

lemma implies_compatible_then_rtranscl_implies_compatible:
  \<open>\<forall>x y. r x y \<longrightarrow> compatible x y \<Longrightarrow> r\<^sup>*\<^sup>* x y \<Longrightarrow> compatible x y\<close>
  using implies_rel_then_rtranscl_implies_rel[of r _ _ compatible]
    compatible_trans
  by blast

lemma implies_compatible_then_rtranscl_implies_compatible2:
  \<open>r \<le> compatible \<Longrightarrow> r\<^sup>*\<^sup>* \<le> compatible\<close>
  using implies_compatible_then_rtranscl_implies_compatible
  by (simp add: le_fun_def)

subsection \<open> Relation to units \<close>

lemma step_compatible_units_identical:
  \<open>compatible b z \<Longrightarrow> a \<le> b \<or> b \<le> a \<Longrightarrow> sepadd_unit a \<Longrightarrow> sepadd_unit z \<Longrightarrow> a = z\<close>
  apply (induct rule: converse_compatible_induct)
   apply (force simp add: le_unit_iff_eq)
  apply (simp add: le_unit_iff_eq)
  apply (metis disjoint_preservation2 order.trans le_iff_sepadd_weak le_unit_iff_eq
      sepadd_unit_left)
  done

lemma compatible_units_identical:
  \<open>compatible a z \<Longrightarrow> sepadd_unit a \<Longrightarrow> sepadd_unit z \<Longrightarrow> a = z\<close>
  by (metis converse_compatibleE step_compatible_units_identical)

lemma compatible_unit_disjoint[dest, simp]:
  \<open>compatible u a \<Longrightarrow> sepadd_unit u \<Longrightarrow> a ## u\<close>
  apply (induct rule: compatible_induct)
   apply force
  apply (metis disjoint_add_swap2 disjoint_preservation2 disjoint_sym le_iff_sepadd_weak
      partial_add_commute sepadd_unit_right)
  done

lemma compatible_unit_disjoint2[dest, simp]:
  \<open>compatible a u \<Longrightarrow> sepadd_unit u \<Longrightarrow> a ## u\<close>
  apply (induct rule: converse_compatible_induct)
   apply force
  apply (metis disjoint_add_swap2 disjoint_preservation2 disjoint_sym le_iff_sepadd_weak
      partial_add_commute sepadd_unit_right)
  done

lemma compatible_to_unit_is_unit_left[simp]:
  \<open>compatible u a \<Longrightarrow> sepadd_unit u \<Longrightarrow> u + a = a\<close>
  apply (induct rule: compatible_induct)
   apply force
   apply (simp add: le_iff_sepadd_weak)
  apply (elim disjE; clarsimp) (* 1 \<rightarrow> 2 *)
   apply (metis compatible_unit_disjoint disjoint_sym partial_add_assoc2)
  apply (metis compatible_unit_disjoint disjoint_add_leftL partial_add_commute sepadd_unit_right)
  done

lemma compatible_to_unit_is_unit_right[simp]:
  \<open>compatible u a \<Longrightarrow> sepadd_unit u \<Longrightarrow> a + u = a\<close>
  by (simp add: sepadd_unit_right)

end


section \<open> Permission/Separation Algebra Subclasses \<close>

(* almost a sep_alg, in that if there was a unit, it would be a sep-algebra *)
class allcompatible_perm_alg = perm_alg +
  assumes all_compatible: \<open>compatible a b\<close>
begin

lemma all_units_eq:
  \<open>sepadd_unit a \<Longrightarrow> sepadd_unit b \<Longrightarrow> a = b\<close>
  by (simp add: all_compatible compatible_units_identical)

end

context multiunit_sep_alg
begin

lemma same_unit_compatible:
  \<open>unitof a = unitof b \<Longrightarrow> compatible a b\<close>
  by (metis trans_ge_le_is_compatible unitof_le)

lemma compatible_then_same_unit:
  \<open>compatible a b \<Longrightarrow> unitof a = unitof b\<close>
  by (meson compatible_trans ge_is_compatible step_compatible_units_identical
      unitof_is_sepadd_unit unitof_le)

end

(* compatible multiunit sep algebras collapse *)
class allcompatible_multiunit_sep_alg = allcompatible_perm_alg + multiunit_sep_alg
begin

lemma exactly_one_unit: \<open>\<exists>!u. sepadd_unit u\<close>
  using all_compatible compatible_units_identical unitof_is_sepadd_unit by blast

definition \<open>the_unit \<equiv> The sepadd_unit\<close>

lemma the_unit_is_a_unit:
  \<open>sepadd_unit the_unit\<close>
  unfolding the_unit_def
  by (rule theI', simp add: exactly_one_unit)

lemma is_sep_alg:
  \<open>class.sep_alg the_unit (\<le>) (<) the_unit (##) (+) (\<lambda>_. the_unit)\<close>
  apply standard
      apply (metis exactly_one_unit unitof_is_sepadd_unit unitof_le the_unit_is_a_unit)
     apply (metis exactly_one_unit unitof_disjoint unitof_is_sepadd_unit the_unit_is_a_unit)
    apply (metis exactly_one_unit unitof_disjoint2 unitof_is_sepadd_unit the_unit_is_a_unit)
   apply (metis exactly_one_unit unitof_disjoint2 unitof_is_unit2 unitof_is_sepadd_unit
      the_unit_is_a_unit)
  apply (metis exactly_one_unit unitof_disjoint2 unitof_is_unit2 unitof_is_sepadd_unit
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
  assumes selfsep_implies_unit: \<open>a ## a \<Longrightarrow> sepadd_unit a\<close>
begin

lemma selfsep_iff:
  \<open>a ## a \<longleftrightarrow> sepadd_unit a\<close>
  using selfsep_implies_unit sepadd_unit_def by blast

end

class strong_sep_multiunit_sep_alg = multiunit_sep_alg + strong_sep_perm_alg
begin

lemma mu_selfsep_iff: \<open>a ## a \<longleftrightarrow> unitof a = a\<close>
  by (metis selfsep_iff unitof_disjoint unitof_sepadd_unit)

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

definition \<open>glb_rel a b ab \<equiv> ab \<le> a \<and> ab \<le> b \<and> (\<forall>ab'. ab' \<le> a \<longrightarrow> ab' \<le> b \<longrightarrow> ab' \<le> ab)\<close>

abbreviation \<open>glb_exists a b \<equiv> Ex (glb_rel a b)\<close>
abbreviation \<open>glb a b \<equiv> The (glb_rel a b)\<close>

definition \<open>lub_rel a b ab \<equiv> a \<le> ab \<and> b \<le> ab \<and> (\<forall>ab'. a \<le> ab' \<longrightarrow> b \<le> ab' \<longrightarrow> ab \<le> ab')\<close>

abbreviation \<open>lub_exists a b \<equiv> Ex (lub_rel a b)\<close>
abbreviation \<open>lub a b \<equiv> The (lub_rel a b)\<close>

lemma glb_glb_rel_eq[simp]:
  \<open>glb_rel a b ab \<Longrightarrow> glb a b = ab\<close>
  using glb_rel_def order.antisym by auto

lemma lub_lub_rel_eq[simp]:
  \<open>lub_rel a b ab \<Longrightarrow> lub a b = ab\<close>
  using lub_rel_def order.antisym by auto

lemma glb_exists_glb_eq:
  \<open>glb_exists a b \<Longrightarrow> P (glb a b) \<longleftrightarrow> (\<forall>ab. glb_rel a b ab \<longrightarrow> P ab)\<close>
  using glb_glb_rel_eq by blast

lemma lub_exists_lub_eq:
  \<open>lub_exists a b \<Longrightarrow> P (lub a b) \<longleftrightarrow> (\<forall>ab. lub_rel a b ab \<longrightarrow> P ab)\<close>
  using lub_lub_rel_eq by blast

subsection \<open> Complete Glb \<close>

definition \<open>Glb_rel A x \<equiv> (\<forall>a\<in>A. x \<le> a) \<and> (\<forall>x'. (\<forall>a\<in>A. x' \<le> a) \<longrightarrow> x' \<le> x)\<close>

abbreviation \<open>Glb_exists A \<equiv> Ex (Glb_rel A)\<close>
abbreviation \<open>Glb A \<equiv> The (Glb_rel A)\<close>

definition \<open>Lub_rel A x \<equiv> (\<forall>a\<in>A. a \<le> x) \<and> (\<forall>x'. (\<forall>a\<in>A. a \<le> x') \<longrightarrow> x \<le> x')\<close>

abbreviation \<open>Lub_exists A \<equiv> Ex (Lub_rel A)\<close>
abbreviation \<open>Lub A \<equiv> The (Lub_rel A)\<close>

lemma Glb_Glb_rel_eq[simp]:
  \<open>Glb_rel A x \<Longrightarrow> Glb A = x\<close>
  using Glb_rel_def order.antisym by auto

lemma Lub_Lub_rel_eq[simp]:
  \<open>Lub_rel A x \<Longrightarrow> Lub A = x\<close>
  using Lub_rel_def order.antisym by auto

lemma Glb_exists_Glb_eq:
  \<open>Glb_exists A \<Longrightarrow> P (Glb A) \<longleftrightarrow> (\<forall>x. Glb_rel A x \<longrightarrow> P x)\<close>
  using Glb_Glb_rel_eq by blast

lemma Lub_exists_Lub_eq:
  \<open>Lub_exists A \<Longrightarrow> P (Lub A) \<longleftrightarrow> (\<forall>x. Lub_rel A x \<longrightarrow> P x)\<close>
  using Lub_Lub_rel_eq by blast


lemma Glb_rel_in_Least_equality:
  \<open>Glb_rel (Collect P) x \<Longrightarrow> P x \<Longrightarrow> Least P = x\<close>
  apply (clarsimp simp add: Glb_rel_def)
  apply (subst Least_equality; force)
  done

lemma Lub_rel_in_Greatest_equality:
  \<open>Lub_rel (Collect P) x \<Longrightarrow> P x \<Longrightarrow> Greatest P = x\<close>
  apply (clarsimp simp add: Lub_rel_def)
  apply (subst Greatest_equality; force)
  done

subsection \<open> lub glb interchange properties \<close>

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
  by (clarsimp simp add: lub_rel_def glb_rel_def)

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
  by (clarsimp simp add: lub_rel_def glb_rel_def)

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
  by (clarsimp simp add: lub_rel_def)

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
  by (clarsimp simp add: glb_rel_def sepadd_left_mono)

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

subsection \<open> glb properties \<close>

lemma glb_leqL[intro]: \<open>glb_exists a b \<Longrightarrow> glb a b \<le> a\<close>
  by (clarsimp simp add: glb_rel_def)

lemma glb_leqR[intro]: \<open>glb_exists a b \<Longrightarrow> glb a b \<le> b\<close>
  by (clarsimp simp add: glb_rel_def)

lemma glb_least[intro]: \<open>glb_exists a b \<Longrightarrow> c \<le> a \<Longrightarrow> c \<le> b \<Longrightarrow> c \<le> glb a b\<close>
  by (clarsimp simp add: glb_rel_def)

lemma glb_disjointL: \<open>a ## b \<Longrightarrow> glb_exists a c \<Longrightarrow> glb a c ## b\<close>
  using disjoint_preservation by blast

lemma glb_disjointR: \<open>a ## b \<Longrightarrow> glb_exists b c \<Longrightarrow> a ## glb b c\<close>
  using disjoint_preservation2 by blast

lemma glb_idem[simp]: \<open>glb a a = a\<close>
  by (simp add: glb_rel_def)

lemma sepinf_assoc[simp]:
  \<open>glb_exists b c \<Longrightarrow>
    glb_exists a b \<Longrightarrow>
    glb_exists a (glb b c) \<Longrightarrow>
    glb_exists (glb a b) c \<Longrightarrow>
    glb a (glb b c) = glb (glb a b) c\<close>
  by (clarsimp, meson glb_rel_def order.antisym order.trans)


subsection \<open> weak glb + core \<close>

lemma glb_dup[dest]:
  \<open>glb_exists a b \<Longrightarrow> sepadd_dup a \<Longrightarrow> sepadd_dup (glb a b)\<close>
  using sepadd_dup_antimono
  by blast

lemma glb_dup2[dest]:
  \<open>glb_exists a b \<Longrightarrow> sepadd_dup b \<Longrightarrow> sepadd_dup (glb a b)\<close>
  using sepadd_dup_antimono
  by blast

lemma glb_has_core_antimono:
  \<open>\<forall>x. sepadd_dup x \<longrightarrow> glb_exists a x \<Longrightarrow>
    a \<le> b \<Longrightarrow>
    has_core b \<Longrightarrow>
    has_core a\<close>
  unfolding core_rel_def
  apply clarsimp
  apply (rename_tac cb)
  apply (rule_tac x=\<open>glb a cb\<close> in exI)
  apply (simp add: glb_exists_glb_eq glb_exists_glb_eq[of _ _ \<open>\<lambda>x. x \<le> _\<close>] glb_rel_def)
  apply (metis sepadd_dup_antimono)
  done

lemma has_core_iff_Lub:
  \<open>has_core a \<longleftrightarrow> (\<exists>x. Lub_rel {x. sepadd_dup x \<and> x \<le> a} x \<and> sepadd_dup x)\<close>
  apply (rule iffI)
   apply (clarsimp simp add: Lub_rel_def has_core_def, blast)
  apply (clarsimp simp add: Lub_rel_def has_core_def, blast)
  done

lemma Lub_has_core_mono:
  \<open>(\<And>A. A \<noteq> {} \<Longrightarrow> Ball A sepadd_dup \<Longrightarrow> (\<exists>x. Lub_rel A x \<and> sepadd_dup x)) \<Longrightarrow>
    a \<le> b \<Longrightarrow> has_core a \<Longrightarrow> has_core b\<close>
  apply (clarsimp simp add: has_core_iff_Lub)
  apply (drule meta_spec[of _ \<open>{x. sepadd_dup x \<and> x \<le> b}\<close>])
  apply (fastforce simp add: Lub_rel_def)
  done

lemma has_core_mono_iff_Lub:
  \<open>(\<forall>a b. a \<le> b \<longrightarrow> has_core a \<longrightarrow> has_core b) \<Longrightarrow>
    \<forall>A. A \<noteq> {} \<longrightarrow>
      Ball A sepadd_dup \<longrightarrow>
      (\<forall>x y. x \<le> y \<longrightarrow> y \<in> A \<longrightarrow> x \<in> A) \<longrightarrow>
      (\<exists>z. \<forall>x\<in>A. x \<le> z) \<longrightarrow>
      (\<exists>y. Lub_rel A y \<and> sepadd_dup y)\<close>
  apply -
  apply (subst (asm) has_core_mono_iff)
  apply (clarsimp simp add: Lub_rel_def)
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
  by (meson compatible_trans le_is_compatible sepinf_leqL)

lemma sepinf_preserves_compatibleL2:
  \<open>compatible a b \<Longrightarrow> compatible b c \<Longrightarrow> compatible (a \<sqinter> b) c\<close>
  by (meson compatible_trans sepinf_preserves_compatibleL)

lemma sepinf_preserves_compatibleL3:
  \<open>compatible a c \<Longrightarrow> compatible b c \<Longrightarrow> compatible (a \<sqinter> b) c\<close>
  by (meson compatible_sym compatible_trans sepinf_preserves_compatibleL)

lemma sepinf_preserves_compatibleR:
  \<open>compatible b c \<Longrightarrow> compatible a b \<Longrightarrow> compatible a (b \<sqinter> c)\<close>
  by (meson compatible_trans ge_is_compatible sepinf_leqL)

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
   apply (metis sepinf_preserves_compatibleL2)
  apply (subgoal_tac \<open>compatible a (b \<sqinter> c)\<close>)
   prefer 2
   apply (metis sepinf_preserves_compatibleR)
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
  \<open>compatible a b \<Longrightarrow> sepadd_unit a \<Longrightarrow> sepadd_unit (a \<sqinter> b)\<close>
  using below_unit_impl_unit by blast

lemma sepinf_of_unit_eq_that_unit[simp]:
  \<open>compatible a b \<Longrightarrow> sepadd_unit a \<Longrightarrow> a \<sqinter> b = a\<close>
  by (metis le_unit_iff_eq sepinf_leqL)

lemma sepinf_of_unit_eq_that_unit2[simp]:
  \<open>compatible a b \<Longrightarrow> sepadd_unit b \<Longrightarrow> a \<sqinter> b = b\<close>
  by (metis le_unit_iff_eq sepinf_leqR)

subsection \<open> inf + core \<close>

lemma sepinf_dup[dest]:
  \<open>compatible a b \<Longrightarrow> sepadd_dup a \<Longrightarrow> sepadd_dup (a \<sqinter> b)\<close>
  using sepadd_dup_antimono by blast

lemma sepinf_dup2[dest]:
  \<open>compatible a b \<Longrightarrow> sepadd_dup b \<Longrightarrow> sepadd_dup (a \<sqinter> b)\<close>
  using sepadd_dup_antimono by blast

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
  assumes selfdisjoint_same: \<open>a ## a \<Longrightarrow> a + a = b \<Longrightarrow> a = b\<close>
begin

text \<open> All selfdisjoint elements are duplicable \<close>

lemma all_selfdisjoint_dup:
  \<open>a ## a \<Longrightarrow> sepadd_dup a\<close>
  using selfdisjoint_same sepadd_dup_def by presburger

end

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
  shows \<open>sepadd_unit a\<close>
  unfolding sepadd_unit_def
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
    by (metis disjoint_add_left_commute)

  have \<open>a + c = a + (c + a)\<close>
    using assms D0 E1 Daa
    by (metis partial_add_assoc partial_add_commute)
  then show \<open>a + c = c\<close>
    using D0 D1
    by (metis partial_left_cancelD disjoint_sym partial_add_commute)
qed

lemma cancel_left_to_unit:
  \<open>a ## b \<Longrightarrow> a + b = a \<Longrightarrow> sepadd_unit b\<close>
  by (metis cancel_right_to_unit disjoint_sym partial_add_commute)

paragraph \<open> Seplogic \<close>

lemma precise_then_conj_distrib:
  fixes P :: \<open>'a \<Rightarrow> bool\<close>
  shows \<open>precise P \<Longrightarrow> (\<forall>Q Q'. P \<^emph> (Q \<sqinter> Q') = (P \<^emph> Q) \<sqinter> (P \<^emph> Q'))\<close>
  apply (clarsimp simp add: precise_def sepconj_def inf_fun_def)
  apply (intro ext iffI)
   apply blast
  apply (metis partial_le_plus partial_left_cancel2D)
  done

lemma precise_iff_conj_distrib:
  assumes \<open>\<forall>h u. P h \<longrightarrow> h ## u \<longrightarrow> P (h + u) \<longrightarrow> sepadd_unit u\<close>
  shows \<open>precise P \<longleftrightarrow> (\<forall>Q Q'. P \<^emph> (Q \<sqinter> Q') = (P \<^emph> Q) \<sqinter> (P \<^emph> Q'))\<close>
  using assms
  apply (intro allI iffI)
  apply (metis precise_then_conj_distrib)
  apply (clarsimp simp add: precise_def le_iff_sepadd_weak imp_ex imp_conjL
      simp del: all_simps(5))
  apply (intro conjI impI allI)
    apply (metis sepadd_unit_right)
   apply (metis sepadd_unit_right)
  apply clarsimp
  apply (rename_tac h1 h1' h2 h2')
  apply (drule_tac x=\<open>(=) h1'\<close> and y=\<open>(=) h2'\<close> in spec2)
  apply (simp add: sepconj_def fun_eq_iff)
  apply (metis disjoint_sym_iff partial_right_cancel2D)
  done

lemma precise_iff_all_sepconj_imp_sepcoimp:
  assumes \<open>\<forall>h u. P h \<longrightarrow> h ## u \<longrightarrow> P (h + u) \<longrightarrow> sepadd_unit u\<close>
  shows \<open>precise P \<longleftrightarrow> (\<forall>Q. P \<^emph> Q \<le> P \<sim>\<^emph> Q)\<close>
  using assms precise_iff_conj_distrib sepconj_conj_distrib_iff_sepconj_imp_sepcoimp
  by presburger

lemma precise_sepconj_eq_strong_sepcoimp:
  assumes \<open>\<forall>h u. P h \<longrightarrow> h ## u \<longrightarrow> P (h + u) \<longrightarrow> sepadd_unit u\<close>
  shows \<open>precise P \<longleftrightarrow> (\<forall>Q. P \<^emph> Q = (P \<^emph> \<top>) \<sqinter> (P \<sim>\<^emph> Q))\<close>
  using assms precise_iff_conj_distrib
    sepconj_conj_distrib_iff_sepconj_eq_strong_sepcoimp
  by presburger

end

class cancel_multiunit_sep_alg = cancel_perm_alg + multiunit_sep_alg
begin

lemma selfsep_selfadd_iff_unit:
  \<open>a ## a \<and> a + a = a \<longleftrightarrow> sepadd_unit a\<close>
  by (metis partial_right_cancelD unitof_disjoint2 unitof_inherits_disjointness unitof_is_unit2
      unitof_is_sepadd_unit unitof_sepadd_unit)

lemma strong_positivity:
  \<open>a ## b \<Longrightarrow> c ## c \<Longrightarrow> a + b = c \<Longrightarrow> c + c = c \<Longrightarrow> a = b \<and> b = c\<close>
  by (metis partial_right_cancelD positivity sepadd_unit_def weak_positivity
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

lemma precise_implies_unitlikes_are_units:
  \<open>precise P \<Longrightarrow> (\<forall>h u. P h \<longrightarrow> h ## u \<longrightarrow> P (h + u) \<longrightarrow> sepadd_unit u)\<close>
  by (meson cancel_left_to_unit eq_refl partial_le_plus precise_def)

end

class cancel_sep_alg = cancel_multiunit_sep_alg + sep_alg

subsection \<open>No-unit perm alg\<close>

text \<open>
  Here we create a perm_alg without any unit.
  Such an algebra is necessary to prove permission heaps are cancellative.
\<close>
class no_unit_perm_alg = perm_alg +
  assumes no_units: \<open>\<not> sepadd_unit a\<close>

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
  by (simp add: selfdisjoint_same half_additive_split half_self_disjoint)

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

context sep_alg
begin

lemma \<open>precise2 P \<Longrightarrow> (P \<midarrow>\<odot> P \<^emph> Q) \<le> Q\<close>
  by (simp add: precise2_def sepcoimp_septract_galois septract_reverse)

end

end