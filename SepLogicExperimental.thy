theory SepLogicExperimental
  imports SepLogic
begin


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
  using glb_rel_def resource_order.antisym by auto

lemma lub_lub_rel_eq[simp]:
  \<open>lub_rel a b ab \<Longrightarrow> lub a b = ab\<close>
  using lub_rel_def resource_order.antisym by auto

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
  using Glb_rel_def resource_order.antisym by auto

lemma Lub_Lub_rel_eq[simp]:
  \<open>Lub_rel A x \<Longrightarrow> Lub A = x\<close>
  using Lub_rel_def resource_order.antisym by auto

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
  by (clarsimp, meson glb_rel_def resource_order.antisym resource_order.trans)


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
  apply (meson resource_order.antisym resource_order.trans sepinf_least sepinf_leqL sepinf_leqR; fail)
  done

lemma disjoint_sepinf_of_add_impl_disjoint_sepinf_part:
  \<open>a ## b \<Longrightarrow>
    compatible a c \<Longrightarrow>
    compatible (a + b) c \<Longrightarrow>
    (a + b) \<sqinter> c ## y \<Longrightarrow>
    a \<sqinter> c ## y\<close>
  by (meson disjoint_preservation resource_order.trans partial_le_plus sepinf_least sepinf_leqL sepinf_leqR)

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


end