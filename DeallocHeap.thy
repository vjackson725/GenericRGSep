theory DeallocHeap
  imports Stabilisation
begin

section \<open> Sequencing Algebra \<close>

text \<open> Note this is a subalgebra of a relation algebra. \<close>

class seq =
  fixes seq :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixr \<open>\<triangleright>\<close> 110)

class skip =
  fixes skip :: 'a (\<open>\<I>\<close>)

class monoid_seq = seq + skip +
  assumes seq_assoc[algebra_simps, algebra_split_simps]: \<open>(a \<triangleright> b) \<triangleright> c = a \<triangleright> (b \<triangleright> c)\<close>
    and add_skip_left[simp]: \<open>\<I> \<triangleright> a = a\<close>
    and add_skip_right[simp]: \<open>a \<triangleright> \<I> = a\<close>
begin

sublocale add: monoid seq skip
  by standard (simp add: seq_assoc)+

end


section \<open>Permission Heaps with unstable reads and deallocation\<close>

typedef ('a,'b) dheap =
  \<open>{h::'a \<rightharpoonup> (rat \<times> rat) \<times> 'b.
    finite (dom h)
    \<and> (\<forall>x p s v. h x = Some ((p,s),v) \<longrightarrow> 0 < p \<and> p \<le> 1)
    \<and>  (\<forall>x p s v. h x = Some ((p,s),v) \<longrightarrow> 0 \<le> s \<and> s \<le> 1)}\<close>
  morphisms app_dheap Abs_dheap
  by (rule exI[where x=Map.empty], force)

lemmas Abs_dheap_inverse' = Abs_dheap_inverse[OF iffD2[OF mem_Collect_eq], OF conjI]

syntax app_dheap :: \<open>('a,'b) dheap \<Rightarrow> 'a \<Rightarrow> (rat \<times> 'b) option\<close> (infix \<open>\<bullet>\<close> 990)

setup_lifting type_definition_dheap

lemma dheap_ext:
  fixes a b :: \<open>('a,'b) dheap\<close>
  shows \<open>(\<And>x. a \<bullet> x = b \<bullet> x) \<Longrightarrow> a = b\<close>
  by (force intro: iffD1[OF app_dheap_inject])

lemma dheap_eq_iff:
  fixes a b :: \<open>('a,'b) dheap\<close>
  shows \<open>a = b \<longleftrightarrow> (\<forall>x. a \<bullet> x = b \<bullet> x)\<close>
  using dheap_ext by blast

lemmas app_dheap' = app_dheap[simplified]

lemma app_dheapD:
  assumes
  \<open>app_dheap h x = Some ((p,s),v)\<close>
  shows
    \<open>0 < p\<close> \<open>p \<le> 1\<close>
    \<open>0 \<le> s\<close> \<open>s \<le> 1\<close>
  using assms app_dheap'[of h]
  by force+

lemma Abs_app_dheap:
  assumes
    \<open>finite (dom m)\<close>
    \<open>\<And>x p s v. m x = Some ((p, s), v) \<Longrightarrow> 0 < p \<and> p \<le> 1\<close>
    \<open>\<And>x p s v. m x = Some ((p, s), v) \<Longrightarrow> 0 \<le> s \<and> s \<le> 1\<close>
  shows \<open>(Abs_dheap m) \<bullet> x = m x\<close>
  using assms
  by (simp add: Abs_dheap_inverse')

lemma Abs_dheap_inverse_app[simp]:
  \<open>Abs_dheap (app_dheap h) \<bullet> x = h \<bullet> x\<close>
  by (simp add: app_dheap_inverse)

lemma app_dheap_bounded_permD:
  \<open>a \<bullet> x = Some ((p,s), v) \<Longrightarrow> 1 \<le> p \<longleftrightarrow> p = 1\<close>
  \<open>a \<bullet> x = Some ((p,s), v) \<Longrightarrow> s \<le> 0 \<longleftrightarrow> s = 0\<close>
  \<open>a \<bullet> x = Some ((p,s), v) \<Longrightarrow> 1 \<le> s \<longleftrightarrow> s = 1\<close>
  by (simp add: app_dheapD order.antisym)+

lemma ex_app_dheap_iff:
  \<open>(\<exists>a. P (app_dheap a)) \<longleftrightarrow>
    (\<exists>m. finite (dom m) \<and>
      (P m \<and>
      (\<forall>x p s v. m x = Some ((p,s), v) \<longrightarrow> 0 < p \<and> p \<le> 1) \<and>
      (\<forall>x p s v. m x = Some ((p,s), v) \<longrightarrow> 0 \<le> s \<and> s \<le> 1)))\<close>
  by (rule iffI, metis app_dheap', metis Abs_dheap_inverse')

lemma ex_dheap_by_parts:
  \<open>(\<exists>a. \<forall>x. P x (a \<bullet> x)) \<longleftrightarrow>
    (finite {x. (\<exists>p s. (\<exists>v. P x (Some ((p, s), v))) \<and> 0 < p \<and> p \<le> 1 \<and> 0 \<le> s \<and> s \<le> 1) \<and> \<not> P x None} \<and>
     (\<forall>x. P x None \<or> (\<exists>p s. (\<exists>v. P x (Some ((p, s), v))) \<and> 0 < p \<and> p \<le> 1 \<and> 0 \<le> s \<and> s \<le> 1)))\<close>
  apply (subst ex_app_dheap_iff)
  apply (simp add: all_conj_distrib[symmetric])
  apply (subst finite_map_choice_iff)
  apply (simp add: split_option_ex all_conj_distrib)
  done


subsection \<open>Basic dheap operations\<close>

subsubsection \<open> Domain \<close>

lift_definition dom_dheap :: \<open>('a,'b) dheap \<Rightarrow> 'a set\<close> is \<open>dom\<close> .

lemma finite_dom_app_dheap[simp]:
  \<open>finite (dom (app_dheap a))\<close>
  using app_dheap by blast

lemma finite_dom_dheap[simp]:
  \<open>finite (dom_dheap a)\<close>
  by (simp add: dom_dheap.rep_eq)

lemma in_dom_dheap_iff:
  \<open>x \<in> dom_dheap a \<longleftrightarrow> (\<exists>c v. a \<bullet> x = Some (c,v))\<close>
  by (simp add: dom_dheap.rep_eq dom_def)

lemma dom_dheap_iff:
  \<open>dom_dheap a = {x. \<exists>c v. a \<bullet> x = Some (c,v)}\<close>
  by (simp add: dom_dheap.rep_eq dom_def)

subsubsection \<open> Map \<close>

text \<open>change the values of a dheap without changing the domain\<close>

lift_definition map_dheap :: \<open>(rat \<Rightarrow> rat) \<Rightarrow> (rat \<Rightarrow> rat) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('i,'a) dheap \<Rightarrow> ('i,'b) dheap\<close> is
  \<open>\<lambda>fp fs fv h. \<lambda>x. map_option (\<lambda>((p,s),v). ((if fp p \<le> 0 then 1 else min 1 (fp p), max 0 (min 1 (fs s))), fv v)) (h x)\<close>
  by (force simp add: dom_map_option)

lemma map_app_dheap_eq:
  \<open>map_dheap fp fs fv a \<bullet> x =
    map_option (\<lambda>((p,s),v). ((if fp p \<le> 0 then 1 else min 1 (fp p), max 0 (min 1 (fs s))), fv v)) (a \<bullet> x)\<close>
  by (metis map_dheap.rep_eq)

lemma map_app_dheap_eq_nice[simp]:
  assumes
    \<open>\<And>x. 0 < x \<Longrightarrow> x \<le> 1 \<Longrightarrow> 0 < fp x\<close>
    \<open>\<And>x. 0 < x \<Longrightarrow> x \<le> 1 \<Longrightarrow> fp x \<le> 1\<close>
    \<open>\<And>x. 0 \<le> x \<Longrightarrow> x \<le> 1 \<Longrightarrow> 0 \<le> fs x\<close>
    \<open>\<And>x. 0 \<le> x \<Longrightarrow> x \<le> 1 \<Longrightarrow> fs x \<le> 1\<close>
  shows
  \<open>map_dheap fp fs fv a \<bullet> x = map_option (map_prod (map_prod fp fs) fv) (a \<bullet> x)\<close>
  using assms
  apply (simp add: map_app_dheap_eq fun_eq_iff map_option_case split: option.splits)
  apply (metis app_dheapD leD max_def min.absorb2)
  done

lemma dom_map_dheap_eq[simp]:
  \<open>dom_dheap (map_dheap fp fs fv a) = dom_dheap a\<close>
  by (simp add: dom_dheap_iff map_dheap.rep_eq)

subsubsection \<open> Sequence \<close>

instantiation dheap :: (type, type) monoid_seq
begin

lift_definition seq_dheap :: \<open>('a,'b) dheap \<Rightarrow> ('a,'b) dheap \<Rightarrow> ('a,'b) dheap\<close>is
  \<open>\<lambda>a b. \<lambda>x. case a x of Some y \<Rightarrow> Some y | None \<Rightarrow> b x\<close>
  apply (rename_tac a b)
  apply (rule conjI)
   apply (rule_tac B=\<open>dom a \<union> dom b\<close> in rev_finite_subset; force split: option.splits)
  apply (simp split: option.splits; fail)
  done

lemma seq_app_dheap_eq[simp]:
  \<open>(a \<triangleright> b) \<bullet> x = (case a \<bullet> x of Some y \<Rightarrow> Some y | None \<Rightarrow> b \<bullet> x)\<close>
  by (simp add: seq_dheap.rep_eq)

lemma dom_seq_dheap_eq[simp]: \<open>dom_dheap (a \<triangleright> b) = dom_dheap a \<union> dom_dheap b\<close>
  by (simp add: dom_dheap.rep_eq seq_dheap.rep_eq set_eq_iff dom_def split: option.splits)


lift_definition skip_dheap :: \<open>('a,'b) dheap\<close> is \<open>Map.empty\<close>
  by simp

lemma skip_app_dheap[simp]:
  \<open>\<I> \<bullet> x = None\<close>
  by (simp add: skip_dheap.rep_eq)

instance
  by standard (simp add: dheap_eq_iff split: option.splits)+

end


subsubsection \<open> Restriction \<close>

lift_definition restrict_dheap :: \<open>('a,'b) dheap \<Rightarrow> 'a set \<Rightarrow> ('a,'b) dheap\<close>
  (infixr \<open>|`\<^sub>d\<close> 110) is \<open>(|`)\<close>
  by (clarsimp simp add: restrict_map_def dom_def)

lemma restrict_app_dheap_eq[simp]:
  \<open>(a |`\<^sub>d A) \<bullet> x = (if x \<in> A then a \<bullet> x else None)\<close>
  by (simp add: restrict_dheap.rep_eq)

lemma dom_restrict_dheap_eq[simp]: \<open>dom_dheap (a |`\<^sub>d A) = dom_dheap a \<inter> A\<close>
  by (simp add: dom_dheap.rep_eq seq_dheap.rep_eq set_eq_iff dom_def split: option.splits)

lemma restrict_dom_subset_eq:
  \<open>dom_dheap a \<subseteq> A \<Longrightarrow> a |`\<^sub>d A = a\<close>
  by (rule ccontr, clarsimp simp add: dom_dheap.rep_eq dheap_eq_iff dom_def subset_iff
      split: if_splits)

lemma restrict_sequence_right:
  \<open>(a \<triangleright> b) = (a \<triangleright> b |`\<^sub>d (- dom_dheap a))\<close>
  by (simp add: dheap_eq_iff dom_dheap_iff split: option.splits)

section \<open>Operations on permissions\<close>

definition plus_perm :: \<open>((rat \<times> rat) \<times> 'a) option \<Rightarrow> ((rat \<times> rat) \<times> 'a) option \<Rightarrow> ((rat \<times> rat) \<times> 'a) option\<close>
  (infixl \<open>\<oplus>\<^sub>d\<close> 65) where
  \<open>plus_perm a b \<equiv> case b of
                    Some ((p2,s2), v2) \<Rightarrow>
                      (case a of
                        Some ((p1,s1), v1) \<Rightarrow> Some ((min (p1+p2) 1, min (s1+s2) 1), v1)
                        | None \<Rightarrow> Some ((p2,s2), v2))
                    | None \<Rightarrow> a\<close>

lemma finite_dom_add[simp]:
  \<open>finite (dom (\<lambda>x. a x \<oplus>\<^sub>d b x)) \<longleftrightarrow> finite (dom a) \<and> finite (dom b)\<close>
  by (simp add: dom_def plus_perm_def imp_conv_disj del: imp_conv_disj[symmetric]
      split: option.splits, blast)

lemma plus_perm_simps[simp]:
  \<open>a \<oplus>\<^sub>d None = a\<close>
  \<open>None \<oplus>\<^sub>d b = b\<close>
  \<open>Some ((p1,s1), v1) \<oplus>\<^sub>d Some ((p2,s2), v2) = Some ((min (p1 + p2) 1, min (s1 + s2) 1), v1)\<close>
  by (force simp add: plus_perm_def split: option.splits)+

lemma plus_perm_eq_None_iff[simp]:
  \<open>a \<oplus>\<^sub>d b = None \<longleftrightarrow> a = None \<and> b = None\<close>
  by (force simp add: plus_perm_def split: option.splits)

lemma plus_perm_eq_Some_iff:
  \<open>\<And>a p2 s2 v2 c.
    a \<oplus>\<^sub>d Some ((p2,s2), v2) = c \<longleftrightarrow>
      (case a of None \<Rightarrow> c = Some ((p2,s2), v2) | Some ((p1,s1), v1) \<Rightarrow> c = Some ((min (p1 + p2) 1, min (s1 + s2) 1), v1))\<close>
  \<open>\<And>p1 s1 v1 b c.
    Some ((p1,s1), v1) \<oplus>\<^sub>d b  = c \<longleftrightarrow>
      (case b of None \<Rightarrow> c = Some ((p1,s1), v1) | Some ((p2,s2), v2) \<Rightarrow> c = Some ((min (p1 + p2) 1, min (s1 + s2) 1), v1))\<close>
  \<open>\<And>a b p s v.
    (a \<oplus>\<^sub>d b) = Some ((p,s), v) \<longleftrightarrow>
      (b = None \<longrightarrow> a = Some ((p,s), v)) \<and>
      (a = None \<longrightarrow> b = Some ((p,s), v)) \<and>
      (\<forall>p1 s1 v1. a = Some ((p1,s1), v1) \<longrightarrow>
        (\<forall>p2 s2 v2. b = Some ((p2,s2), v2) \<longrightarrow>
          p = min (p1 + p2) 1 \<and> s = min (s1 + s2) 1 \<and> v = v1))\<close>
  by (force simp add: plus_perm_def split: option.splits)+

lemmas plus_perm_eq_Some_iff_rev = HOL.trans[OF HOL.eq_commute plus_perm_eq_Some_iff(3)]

(*
definition minus_perm :: \<open>(rat \<times> 'a) option \<Rightarrow> (rat \<times> 'a) option \<Rightarrow> (rat \<times> 'a) option\<close>
  (infixl \<open>\<ominus>\<^sub>d\<close> 65) where
  \<open>minus_perm a b \<equiv> case a of
                      Some (c1, v1) \<Rightarrow>
                        (case b of
                          Some (c2, v2) \<Rightarrow> if v1 = v2 then Some (max (c2 - c1) 0, v1) else None
                        | None \<Rightarrow> Some (c1, v1))
                    | None \<Rightarrow> None\<close>

lemma finite_dom_minus[intro]:
  \<open>finite (dom a) \<Longrightarrow> finite (dom (\<lambda>x. a x \<ominus>\<^sub>d b x))\<close>
  by (simp add: dom_def minus_perm_def Collect_conj_eq split: option.splits)

lemma minus_perm_None[simp]:
  \<open>a \<ominus>\<^sub>d None = a\<close>
  \<open>None \<ominus>\<^sub>d b = None\<close>
  by (simp add: minus_perm_def split: option.splits)+

lemma minus_perm_Some_iff:
  \<open>Some (ca, va) \<ominus>\<^sub>d b = x \<longleftrightarrow>
      b = None \<and> x = Some (ca, va) \<or>
      (\<exists>cb. b = Some (cb, va) \<and> x = Some (max 0 (cb - ca), va)) \<or>
      (\<exists>cb vb. vb \<noteq> va \<and> b = Some (cb, vb) \<and> x = None)\<close>
  \<open>a \<ominus>\<^sub>d Some (cb, vb) = x \<longleftrightarrow>
      a = None \<and> x = None \<or>
      (\<exists>ca. a = Some (ca, vb) \<and> x = Some (max 0 (cb - ca), vb)) \<or>
      (\<exists>ca va. va \<noteq> vb \<and> a = Some (ca, va) \<and> x = None)\<close>
  \<open>a \<ominus>\<^sub>d b = Some (c, v) \<longleftrightarrow>
      a = Some (c, v) \<and> b = None \<or>
      (\<exists>c1. a = Some (c1, v) \<and> (\<exists>c2. b = Some (c2, v) \<and> c = max (c2 - c1) 0))\<close>
  by (force simp add: minus_perm_def split: option.splits)+


lemma minus_perm_eq_None[simp]:
  \<open>a \<ominus>\<^sub>d b = None \<longleftrightarrow>
    (a = None \<or> (\<exists>c1 v1. a = Some (c1, v1) \<and> (\<exists>c2 v2. b = Some (c2, v2) \<and> v1 \<noteq> v2)))\<close>
  by (simp add: minus_perm_def max_def split: option.splits)

lemma
  fixes c1 c2 :: \<open>'a :: linordered_idom\<close>
  shows
    \<open>(c2 = min (c1 + max (c1 - c2) 0) m) = (c2 = c1 \<and> c2 \<le> m \<or> c2 \<le> c1 \<and> c2 = m)\<close>
  by (fastforce simp add: min_le_iff_disj le_max_iff_disj)

lemma perm_eq_plus_minus_iff:
  \<open>b = a \<oplus>\<^sub>d (b \<ominus>\<^sub>d a) \<longleftrightarrow>
    a = None \<or>
      b = a \<and> (\<exists>c v. a = Some (c, v) \<and> c \<le> 1) \<or>
      (\<exists>v. b = Some (1, v) \<and> (\<exists>c1\<ge>1. a = Some (c1, v)))\<close>
  by (force simp add: plus_perm_def minus_perm_def split: option.splits)
*)

subsection \<open> Disjointness \<close>

definition disjoint_set_dheap :: \<open>('a,'b) dheap \<Rightarrow> 'a set \<Rightarrow> ('a,'b) dheap \<Rightarrow> bool\<close>
  ("_ ##\<^bsub>_\<^esub> _" [61,0,61] 60) where
  \<open>a ##\<^bsub>A\<^esub> b \<equiv> \<forall>x\<in>A.
    \<forall>p1 s1 v1. a \<bullet> x = Some ((p1,s1), v1) \<longrightarrow>
      (\<forall>p2 s2 v2. b \<bullet> x = Some ((p2,s2), v2) \<longrightarrow> p1 + p2 \<le> 1 \<and> s1 + s2 \<le> 1 \<and> v1 = v2)\<close>

lemma disjoint_set_un_eq[simp]:
  \<open>a ##\<^bsub>A \<union> B\<^esub> b \<longleftrightarrow> a ##\<^bsub>A\<^esub> b \<and> a ##\<^bsub>B\<^esub> b\<close>
  by (simp add: disjoint_set_dheap_def Ball_def, blast)

lemma disjoint_set_antimono_dheap:
  \<open>Y \<subseteq> X \<Longrightarrow> a ##\<^bsub>X\<^esub> b \<Longrightarrow> a ##\<^bsub>Y\<^esub> b\<close>
  by (metis Un_absorb2 disjoint_set_un_eq)

lemma disjoint_skip[iff]:
  \<open>\<I> ##\<^bsub>A\<^esub> b\<close>
  \<open>a ##\<^bsub>A\<^esub> \<I>\<close>
  by (clarsimp simp add: disjoint_set_dheap_def)+

lemma disjoint_seq[simp]:
  \<open>a1 \<triangleright> a2 ##\<^bsub>A\<^esub> b \<longleftrightarrow> a1 ##\<^bsub>A\<^esub> b \<and> a2 ##\<^bsub>A - dom_dheap a1\<^esub> b\<close>
  \<open>b ##\<^bsub>A\<^esub> a1 \<triangleright> a2 \<longleftrightarrow> b ##\<^bsub>A\<^esub> a1 \<and> b ##\<^bsub>A - dom_dheap a1\<^esub> a2\<close>
   apply (clarsimp simp add: disjoint_set_dheap_def dom_dheap_iff Ball_def
      all_conj_distrib[symmetric] split: option.splits)
   apply (rule all_cong1, case_tac \<open>app_dheap a1 x\<close>; force)
   apply (clarsimp simp add: disjoint_set_dheap_def dom_dheap_iff Ball_def
      all_conj_distrib[symmetric] split: option.splits)
   apply (rule all_cong1, case_tac \<open>app_dheap a1 x\<close>; force)
  done


text \<open>Define disjointness on dheaps\<close>
instantiation dheap :: (type,type) disjoint
begin

definition disjoint_dheap :: \<open>('a,'b) dheap \<Rightarrow> ('a,'b) dheap \<Rightarrow> bool\<close> where
  \<open>disjoint_dheap a b \<equiv> a ##\<^bsub>UNIV\<^esub> b\<close>

instance by standard

end

lemmas disjoint_dheap_def' = disjoint_dheap_def disjoint_set_dheap_def

subsection \<open> Addition \<close>

text \<open>Define plus on dheaps\<close>
instantiation dheap :: (type, type) plus
begin

lift_definition plus_dheap :: \<open>('a,'b) dheap \<Rightarrow> ('a,'b) dheap \<Rightarrow> ('a,'b) dheap\<close> is
  \<open>\<lambda>ma mb. \<lambda>x. ma x \<oplus>\<^sub>d mb x\<close>
  apply (rename_tac ma mb)
  apply (simp add: dom_def plus_perm_def split: option.splits)
  apply (rule conjI)
   apply (rule_tac B=\<open>dom ma \<union> dom mb\<close> in rev_finite_subset; force simp add: dom_def)
  apply (fastforce intro: add_nonneg_nonneg)
  done

instance by standard

end

lemma Rep_add_in_bounds:
  assumes \<open>a \<bullet> x \<oplus>\<^sub>d b \<bullet> x = Some ((p,s), v)\<close>
  shows
    \<open>0 < p\<close> \<open>p \<le> 1\<close>
    \<open>0 \<le> s\<close> \<open>s \<le> 1\<close>
  using assms
  by (simp add: dom_def plus_dheap_def plus_perm_def app_dheapD add_pos_pos eq_commute[of \<open>min _ _\<close>]
      split: option.splits prod.splits; fail)+

lemma app_plus_dheap[simp]:
  \<open>(a + b) \<bullet> x = a \<bullet> x \<oplus>\<^sub>d b \<bullet> x\<close>
  apply (simp add: disjoint_dheap_def' plus_dheap_def)
  apply (subst Abs_dheap_inverse; force simp add: Rep_add_in_bounds)
  done

lemma restrict_dheap_add_eq[simp]:
  \<open>(a + b) |`\<^sub>d A = a |`\<^sub>d A + b |`\<^sub>d A\<close>
  by (simp add: dheap_eq_iff)

lemma dom_plus_dheap_eq[simp]: \<open>dom_dheap (h1 + h2) = dom_dheap h1 \<union> dom_dheap h2\<close>
  by (simp add: dom_dheap.rep_eq plus_perm_def dom_def set_eq_iff split: option.splits)

(*
text \<open>Define minus on dheaps\<close>

instantiation dheap :: (type, type) minus
begin

lift_definition minus_dheap :: \<open>('a,'b) dheap \<Rightarrow> ('a,'b) dheap \<Rightarrow> ('a,'b) dheap\<close> is
  \<open>\<lambda>ma mb. \<lambda>x. ma x \<ominus>\<^sub>d mb x\<close>
  by (force simp add: dom_def minus_perm_def split: option.splits)

instance by standard

end

lemma Rep_minus_in_bounds:
  assumes \<open>app_dheap a p \<ominus>\<^sub>d app_dheap b p = Some (c, v)\<close>
  shows \<open>c \<le> 1\<close> \<open>0 \<le> c\<close>
  using assms
  by (clarsimp simp add: dom_def minus_dheap_def minus_perm_def app_dheap_bounded_permD
      add_increasing2 diff_le_eq split: option.splits prod.splits if_splits)+

lemma minus_plus_dheap[simp]:
  \<open>(a - b) \<bullet> x = a \<bullet> x \<ominus>\<^sub>d b \<bullet> x\<close>
  apply (simp add: disjoint_dheap_def' minus_dheap_def)
  apply (subst Abs_dheap_inverse; force simp add: Rep_minus_in_bounds)
  done

lemma dheap_eq_plus_minus_iff:
  fixes a b :: \<open>('p,'v) dheap\<close>
  shows \<open>b = a + (b - a) \<longleftrightarrow> (\<forall>x. a \<bullet> x = None \<or> a \<bullet> x = b \<bullet> x)\<close>
  by (simp add: dheap_eq_iff perm_eq_plus_minus_iff,
      metis app_dheap_bounded_permD(2) nle_le not_Some_prod_eq)
*)

text \<open>Define less than and less than or equal on dheaps\<close>
instantiation dheap :: (type, type) preorder
begin

definition less_eq_dheap :: \<open>('a,'b) dheap \<Rightarrow> ('a,'b) dheap \<Rightarrow> bool\<close> where
  \<open>less_eq_dheap ma mb \<equiv>
    \<forall>x. \<forall>pa sa v. ma \<bullet> x  = Some ((pa, sa), v) \<longrightarrow> (\<exists>pb\<ge>pa. \<exists>sb\<ge>sa. mb \<bullet> x = Some ((pb,sb), v))\<close>

definition less_dheap :: \<open>('a,'b) dheap \<Rightarrow> ('a,'b) dheap \<Rightarrow> bool\<close> where
  \<open>less_dheap a b \<equiv> a \<le> b \<and> \<not>(b \<le> a)\<close>

instance
  by standard (simp add: less_dheap_def less_eq_dheap_def; meson order.trans)+

end

(*
definition compl_perm :: \<open>(rat \<times> 'a) option \<Rightarrow> (rat \<times> 'a) option \<Rightarrow> (rat \<times> 'a) option\<close>
  (infixl \<open>\<oslash>\<^sub>d\<close> 65) where
  \<open>compl_perm a b \<equiv> case a of
                      Some (c1, v1) \<Rightarrow>
                        (case b of
                          Some (c2, v2) \<Rightarrow>
                            if c2 = c1
                            then None
                            else Some (c2 - c1, v2)
                        | None \<Rightarrow> Some (c1, v1))
                    | None \<Rightarrow> b\<close>

lemma compl_dheap_eq[simp]:
  \<open>None \<oslash>\<^sub>d b = b\<close>
  \<open>a \<oslash>\<^sub>d None = a\<close>
  \<open>Some (c, v1) \<oslash>\<^sub>d Some (c, v2) = None\<close>
  \<open>c1 \<noteq> c2 \<Longrightarrow> Some (c1, v1) \<oslash>\<^sub>d Some (c2, v2) = Some (c2 - c1, v2)\<close>
  by (force simp add: compl_perm_def split: option.splits)+


lemma subheap_plus_compl_dheap_inverse:
  \<open>a \<bullet> x \<subseteq>\<^sub>d b \<bullet> x \<Longrightarrow> (a \<bullet> x \<oplus>\<^sub>d (b \<bullet> x \<oslash>\<^sub>d a \<bullet> x)) \<subseteq>\<^sub>d b \<bullet> x\<close>
  apply (clarsimp simp add: plus_perm_def compl_perm_def less_eq_perm_def split: option.splits)
  apply (intro conjI impI allI)
     apply force
    apply force
   apply (drule_tac spec, drule_tac spec, drule_tac mp, blast)
  apply clarsimp
  done

lemma app_Abs_compl_dheap[simp]:
  \<open>\<forall>x ca v. app_dheap a x = Some (ca, v) \<longrightarrow> (\<exists>cb\<ge>ca. app_dheap b x = Some (cb, v)) \<Longrightarrow>
    Abs_dheap (\<lambda>x. a \<bullet> x \<oslash>\<^sub>d b \<bullet> x) \<bullet> x = a \<bullet> x \<oslash>\<^sub>d b \<bullet> x\<close>
  apply (subst Abs_dheap_inverse)
   apply clarsimp
   apply (rule conjI)
    apply (rule rev_finite_subset[of \<open>dom_dheap b\<close>];
      force simp add: compl_perm_def dom_dheap_def less_eq_perm_def split: option.splits)
   apply (clarsimp simp add: compl_perm_def dom_dheap_def less_eq_perm_def split: option.splits)
   apply (intro conjI allI)
     apply (force simp add: app_dheap_bounded_permD)
    apply (force simp add: app_dheap_bounded_permD)
   apply (metis app_dheap_bounded_permD(1,2) cancel_comm_monoid_add_class.diff_zero diff_mono
      option.inject prod.inject)
  apply (force simp add: app_dheap_bounded_permD)
  done
*)

instantiation dheap :: (type,type) seplogic
begin

lift_definition zero_dheap :: \<open>('a,'b) dheap\<close> is \<open>Map.empty\<close>
  by simp

lemma app_zero_dheap[simp]:
  \<open>0 \<bullet> x = None\<close>
  by (simp add: zero_dheap.rep_eq)

lift_definition bot_dheap :: \<open>('a,'b) dheap\<close> is \<open>Map.empty\<close>
  by simp

lemma app_bot_dheap[simp]:
  \<open>\<bottom> \<bullet> x = None\<close>
  by (simp add: bot_dheap.rep_eq)

lemma bot_dheap_eq_zero_dheap:
  \<open>(\<bottom> :: ('a,'b) dheap) = 0\<close>
  by (simp add: zero_dheap.abs_eq bot_dheap.abs_eq)

lemma le_iff_sepadd_helper:
  fixes a b :: \<open>('a,'b) dheap\<close>
  shows \<open>(a \<le> b) = (\<exists>c. a ## c \<and> b = a + c)\<close>
  apply (rule iffI)
   apply (clarsimp simp add: dheap_eq_iff disjoint_dheap_def' less_eq_dheap_def split: option.splits)
(*
   apply (rule_tac x=\<open>Abs_dheap (\<lambda>x. a \<bullet> x \<oslash>\<^sub>d b \<bullet> x)\<close> in exI)
   apply (simp, force simp add: compl_perm_def plus_perm_def app_dheap_bounded_permD
      split: option.splits)
  apply (force simp add: less_eq_dheap_def less_eq_perm_def plus_perm_def app_dheap_bounded_permD
      split: option.splits)
  done
*)
  sorry


instance
  apply standard
           apply (clarsimp simp add: less_eq_dheap_def dheap_eq_iff option_eq_iff)
           apply (fastforce split: option.splits)
          apply (simp add: less_eq_dheap_def; fail)
         apply (force simp add: disjoint_dheap_def')
        apply (force simp add: disjoint_dheap_def')
  subgoal
    apply (clarsimp simp add: disjoint_dheap_def' plus_perm_def split: option.splits)
    apply (drule_tac x=x in spec)+
    apply clarsimp
    apply (elim disjE conjE)
     apply clarsimp
     apply (metis app_dheapD(1) app_dheapD(3) dual_order.trans group_cancel.add1 leD le_add_same_cancel1 linorder_le_cases)
    apply force
    done
  subgoal
    apply (clarsimp simp add: disjoint_dheap_def')
    apply (drule_tac x=x in spec)+
    apply (simp add: plus_perm_def min_add_distrib_right min_le_iff_disj split: option.splits prod.splits)
    apply force
    done
     apply (simp add: le_iff_sepadd_helper; fail)
  subgoal
    apply (clarsimp simp add: dheap_eq_iff plus_perm_def split: option.splits)
    apply (simp add: add.commute disjoint_dheap_def' min_add_distrib_right)
    apply ((drule spec)+, (drule mp, assumption)+)+
    apply (simp add: add.commute add.left_commute)
    done
  subgoal
    apply (clarsimp simp add: disjoint_dheap_def' dheap_eq_iff)
    apply (force simp add: plus_perm_def eq_iff min_le_iff_disj split: option.splits)
    done
  apply (simp add: dheap_eq_iff; fail)
  done

end


lemma disjoint_restrict_dheap_iff[simp]:
  \<open>a |`\<^sub>d A ##\<^bsub>X\<^esub> b \<longleftrightarrow> a ##\<^bsub>X \<inter> A\<^esub> b\<close>
  \<open>a ##\<^bsub>X\<^esub> b |`\<^sub>d B \<longleftrightarrow> a ##\<^bsub>X \<inter> B\<^esub> b\<close>
  by (force simp add: disjoint_set_dheap_def Ball_def)+


section \<open> The stable and zero domains \<close>

definition stabledom :: \<open>('a,'b) dheap \<Rightarrow> 'a set\<close> where
  \<open>stabledom a \<equiv> {x. \<exists>p s v. a \<bullet> x = Some ((p,s),v) \<and> s > 0}\<close>

definition zerodom :: \<open>('a,'b) dheap \<Rightarrow> 'a set\<close> where
  \<open>zerodom a \<equiv> {x. \<exists>p s v. a \<bullet> x = Some ((p,s),v) \<and> s = 0}\<close>

lemma dom_dheap_sep:
  \<open>dom_dheap a = stabledom a \<union> zerodom a\<close>
  by (fastforce simp add: dom_dheap_def stabledom_def zerodom_def dom_def set_eq_iff
      dest: app_dheap_bounded_permD)

lemma stabledom_subseteq_dom_dheap:
  \<open>stabledom a \<subseteq> dom_dheap a\<close>
  by (simp add: dom_dheap_sep)

subsection \<open>stabledom simps\<close>

lemma restrict_stabledom_eq[simp]:
  \<open>stabledom (a |`\<^sub>d A) = stabledom a \<inter> A\<close>
  by (simp add: stabledom_def set_eq_iff)

lemma seq_stabledom_eq[simp]:
  \<open>stabledom (a \<triangleright> b) = stabledom a \<union> (stabledom b - zerodom a)\<close>
  by (fastforce dest: app_dheap_bounded_permD
      simp add: stabledom_def set_eq_iff zerodom_def split: option.splits)

lemma stabledom_plus[simp]:
  \<open>stabledom (a + b) = stabledom a \<union> stabledom b\<close>
  apply (clarsimp simp add: stabledom_def set_eq_iff plus_perm_eq_Some_iff)
  apply (case_tac \<open>app_dheap a x\<close>)
   apply force
  apply (case_tac \<open>app_dheap b x\<close>)
   apply force
  apply (simp, fastforce dest: app_dheap_bounded_permD)
  done

lemma map_stabledom_eq:
  \<open>\<forall>x. x > 0 \<longrightarrow> fp x > 0 \<Longrightarrow> \<forall>x. x > 0 \<longleftrightarrow> fs x > 0 \<Longrightarrow> stabledom (map_dheap fp fs fv a) = stabledom a\<close>
  apply (clarsimp simp add: stabledom_def set_eq_iff map_app_dheap_eq not_le max_def
      split: option.splits if_splits)
  apply (safe; simp)
  apply (metis leD less_numeral_extra(1) min_eq_k_iff)
  done

lemma map_stabledom_reduce1:
  \<open>\<forall>x. x > 0 \<longrightarrow> fp x > 0 \<Longrightarrow> stabledom (map_dheap fp fs fv a) = stabledom (map_dheap id fs fv a)\<close>
  apply (clarsimp simp add: stabledom_def set_eq_iff map_app_dheap_eq not_le not_less max_def
      split: option.splits if_splits)
  apply (safe; simp)
  apply (metis leD less_numeral_extra(1) min_eq_k_iff)+
  done

lemma map_stabledom_reduce2:
  \<open>\<forall>x. x > 0 \<longleftrightarrow> fs x > 0 \<Longrightarrow> stabledom (map_dheap fp fs fv a) = stabledom (map_dheap fp id fv a)\<close>
  apply (clarsimp simp add: stabledom_def set_eq_iff map_app_dheap_eq not_le not_less max_def
      split: option.splits if_splits)
  apply (safe; simp)
  apply (metis leD less_numeral_extra(1) min_eq_k_iff)+
  done

lemma map_stabledom_permid_eq[simp]:
  \<open>stabledom (map_dheap id id fv a) = stabledom a\<close>
  by (force simp add: map_stabledom_eq)

lemma map_stabledom_perm_mult_eq[simp]:
  \<open>k > 0 \<Longrightarrow> stabledom (map_dheap (\<lambda>x. x * k) fs fv a) = stabledom (map_dheap id fs fv a)\<close>
  \<open>k > 0 \<Longrightarrow> stabledom (map_dheap fp (\<lambda>x. x * k) fv a) = stabledom (map_dheap fp id fv a)\<close>
  using map_stabledom_reduce1[of \<open>\<lambda>x. x * k\<close>] map_stabledom_reduce2[of \<open>\<lambda>x. x * k\<close>]
  by (force simp add: zero_less_mult_iff)+

lemma map_stabledom_perm_frac_eq[simp]:
  \<open>k > 0 \<Longrightarrow> stabledom (map_dheap (\<lambda>x. x / k) fs fv a) = stabledom (map_dheap id fs fv a)\<close>
  \<open>k > 0 \<Longrightarrow> stabledom (map_dheap fp (\<lambda>x. x / k) fv a) = stabledom (map_dheap fp id fv a)\<close>
  using map_stabledom_reduce1[of \<open>\<lambda>x. x / k\<close>] map_stabledom_reduce2[of \<open>\<lambda>x. x / k\<close>]
  by (force simp add: zero_less_divide_iff)+

subsection \<open>zerodom simps\<close>

lemma restrict_zerodom_eq[simp]:
  \<open>zerodom (a |`\<^sub>d A) = zerodom a \<inter> A\<close>
  by (simp add: zerodom_def set_eq_iff)

lemma seq_zerodom_eq[simp]:
  \<open>zerodom (a \<triangleright> b) = zerodom a \<union> (zerodom b - stabledom a)\<close>
    by (fastforce dest: app_dheap_bounded_permD
      simp add: stabledom_def set_eq_iff zerodom_def split: option.splits)

lemma map_zerodom_eq:
  \<open>\<forall>x. x > 0 \<longrightarrow> fp x > 0 \<Longrightarrow> \<forall>x. x > 0 \<longleftrightarrow> fs x > 0 \<Longrightarrow> zerodom (map_dheap fp fs fv a) = zerodom a\<close>
  apply (clarsimp simp add: zerodom_def set_eq_iff map_app_dheap_eq not_le min_def max_def
      split: option.splits if_splits)
  apply safe
      apply force
     apply (metis app_dheapD(3) less_eq_rat_def)
    apply (metis app_dheapD(3) less_eq_rat_def)
   apply (metis app_dheap_bounded_permD(2) leI order_less_irrefl)
  apply (metis order.strict_trans1 leI nless_le zero_less_one)
  done

lemma map_zerodom_reduce1:
  \<open>\<forall>x. x > 0 \<longrightarrow> fp x > 0 \<Longrightarrow> zerodom (map_dheap fp fs fv a) = zerodom (map_dheap id fs fv a)\<close>
  by (clarsimp simp add: zerodom_def set_eq_iff map_app_dheap_eq not_le not_less max_def
      split: option.splits if_splits)

lemma map_zerodom_reduce2:
  \<open>\<forall>x. x > 0 \<longleftrightarrow> fs x > 0 \<Longrightarrow> zerodom (map_dheap fp fs fv a) = zerodom (map_dheap fp id fv a)\<close>
  apply (clarsimp simp add: zerodom_def set_eq_iff map_app_dheap_eq not_le not_less max_def
      split: option.splits if_splits)
  apply (metis (no_types, lifting) less_eq_rat_def min_eq_k_iff not_less_iff_gr_or_eq zero_less_one_class.zero_le_one)
  done

lemma map_zerodom_permid_eq[simp]:
  \<open>zerodom (map_dheap id id fv a) = zerodom a\<close>
  by (force simp add: map_zerodom_eq)

lemma map_zerodom_perm_mult_eq[simp]:
  \<open>k > 0 \<Longrightarrow> zerodom (map_dheap (\<lambda>x. x * k) fs fv a) = zerodom (map_dheap id fs fv a)\<close>
  \<open>k > 0 \<Longrightarrow> zerodom (map_dheap fp (\<lambda>x. x * k) fv a) = zerodom (map_dheap fp id fv a)\<close>
  using map_zerodom_reduce1[of \<open>\<lambda>x. x * k\<close>] map_zerodom_reduce2[of \<open>\<lambda>x. x * k\<close>]
  by (force simp add: zero_less_mult_iff)+

lemma map_zerodom_perm_frac_eq[simp]:
  \<open>k > 0 \<Longrightarrow> zerodom (map_dheap (\<lambda>x. x / k) fs fv a) = zerodom (map_dheap id fs fv a)\<close>
  \<open>k > 0 \<Longrightarrow> zerodom (map_dheap fp (\<lambda>x. x / k) fv a) = zerodom (map_dheap fp id fv a)\<close>
  using map_zerodom_reduce1[of \<open>\<lambda>x. x / k\<close>] map_zerodom_reduce2[of \<open>\<lambda>x. x / k\<close>]
  by (force simp add: zero_less_divide_iff)+

subsection \<open> Halve permissions in a set \<close>

text \<open>Halve the permissions in a given set\<close>
definition halve_dheap :: \<open>('a,'b) dheap \<Rightarrow> 'a set \<Rightarrow> ('a,'b) dheap\<close> where
  \<open>halve_dheap a A \<equiv> map_dheap (\<lambda>c. c/2) (\<lambda>c. c/2) id (a |`\<^sub>d A) \<triangleright> a\<close>

lemma halve_dheap_iff:
  \<open>halve_dheap a A \<bullet> x =
    (case a \<bullet> x of
        None \<Rightarrow> None
      | Some ((p,s),v) \<Rightarrow>
          if x \<in> A
          then Some ((p/2,s/2),v)
          else Some ((p,s),v))\<close>
  by (clarsimp split: option.splits
      simp add: halve_dheap_def comp_def max_mult_distrib_right min_mult_distrib_right)

lemma halve_dheap_app_eq:
  \<open>halve_dheap a A \<bullet> x = (if x \<in> A then map_dheap (\<lambda>x. x / 2) (\<lambda>x. x / 2) id a \<bullet> x else a \<bullet> x)\<close>
  by (simp add: halve_dheap_def split: option.splits)

lemma halve_dheap_subheap:
  \<open>halve_dheap a A \<le> a\<close>
  by (fastforce simp add: less_eq_dheap_def halve_dheap_iff zero_le_mult_iff split: option.splits
      dest: app_dheapD(1)[of a, THEN less_imp_le] app_dheapD(3))

lemma stabledom_halve_dheap_eq[simp]:
  \<open>stabledom (halve_dheap a A) = stabledom a\<close>
  by (force simp add: halve_dheap_def dom_dheap_sep)


section \<open> Stable rely-relation \<close>

definition stablerel :: \<open>('a,'b) dheap \<Rightarrow> ('a,'b) dheap \<Rightarrow> bool\<close> where
  \<open>stablerel a b \<equiv> \<forall>x v.
    (\<exists>pa sa. a \<bullet> x = Some ((pa,sa),v) \<and> 0 < sa) \<longrightarrow> (\<exists>pb sb. b \<bullet> x = Some ((pb,sb),v) \<and> 0 < sb)\<close>

lemma stablerel_refl:
  \<open>stablerel a a\<close>
  by (simp add: stablerel_def split: option.splits if_splits)

lemma stablerel_trans:
  \<open>stablerel a b \<Longrightarrow> stablerel b c \<Longrightarrow> stablerel a c\<close>
  by (clarsimp simp add: stablerel_def)

lemma stablerel_reflp:
  \<open>reflp stablerel\<close>
  by (simp add: reflpI stablerel_refl)

lemma stablerel_transp:
  \<open>transp stablerel\<close>
  using stablerel_trans transpI by blast

lemma stablerel_comp:
  \<open>stablerel OO stablerel = stablerel\<close>
  by (force simp add: fun_eq_iff stablerel_def relcompp_apply)

lemma tranclp_stablerel_eq[simp]:
  \<open>stablerel\<^sup>*\<^sup>* = stablerel\<close>
  apply (rule antisym)
   apply (clarsimp simp add: le_fun_def, rule rtranclp_induct, assumption)
    apply (force intro: stablerel_refl stablerel_trans)+
  done

lemma stablerel_add:
  \<open>a1 ## a2 \<Longrightarrow> b1 ## b2 \<Longrightarrow> stablerel a1 b1 \<Longrightarrow> stablerel a2 b2 \<Longrightarrow> stablerel (a1 + a2) (b1 + b2)\<close>
  apply (clarsimp simp add: stablerel_def stabledom_def plus_perm_def split: option.splits)
  apply (drule_tac x=x in spec)+
  apply (intro conjI impI allI; simp)
         apply force
        apply force
       apply (simp add: add_strict_increasing app_dheapD(3); fail)
      apply (force simp add: disjoint_dheap_def')
     apply (simp add: add_nonneg_pos app_dheapD(3); fail)
    apply (force simp add: disjoint_dheap_def')
   apply (fastforce simp add: disjoint_dheap_def')  
  apply (metis add.commute add_pos_nonneg app_dheapD(3) nless_le)
  done

lemma stablerel_subheap:
  \<open>stablerel a b \<Longrightarrow> a' \<le> a \<Longrightarrow> b' \<le> b \<Longrightarrow> stabledom a' \<subseteq> stabledom b' \<Longrightarrow> stablerel a' b'\<close>
  apply (clarsimp simp add: stablerel_def stabledom_def le_iff_sepadd plus_perm_eq_Some_iff
      set_eq_iff subset_iff)
  apply (rename_tac a'' b'' x va' pa' sa')
  apply (drule_tac x=x in spec)+
  apply (case_tac \<open>a'' \<bullet> x\<close>; case_tac \<open>b'' \<bullet> x\<close>)
     apply (force simp add: add_pos_nonneg app_dheap_bounded_permD)
    apply (force simp add: add_pos_nonneg app_dheap_bounded_permD)

  oops

lemma stablerel_impl_subseteq_stabledom:
  \<open>stablerel a b \<Longrightarrow> stabledom a \<subseteq> stabledom b\<close>
  by (force simp add: stablerel_def stabledom_def)


lemma stablerel_additivity_of_update:
  assumes
    \<open>a1 ## a2\<close>
    \<open>stablerel (a1 + a2) b\<close>
  shows
    \<open>\<exists>b1 b2. b1 ## b2 \<and> b = b1 + b2 \<and> stablerel a1 b1 \<and> stablerel a2 b2\<close>
proof - 
  let ?bnew = \<open>dom_dheap b - stabledom a1 - stabledom a2\<close>
  let ?b1=\<open>halve_dheap (b |`\<^sub>d (stabledom a1 \<union> ?bnew)) (stabledom a2 \<union> ?bnew)\<close>
  let ?b2=\<open>halve_dheap (b |`\<^sub>d (stabledom a2 \<union> ?bnew)) (stabledom a1 \<union> ?bnew)\<close>

  have
    \<open>stabledom a1 \<subseteq> stabledom b\<close>
    \<open>stabledom a2 \<subseteq> stabledom b\<close>
    using assms stablerel_impl_subseteq_stabledom
    by fastforce+
  then show ?thesis
    using assms
    apply -
    apply (rule_tac x=\<open>?b1\<close> in exI, rule_tac x=\<open>?b2\<close> in exI)
    apply (intro conjI)
       apply (force simp add: disjoint_dheap_def disjoint_set_dheap_def halve_dheap_iff
        field_All_mult_inverse_iff dom_def stabledom_def dom_dheap_def app_dheap_bounded_permD
        split: option.splits)
      apply (force simp add: dheap_eq_iff halve_dheap_iff dom_dheap_iff app_dheap_bounded_permD
        split: option.splits)
    subgoal
      apply (rule stablerel_subheap, blast)
        apply (force simp add: le_plus)
       apply (simp add: less_eq_dheap_def less_eq_perm_def, force simp add: halve_dheap_def
          stabledom_def dom_dheap_iff not_less app_dheap_bounded_permD min.coboundedI2
          split: option.splits if_splits)
      apply force
      done
    subgoal
      apply (rule stablerel_subheap, blast)
        apply (force simp add: le_plus2)
       apply (simp add: less_eq_dheap_def less_eq_perm_def, force simp add: halve_dheap_def
          stabledom_def dom_dheap_iff not_less app_dheap_bounded_permD min.coboundedI2
          split: option.splits if_splits)
      apply force
      done
    done
qed


(* strongest weaker stable predicate *)
abbreviation swstable_pred_dheap :: \<open>(('a,'b) dheap \<Rightarrow> bool) \<Rightarrow> (('a,'b) dheap \<Rightarrow> bool)\<close> ("\<lfloor> _ \<rfloor>\<^sub>d" 90)
  where
    \<open>\<lfloor> P \<rfloor>\<^sub>d \<equiv> \<lfloor> P \<rfloor>\<^bsub>stablerel\<^esub>\<close>

(* weakest stronger stable predicate *)
abbreviation wsstable_pred_dheap :: \<open>(('a,'b) dheap \<Rightarrow> bool) \<Rightarrow> (('a,'b) dheap \<Rightarrow> bool)\<close> ("\<lceil> _ \<rceil>\<^sub>d" 90)
  where
    \<open>\<lceil> P \<rceil>\<^sub>d \<equiv> \<lceil> P \<rceil>\<^bsub>stablerel\<^esub>\<close>

lemma swstable_pred_dheap_semidistrib:
  \<open>\<lfloor> P \<rfloor>\<^sub>d \<^emph> \<lfloor> Q \<rfloor>\<^sub>d \<le> \<lfloor> P \<^emph> Q \<rfloor>\<^sub>d\<close>
  by (rule swstable_sepconj_semidistrib, simp add: stablerel_additivity_of_update)

lemma wsstable_pred_dheap_semidistrib:
  \<open>\<lceil> P \<^emph> Q \<rceil>\<^sub>d \<le> \<lceil> P \<rceil>\<^sub>d \<^emph> \<lceil> Q \<rceil>\<^sub>d\<close>
  by (rule wsstable_sepconj_semidistrib, simp add: stablerel_additivity_of_update)




end