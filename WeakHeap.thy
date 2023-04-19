theory WeakHeap
  imports Stabilisation
begin

section \<open>(Weak) Permission Heaps\<close>

typedef ('p,'v) pheap =
  \<open>{h::'p \<rightharpoonup> rat \<times> 'v.
    finite (dom h) \<and> (\<forall>p c v. h p = Some (c,v) \<longrightarrow> 0 \<le> c \<and> c \<le> 1)}\<close>
  morphisms app_pheap Abs_pheap
  by (rule exI[where x=Map.empty], force)

lemmas Abs_pheap_inverse' = Abs_pheap_inverse[OF iffD2[OF mem_Collect_eq], OF conjI]

syntax app_pheap :: \<open>('a,'b) pheap \<Rightarrow> 'a \<Rightarrow> (rat \<times> 'b) option\<close> (infix \<open>\<bullet>\<close> 990)

setup_lifting type_definition_pheap

lemma eq_app_pheap_iff:
  \<open>a = app_pheap a' \<longleftrightarrow> a' = Abs_pheap a \<and> finite (dom a) \<and> (\<forall>p c v. a p = Some (c,v) \<longrightarrow> 0 \<le> c \<and> c \<le> 1)\<close>
  \<open>app_pheap a' = a \<longleftrightarrow> a' = Abs_pheap a \<and> finite (dom a) \<and> (\<forall>p c v. a p = Some (c,v) \<longrightarrow> 0 \<le> c \<and> c \<le> 1)\<close>
  by (case_tac a' rule: Abs_pheap_cases, force simp add: Abs_pheap_inverse Abs_pheap_inject)+

lemma eq_Abs_pheap_iff:
  assumes
    \<open>finite (dom a)\<close>
    \<open>\<forall>p c v. a p = Some (c,v) \<longrightarrow> 0 \<le> c \<and> c \<le> 1\<close>
  shows
    \<open>a' = Abs_pheap a \<longleftrightarrow> a = app_pheap a'\<close>
    \<open>Abs_pheap a = a' \<longleftrightarrow> a = app_pheap a'\<close>
  by (force simp add: assms eq_app_pheap_iff)+

lemma pheap_ext:
  fixes a b :: \<open>('a,'b) pheap\<close>
  shows \<open>(\<And>x. a \<bullet> x = b \<bullet> x) \<Longrightarrow> a = b\<close>
  by (force intro: iffD1[OF app_pheap_inject])

lemma pheap_eq_iff:
  fixes a b :: \<open>('a,'b) pheap\<close>
  shows \<open>a = b \<longleftrightarrow> (\<forall>x. a \<bullet> x = b \<bullet> x)\<close>
  using pheap_ext by blast

subsection \<open>Basic pheap operations\<close>

subsubsection \<open> Domain \<close>

lift_definition dom_pheap :: \<open>('a,'b) pheap \<Rightarrow> 'a set\<close> is \<open>dom\<close> .

lemma finite_dom_app_pheap[simp]:
  \<open>finite (dom (app_pheap a))\<close>
  by (metis eq_app_pheap_iff(1))

lemma finite_dom_pheap[simp]:
  \<open>finite (dom_pheap a)\<close>
  by (simp add: dom_pheap.rep_eq)

lemma in_dom_pheap_iff:
  \<open>x \<in> dom_pheap a \<longleftrightarrow> (\<exists>c v. a \<bullet> x = Some (c,v))\<close>
  by (simp add: dom_pheap.rep_eq dom_def)

lemma dom_pheap_iff:
  \<open>dom_pheap a = {x. \<exists>c v. a \<bullet> x = Some (c,v)}\<close>
  by (simp add: dom_pheap.rep_eq dom_def)

subsubsection \<open> Map \<close>

text \<open>change the values of a pheap without changing the domain\<close>

lift_definition map_pheap :: \<open>(rat \<Rightarrow> rat) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('i,'a) pheap \<Rightarrow> ('i,'b) pheap\<close> is
  \<open>\<lambda>fc fv a. \<lambda>x. map_option (map_prod (max 0 \<circ> min 1 \<circ> fc) fv) (a x)\<close>
  by (clarsimp simp add: dom_map_option)

lemma map_app_pheap_eq[simp]:
  \<open>map_pheap fc fv a \<bullet> x = map_option (map_prod (max 0 \<circ> min 1 \<circ> fc) fv) (a \<bullet> x)\<close>
  by (metis map_pheap.rep_eq)

lemma dom_map_pheap_eq[simp]:
  \<open>dom_pheap (map_pheap fc fv a) = dom_pheap a\<close>
  by (simp add: dom_pheap_iff map_pheap.rep_eq)


subsubsection \<open> Intersection-merge \<close>

lift_definition int_merge_pheap
  :: \<open>(rat \<Rightarrow> rat \<Rightarrow> rat) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('i,'a) pheap \<Rightarrow> ('i,'b) pheap \<Rightarrow> ('i,'c) pheap\<close> is
  \<open>\<lambda>fc fv a b. \<lambda>x. case a x of
                    Some (ca, va) \<Rightarrow>
                      (case b x of
                        Some (cb, vb) \<Rightarrow> Some (max 0 (min 1 (fc ca cb)), fv va vb)
                      | None \<Rightarrow> None)
                    | None \<Rightarrow> None\<close>
  apply (rule conjI)
   apply (rule_tac B=\<open>dom fun3\<close> in rev_finite_subset; force split: option.splits)
  apply (force split: option.splits)
  done

lemma int_merge_app_pheap_eq:
  \<open>int_merge_pheap fc fv a b \<bullet> x =
    (case a \<bullet> x of
      Some (ca, va) \<Rightarrow>
        (case b \<bullet> x of
          Some (cb, vb) \<Rightarrow> Some (max 0 (min 1 (fc ca cb)), fv va vb)
        | None \<Rightarrow> None)
      | None \<Rightarrow> None)\<close>
  by (metis int_merge_pheap.rep_eq)

subsubsection \<open> Union-merge \<close>

lift_definition un_merge_pheap
  :: \<open>(rat \<Rightarrow> rat \<Rightarrow> rat) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('i,'a) pheap \<Rightarrow> ('i,'a) pheap \<Rightarrow> ('i,'a) pheap\<close> is
  \<open>\<lambda>fc fv a b. \<lambda>x. case a x of
                    Some (ca, va) \<Rightarrow>
                      (case b x of
                        Some (cb, vb) \<Rightarrow> Some (max 0 (min 1 (fc ca cb)), fv va vb)
                      | None \<Rightarrow> Some (ca, va))
                    | None \<Rightarrow> b x\<close>
  apply (rule conjI)
   apply (rule_tac B=\<open>dom fun3 \<union> dom fun4\<close> in rev_finite_subset; force split: option.splits)
  apply (simp split: option.splits; fail)
  done

lemma un_merge_app_pheap_eq:
  \<open>un_merge_pheap fc fv a b \<bullet> x =
    (case a \<bullet> x of
      Some (ca, va) \<Rightarrow>
        (case b \<bullet> x of
          Some (cb, vb) \<Rightarrow> Some (max 0 (min 1 (fc ca cb)), fv va vb)
        | None \<Rightarrow> Some (ca, va))
      | None \<Rightarrow> b \<bullet> x)\<close>
  by (metis un_merge_pheap.rep_eq)


subsubsection \<open> Sequence \<close>

lift_definition seq_pheap :: \<open>('a,'b) pheap \<Rightarrow> ('a,'b) pheap \<Rightarrow> ('a,'b) pheap\<close> (infixr \<open>\<triangleright>\<close> 110) is
  \<open>\<lambda>a b. \<lambda>x. case a x of Some y \<Rightarrow> Some y | None \<Rightarrow> b x\<close>
  apply (rename_tac a b)
  apply (rule conjI)
   apply (rule_tac B=\<open>dom a \<union> dom b\<close> in rev_finite_subset; force split: option.splits)
  apply (simp split: option.splits; fail)
  done

lemma seq_app_pheap_eq[simp]:
  \<open>(a \<triangleright> b) \<bullet> x = (case a \<bullet> x of Some y \<Rightarrow> Some y | None \<Rightarrow> b \<bullet> x)\<close>
  by (simp add: seq_pheap.rep_eq)

lemma dom_seq_pheap_eq[simp]: \<open>dom_pheap (a \<triangleright> b) = dom_pheap a \<union> dom_pheap b\<close>
  by (simp add: dom_pheap.rep_eq seq_pheap.rep_eq set_eq_iff dom_def split: option.splits)

subsubsection \<open> Restriction \<close>

lift_definition restrict_pheap :: \<open>('a,'b) pheap \<Rightarrow> 'a set \<Rightarrow> ('a,'b) pheap\<close>
  (infixr \<open>|`\<^sub>p\<close> 110) is \<open>(|`)\<close>
  by (clarsimp simp add: restrict_map_def dom_def)

lemma restrict_app_pheap_eq[simp]:
  \<open>(a |`\<^sub>p A) \<bullet> x = (if x \<in> A then a \<bullet> x else None)\<close>
  by (simp add: restrict_pheap.rep_eq)

lemma dom_restrict_pheap_eq[simp]: \<open>dom_pheap (a |`\<^sub>p A) = dom_pheap a \<inter> A\<close>
  by (simp add: dom_pheap.rep_eq seq_pheap.rep_eq set_eq_iff dom_def split: option.splits)

lemma restrict_dom_subset_eq:
  \<open>dom_pheap a \<subseteq> A \<Longrightarrow> a |`\<^sub>p A = a\<close>
  by (force simp add: dom_pheap.rep_eq pheap_eq_iff subset_eq set_eq_iff dom_def)

lemma restrict_sequence_right:
  \<open>(a \<triangleright> b) = (a \<triangleright> b |`\<^sub>p (- dom_pheap a))\<close>
  by (simp add: pheap_eq_iff dom_pheap_iff split: option.splits)

section \<open>Operations on permissions\<close>

definition plus_perm :: \<open>(rat \<times> 'a) option \<Rightarrow> (rat \<times> 'a) option \<Rightarrow> (rat \<times> 'a) option\<close>
  (infixl \<open>\<oplus>\<^sub>p\<close> 65) where
  \<open>plus_perm a b \<equiv> case b of
                    Some (c2, v2) \<Rightarrow>
                      (case a of
                        Some (c1, v1) \<Rightarrow> Some (min (c1+c2) 1, v1)
                        | None \<Rightarrow> Some (c2, v2))
                    | None \<Rightarrow> a\<close>

lemma finite_dom_add[simp]:
  \<open>finite (dom (\<lambda>x. a x \<oplus>\<^sub>p b x)) \<longleftrightarrow> finite (dom a) \<and> finite (dom b)\<close>
  by (simp add: dom_def plus_perm_def imp_conv_disj del: imp_conv_disj[symmetric]
      split: option.splits, blast)

lemma plus_perm_simps[simp]:
  \<open>a \<oplus>\<^sub>p None = a\<close>
  \<open>None \<oplus>\<^sub>p b = b\<close>
  \<open>Some (c1, v1) \<oplus>\<^sub>p Some (c2, v2) = Some (min (c1 + c2) 1, v1)\<close>
  by (force simp add: plus_perm_def split: option.splits)+

lemma plus_perm_eq_None_iff[simp]:
  \<open>a \<oplus>\<^sub>p b = None \<longleftrightarrow> a = None \<and> b = None\<close>
  by (force simp add: plus_perm_def split: option.splits)

lemma plus_perm_eq_Some_iff:
  \<open>\<And>a c2 v2 c.
    a \<oplus>\<^sub>p Some (c2, v2) = c \<longleftrightarrow>
      (case a of None \<Rightarrow> c = Some (c2, v2) | Some (c1, v1) \<Rightarrow> c = Some (min (c1 + c2) 1, v1))\<close>
  \<open>\<And>c1 v1 b c.
    Some (c1, v1) \<oplus>\<^sub>p b  = c \<longleftrightarrow>
      (case b of None \<Rightarrow> c = Some (c1, v1) | Some (c2, v2) \<Rightarrow> c = Some (min (c1 + c2) 1, v1))\<close>
  \<open>\<And>a b c v.
    (a \<oplus>\<^sub>p b) = Some (c, v) \<longleftrightarrow>
      (b = None \<longrightarrow> a = Some (c, v)) \<and>
      (a = None \<longrightarrow> b = Some (c, v)) \<and>
      (\<forall>c1 v1. a = Some (c1, v1) \<longrightarrow>
        (\<forall>c2 v2. b = Some (c2, v2) \<longrightarrow>
          min (c1 + c2) 1 = c \<and> v = v1))\<close>
  by (force simp add: plus_perm_def split: option.splits)+

lemmas plus_perm_eq_Some_iff_rev = HOL.trans[OF HOL.eq_commute plus_perm_eq_Some_iff(3)]


definition minus_perm :: \<open>(rat \<times> 'a) option \<Rightarrow> (rat \<times> 'a) option \<Rightarrow> (rat \<times> 'a) option\<close>
  (infixl \<open>\<ominus>\<^sub>p\<close> 65) where
  \<open>minus_perm a b \<equiv> case a of
                      Some (c1, v1) \<Rightarrow>
                        (case b of
                          Some (c2, v2) \<Rightarrow> if v1 = v2 then Some (max (c2 - c1) 0, v1) else None
                        | None \<Rightarrow> Some (c1, v1))
                    | None \<Rightarrow> None\<close>

lemma finite_dom_minus[intro]:
  \<open>finite (dom a) \<Longrightarrow> finite (dom (\<lambda>x. a x \<ominus>\<^sub>p b x))\<close>
  by (simp add: dom_def minus_perm_def Collect_conj_eq split: option.splits)

lemma minus_perm_None[simp]:
  \<open>a \<ominus>\<^sub>p None = a\<close>
  \<open>None \<ominus>\<^sub>p b = None\<close>
  by (simp add: minus_perm_def split: option.splits)+

lemma minus_perm_Some_iff:
  \<open>Some (ca, va) \<ominus>\<^sub>p b = x \<longleftrightarrow>
      b = None \<and> x = Some (ca, va) \<or>
      (\<exists>cb. b = Some (cb, va) \<and> x = Some (max 0 (cb - ca), va)) \<or>
      (\<exists>cb vb. vb \<noteq> va \<and> b = Some (cb, vb) \<and> x = None)\<close>
  \<open>a \<ominus>\<^sub>p Some (cb, vb) = x \<longleftrightarrow>
      a = None \<and> x = None \<or>
      (\<exists>ca. a = Some (ca, vb) \<and> x = Some (max 0 (cb - ca), vb)) \<or>
      (\<exists>ca va. va \<noteq> vb \<and> a = Some (ca, va) \<and> x = None)\<close>
  \<open>a \<ominus>\<^sub>p b = Some (c, v) \<longleftrightarrow>
      a = Some (c, v) \<and> b = None \<or>
      (\<exists>c1. a = Some (c1, v) \<and> (\<exists>c2. b = Some (c2, v) \<and> c = max (c2 - c1) 0))\<close>
  by (force simp add: minus_perm_def split: option.splits)+


lemma minus_perm_eq_None[simp]:
  \<open>a \<ominus>\<^sub>p b = None \<longleftrightarrow>
    (a = None \<or> (\<exists>c1 v1. a = Some (c1, v1) \<and> (\<exists>c2 v2. b = Some (c2, v2) \<and> v1 \<noteq> v2)))\<close>
  by (simp add: minus_perm_def max_def split: option.splits)


lemma
  fixes c1 c2 :: \<open>'a :: linordered_idom\<close>
  shows
    \<open>(c2 = min (c1 + max (c1 - c2) 0) m) = (c2 = c1 \<and> c2 \<le> m \<or> c2 \<le> c1 \<and> c2 = m)\<close>
  by (fastforce simp add: min_le_iff_disj le_max_iff_disj)

lemma perm_eq_plus_minus_iff:
  \<open>b = a \<oplus>\<^sub>p (b \<ominus>\<^sub>p a) \<longleftrightarrow>
    a = None \<or>
      b = a \<and> (\<exists>c v. a = Some (c, v) \<and> c \<le> 1) \<or>
      (\<exists>v. b = Some (1, v) \<and> (\<exists>c1\<ge>1. a = Some (c1, v)))\<close>
  by (force simp add: plus_perm_def minus_perm_def split: option.splits)

lemma Abs_app_pheap:
  \<open>finite (dom m) \<Longrightarrow> (\<And>p c v. m p = Some (c, v) \<Longrightarrow> 0 \<le> c \<and> c \<le> 1) \<Longrightarrow> (Abs_pheap m) \<bullet> x = m x\<close>
  using Abs_pheap_inverse
  by fastforce

lemma Abs_pheap_inverse_app[simp]:
  \<open>Abs_pheap (app_pheap h) \<bullet> x = h \<bullet> x\<close>
  by (simp add: app_pheap_inverse)

lemma app_pheap_bounded_permD:
  \<open>a \<bullet> x = Some (c, v) \<Longrightarrow> 0 \<le> c\<close>
  \<open>a \<bullet> x = Some (c, v) \<Longrightarrow> c \<le> 1\<close>
  \<open>a \<bullet> x = Some (c, v) \<Longrightarrow> c \<le> 0 \<longleftrightarrow> c = 0\<close>
  \<open>a \<bullet> x = Some (c, v) \<Longrightarrow> 1 \<le> c \<longleftrightarrow> c = 1\<close>
  by (meson eq_app_pheap_iff nle_le)+

lemma ex_app_pheap_iff:
  \<open>(\<exists>a. P (app_pheap a)) \<longleftrightarrow>
      (\<exists>m. finite (dom m) \<and> (P m \<and> (\<forall>x c v. m x = Some (c, v) \<longrightarrow> 0 \<le> c \<and> c \<le> 1)))\<close>
  apply (rule iffI)
   apply (meson app_pheap_bounded_permD finite_dom_app_pheap)
  apply (metis eq_Abs_pheap_iff(1))
  done

lemma ex_pheap_by_parts:
  \<open>(\<exists>a. \<forall>x. P x (a \<bullet> x)) \<longleftrightarrow>
    (finite {x. (\<exists>c v. P x (Some (c, v)) \<and> 0 \<le> c \<and> c \<le> 1) \<and> \<not> P x None} \<and>
      (\<forall>x. P x None \<or> (\<exists>c v. P x (Some (c,v)) \<and> 0 \<le> c \<and> c \<le> 1)))\<close>
  apply (subst ex_app_pheap_iff)
  apply (simp add: all_conj_distrib[symmetric])
  apply (subst finite_map_choice_iff)
  apply (simp add: split_option_ex)
  done


subsection \<open> Disjointness \<close>

definition disjoint_set_pheap :: \<open>('a,'b) pheap \<Rightarrow> 'a set \<Rightarrow> ('a,'b) pheap \<Rightarrow> bool\<close>
  ("_ ##\<^bsub>_\<^esub> _" [61,0,61] 60) where
  \<open>a ##\<^bsub>A\<^esub> b \<equiv> \<forall>x\<in>A.
    \<forall>c1 v1. a \<bullet> x = Some (c1, v1) \<longrightarrow>
      (\<forall>c2 v2. b \<bullet> x = Some (c2, v2) \<longrightarrow> c1 + c2 \<le> 1 \<and> v1 = v2)\<close>

lemma disjoint_set_un_eq[simp]:
  \<open>a ##\<^bsub>A \<union> B\<^esub> b \<longleftrightarrow> a ##\<^bsub>A\<^esub> b \<and> a ##\<^bsub>B\<^esub> b\<close>
  by (simp add: disjoint_set_pheap_def Ball_def, blast)

lemma disjoint_set_antimono_pheap:
  \<open>Y \<subseteq> X \<Longrightarrow> a ##\<^bsub>X\<^esub> b \<Longrightarrow> a ##\<^bsub>Y\<^esub> b\<close>
  by (metis Un_absorb2 disjoint_set_un_eq)

lemma disjoint_seq[simp]:
  \<open>a1 \<triangleright> a2 ##\<^bsub>A\<^esub> b \<longleftrightarrow> a1 ##\<^bsub>A\<^esub> b \<and> a2 ##\<^bsub>A - dom_pheap a1\<^esub> b\<close>
  \<open>b ##\<^bsub>A\<^esub> a1 \<triangleright> a2 \<longleftrightarrow> b ##\<^bsub>A\<^esub> a1 \<and> b ##\<^bsub>A - dom_pheap a1\<^esub> a2\<close>
  by (force simp add: disjoint_set_pheap_def dom_pheap_iff Ball_def split: option.splits)+

lemma disjoint_map_iff:
  assumes
    \<open>\<And>x c v. x \<in> A \<Longrightarrow> a \<bullet> x = Some (c,v) \<Longrightarrow> g v = v\<close>
    \<open>\<And>x ca va cb vb.
        x \<in> A \<Longrightarrow> a \<bullet> x = Some (ca,va) \<Longrightarrow> b \<bullet> x = Some (cb, vb) \<Longrightarrow> 
        ca + cb \<le> 1 \<longleftrightarrow> max 0 (min 1 (f ca)) + cb \<le> 1\<close>
  shows
    \<open>map_pheap f g a ##\<^bsub>A\<^esub> b \<longleftrightarrow> a ##\<^bsub>A\<^esub> b\<close>
  using assms
  apply (clarsimp simp add: disjoint_set_pheap_def Ball_def split: option.splits)
  apply (intro iffI allI impI)
   apply (drule spec, drule mp, blast)
   apply (drule spec, drule spec, drule mp, blast)
   apply (drule spec, drule spec, drule mp, blast)
   apply force
  apply (drule spec, drule mp, blast)
  apply clarsimp
  done

lemma disjoint_map_val_id_iff:
  assumes
    \<open>\<And>x ca va cb vb.
        x \<in> A \<Longrightarrow> a \<bullet> x = Some (ca,va) \<Longrightarrow> b \<bullet> x = Some (cb, vb) \<Longrightarrow> 
        ca + cb \<le> 1 \<longleftrightarrow> max 0 (min 1 (f ca)) + cb \<le> 1\<close>
  shows
    \<open>map_pheap f id a ##\<^bsub>A\<^esub> b \<longleftrightarrow> a ##\<^bsub>A\<^esub> b\<close>
  using assms
  by (simp add: disjoint_map_iff)


text \<open>Define disjointness on pheaps\<close>
instantiation pheap :: (type,type) disjoint
begin

definition disjoint_pheap :: \<open>('a,'b) pheap \<Rightarrow> ('a,'b) pheap \<Rightarrow> bool\<close> where
  \<open>disjoint_pheap a b \<equiv> a ##\<^bsub>UNIV\<^esub> b\<close>

instance by standard

end

lemmas disjoint_pheap_def' = disjoint_pheap_def disjoint_set_pheap_def

lemma self_disjoint_pheap:
  \<open>a ##\<^bsub>X\<^esub> a \<longleftrightarrow> (\<forall>x\<in>X. \<forall>c v. a \<bullet> x = Some (c, v) \<longrightarrow> c \<le> 1 /2)\<close>
  by (simp add: disjoint_set_pheap_def Ball_def mult.commute)

subsection \<open> Addition \<close>

text \<open>Define plus on pheaps\<close>
instantiation pheap :: (type, type) plus
begin

lift_definition plus_pheap :: \<open>('a,'b) pheap \<Rightarrow> ('a,'b) pheap \<Rightarrow> ('a,'b) pheap\<close> is
  \<open>\<lambda>ma mb. \<lambda>x. ma x \<oplus>\<^sub>p mb x\<close>
  apply (rename_tac ma mb)
  apply (simp add: dom_def plus_perm_def split: option.splits)
  apply (rule conjI)
   apply (rule_tac B=\<open>dom ma \<union> dom mb\<close> in rev_finite_subset; force simp add: dom_def)
  apply (force intro: add_nonneg_nonneg)
  done

instance by standard

end

lemma Rep_add_in_bounds:
  assumes \<open>app_pheap a p \<oplus>\<^sub>p app_pheap b p = Some (c, v)\<close>
  shows \<open>c \<le> 1\<close> \<open>0 \<le> c\<close>
  using assms
  by (simp add: dom_def plus_pheap_def plus_perm_def
      app_pheap_bounded_permD eq_commute[of \<open>min _ _\<close>] split: option.splits prod.splits)+

lemma app_plus_pheap[simp]:
  \<open>(a + b) \<bullet> x = a \<bullet> x \<oplus>\<^sub>p b \<bullet> x\<close>
  apply (simp add: disjoint_pheap_def' plus_pheap_def)
  apply (subst Abs_pheap_inverse; force simp add: Rep_add_in_bounds)
  done

lemma restrict_pheap_add_eq[simp]:
  \<open>(a + b) |`\<^sub>p A = a |`\<^sub>p A + b |`\<^sub>p A\<close>
  by (simp add: pheap_eq_iff)

lemma dom_plus_pheap_eq[simp]: \<open>dom_pheap (h1 + h2) = dom_pheap h1 \<union> dom_pheap h2\<close>
  by (simp add: dom_pheap.rep_eq plus_perm_def dom_def set_eq_iff split: option.splits)


text \<open>Define minus on pheaps\<close>
instantiation pheap :: (type, type) minus
begin

lift_definition minus_pheap :: \<open>('a,'b) pheap \<Rightarrow> ('a,'b) pheap \<Rightarrow> ('a,'b) pheap\<close> is
  \<open>\<lambda>ma mb. \<lambda>x. ma x \<ominus>\<^sub>p mb x\<close>
  by (force simp add: dom_def minus_perm_def split: option.splits)

instance by standard

end

lemma Rep_minus_in_bounds:
  assumes \<open>app_pheap a p \<ominus>\<^sub>p app_pheap b p = Some (c, v)\<close>
  shows \<open>c \<le> 1\<close> \<open>0 \<le> c\<close>
  using assms
  by (clarsimp simp add: dom_def minus_pheap_def minus_perm_def app_pheap_bounded_permD
      add_increasing2 diff_le_eq split: option.splits prod.splits if_splits)+

lemma minus_plus_pheap[simp]:
  \<open>(a - b) \<bullet> x = a \<bullet> x \<ominus>\<^sub>p b \<bullet> x\<close>
  apply (simp add: disjoint_pheap_def' minus_pheap_def)
  apply (subst Abs_pheap_inverse; force simp add: Rep_minus_in_bounds)
  done

lemma pheap_eq_plus_minus_iff:
  fixes a b :: \<open>('p,'v) pheap\<close>
  shows \<open>b = a + (b - a) \<longleftrightarrow> (\<forall>x. a \<bullet> x = None \<or> a \<bullet> x = b \<bullet> x)\<close>
  by (simp add: pheap_eq_iff perm_eq_plus_minus_iff,
      metis app_pheap_bounded_permD(2) nle_le not_Some_prod_eq)


definition less_eq_perm :: \<open>(rat \<times> 'a) option \<Rightarrow> (rat \<times> 'a) option \<Rightarrow> bool\<close>
  (infix \<open>\<subseteq>\<^sub>p\<close> 100) where
  \<open>a \<subseteq>\<^sub>p b \<equiv> \<forall>ca v. a = Some (ca, v) \<longrightarrow> (\<exists>cb\<ge>ca. b = Some (cb, v))\<close>

lemma less_eq_perm_refl[iff]:
  \<open>a \<subseteq>\<^sub>p a\<close>
  by (simp add: less_eq_perm_def)

lemma less_eq_perm_trans:
  \<open>a \<subseteq>\<^sub>p b \<Longrightarrow> b \<subseteq>\<^sub>p c \<Longrightarrow> a \<subseteq>\<^sub>p c\<close>
  by (force simp add: less_eq_perm_def)

lemma less_eq_perm_NoneL[iff]:
  \<open>None \<subseteq>\<^sub>p a\<close>
  by (force simp add: less_eq_perm_def)

lemma less_eq_perm_NoneR[iff]:
  \<open>a \<subseteq>\<^sub>p None \<longleftrightarrow> a = None\<close>
  by (force simp add: less_eq_perm_def)


text \<open>Define less than and less than or equal on pheaps\<close>
instantiation pheap :: (type, type) preorder
begin

definition less_eq_pheap :: \<open>('a,'b) pheap \<Rightarrow> ('a,'b) pheap \<Rightarrow> bool\<close> where
  \<open>less_eq_pheap ma mb \<equiv> \<forall>x. ma \<bullet> x \<subseteq>\<^sub>p mb \<bullet> x\<close>

definition less_pheap :: \<open>('a,'b) pheap \<Rightarrow> ('a,'b) pheap \<Rightarrow> bool\<close> where
  \<open>less_pheap a b \<equiv> a \<le> b \<and> \<not>(b \<le> a)\<close>

instance
  by standard
    (simp add: less_pheap_def less_eq_pheap_def; blast dest: less_eq_perm_trans)+

end


definition compl_perm :: \<open>(rat \<times> 'a) option \<Rightarrow> (rat \<times> 'a) option \<Rightarrow> (rat \<times> 'a) option\<close>
  (infixl \<open>\<oslash>\<^sub>p\<close> 65) where
  \<open>compl_perm a b \<equiv> case a of
                      Some (c1, v1) \<Rightarrow>
                        (case b of
                          Some (c2, v2) \<Rightarrow>
                            if c2 = c1
                            then None
                            else Some (c2 - c1, v2)
                        | None \<Rightarrow> Some (c1, v1))
                    | None \<Rightarrow> b\<close>

lemma compl_pheap_eq[simp]:
  \<open>None \<oslash>\<^sub>p b = b\<close>
  \<open>a \<oslash>\<^sub>p None = a\<close>
  \<open>Some (c, v1) \<oslash>\<^sub>p Some (c, v2) = None\<close>
  \<open>c1 \<noteq> c2 \<Longrightarrow> Some (c1, v1) \<oslash>\<^sub>p Some (c2, v2) = Some (c2 - c1, v2)\<close>
  by (force simp add: compl_perm_def split: option.splits)+


lemma subheap_plus_compl_pheap_inverse:
  \<open>a \<bullet> x \<subseteq>\<^sub>p b \<bullet> x \<Longrightarrow> (a \<bullet> x \<oplus>\<^sub>p (b \<bullet> x \<oslash>\<^sub>p a \<bullet> x)) \<subseteq>\<^sub>p b \<bullet> x\<close>
  apply (clarsimp simp add: plus_perm_def compl_perm_def less_eq_perm_def split: option.splits)
  apply (intro conjI impI allI)
     apply force
    apply force
   apply (drule_tac spec, drule_tac spec, drule_tac mp, blast)
  apply clarsimp
  done

lemma app_Abs_compl_pheap[simp]:
  \<open>\<forall>x ca v. app_pheap a x = Some (ca, v) \<longrightarrow> (\<exists>cb\<ge>ca. app_pheap b x = Some (cb, v)) \<Longrightarrow>
    Abs_pheap (\<lambda>x. a \<bullet> x \<oslash>\<^sub>p b \<bullet> x) \<bullet> x = a \<bullet> x \<oslash>\<^sub>p b \<bullet> x\<close>
  apply (subst Abs_pheap_inverse)
   apply clarsimp
   apply (rule conjI)
    apply (rule rev_finite_subset[of \<open>dom_pheap b\<close>];
      force simp add: compl_perm_def dom_pheap_def less_eq_perm_def split: option.splits)
   apply (clarsimp simp add: compl_perm_def dom_pheap_def less_eq_perm_def split: option.splits)
   apply (intro conjI allI)
     apply (force simp add: app_pheap_bounded_permD)
    apply (force simp add: app_pheap_bounded_permD)
   apply (metis app_pheap_bounded_permD(1,2) cancel_comm_monoid_add_class.diff_zero diff_mono
      option.inject prod.inject)
  apply (force simp add: app_pheap_bounded_permD)
  done


instantiation pheap :: (type,type) seplogic
begin

lift_definition zero_pheap :: \<open>('a,'b) pheap\<close> is \<open>Map.empty\<close>
  by simp

lemma app_zero_pheap[simp]:
  \<open>0 \<bullet> x = None\<close>
  by (simp add: zero_pheap.rep_eq)

lift_definition bot_pheap :: \<open>('a,'b) pheap\<close> is \<open>Map.empty\<close>
  by simp

lemma app_bot_pheap[simp]:
  \<open>\<bottom> \<bullet> x = None\<close>
  by (simp add: bot_pheap.rep_eq)

lemma bot_pheap_eq_zero_pheap:
  \<open>(\<bottom> :: ('a,'b) pheap) = 0\<close>
  by (simp add: zero_pheap.abs_eq bot_pheap.abs_eq)

lemma le_iff_sepadd_helper:
  fixes a b :: \<open>('a,'b) pheap\<close>
  shows \<open>(a \<le> b) = (\<exists>c. a ## c \<and> b = a + c)\<close>
  apply (rule iffI)
   apply (clarsimp simp add: pheap_eq_iff disjoint_pheap_def' less_eq_pheap_def
      less_eq_perm_def split: option.splits)
   apply (rule_tac x=\<open>Abs_pheap (\<lambda>x. a \<bullet> x \<oslash>\<^sub>p b \<bullet> x)\<close> in exI)
   apply (simp, force simp add: compl_perm_def plus_perm_def app_pheap_bounded_permD
      split: option.splits)
  apply (force simp add: less_eq_pheap_def less_eq_perm_def plus_perm_def app_pheap_bounded_permD
      split: option.splits)
  done

instance
  apply standard
           apply (clarsimp simp add: less_eq_pheap_def less_eq_perm_def pheap_eq_iff)
           apply (rename_tac a b x)
           apply (case_tac \<open>app_pheap a x\<close>; case_tac \<open>app_pheap b x\<close>; force)
          apply (simp add: less_eq_pheap_def; fail)
         apply (force simp add: disjoint_pheap_def')
        apply (force simp add: disjoint_pheap_def')
  subgoal
    apply (clarsimp simp add: disjoint_pheap_def' plus_perm_def split: option.splits)
    apply (drule_tac x=x in spec)+
    apply (meson add_le_cancel_left app_pheap_bounded_permD(1) le_add_same_cancel1 order_trans)
    done
  subgoal
    apply (clarsimp simp add: disjoint_pheap_def')
    apply (drule_tac x=x in spec)+
    apply (simp add: plus_perm_def split: option.splits prod.splits)
    done
     apply (simp add: le_iff_sepadd_helper; fail)
  subgoal
    apply (clarsimp simp add: pheap_eq_iff plus_perm_def split: option.splits)
    apply (simp add: add.commute disjoint_pheap_def')
    done
  subgoal
    apply (clarsimp simp add: disjoint_pheap_def' pheap_eq_iff)
    apply (force simp add: plus_perm_def eq_iff min_le_iff_disj split: option.splits)
    done
  apply (simp add: pheap_eq_iff; fail)
  done

end


lemma disjoint_restrict_pheap_iff[simp]:
  \<open>a |`\<^sub>p A ##\<^bsub>X\<^esub> b \<longleftrightarrow> a ##\<^bsub>X \<inter> A\<^esub> b\<close>
  \<open>a ##\<^bsub>X\<^esub> b |`\<^sub>p B \<longleftrightarrow> a ##\<^bsub>X \<inter> B\<^esub> b\<close>
  by (force simp add: disjoint_set_pheap_def Ball_def)+


section \<open> The stable and zero domains \<close>

definition stabledom :: \<open>('a,'b) pheap \<Rightarrow> 'a set\<close> where
  \<open>stabledom a \<equiv> {x. \<exists>c v. a \<bullet> x = Some (c,v) \<and> c > 0}\<close>

definition zerodom :: \<open>('a,'b) pheap \<Rightarrow> 'a set\<close> where
  \<open>zerodom a \<equiv> {x. \<exists>c v. a \<bullet> x = Some (c,v) \<and> c = 0}\<close>

lemma dom_pheap_sep:
  \<open>dom_pheap a = stabledom a \<union> zerodom a\<close>
  by (fastforce simp add: dom_pheap_def stabledom_def zerodom_def dom_def set_eq_iff
      dest: app_pheap_bounded_permD(1))

lemma stabledom_subseteq_dom_pheap:
  \<open>stabledom a \<subseteq> dom_pheap a\<close>
  by (simp add: dom_pheap_sep)

subsection \<open>stabledom simps\<close>

lemma restrict_stabledom_eq[simp]:
  \<open>stabledom (a |`\<^sub>p A) = stabledom a \<inter> A\<close>
  by (simp add: stabledom_def set_eq_iff)

lemma seq_stabledom_eq[simp]:
  \<open>stabledom (a \<triangleright> b) = stabledom a \<union> (stabledom b - zerodom a)\<close>
  by (fastforce dest: app_pheap_bounded_permD(1)
      simp add: stabledom_def set_eq_iff zerodom_def split: option.splits)

lemma stabledom_plus[simp]:
  \<open>stabledom (a + b) = stabledom a \<union> stabledom b\<close>
  apply (clarsimp simp add: stabledom_def set_eq_iff plus_perm_eq_Some_iff)
  apply (case_tac \<open>app_pheap a x\<close>)
   apply force
  apply (case_tac \<open>app_pheap b x\<close>)
   apply force
  apply (simp, fastforce dest: app_pheap_bounded_permD(1))
  done

lemma map_stabledom_eq:
  \<open>\<forall>x. fc x > 0 \<longleftrightarrow> x > 0 \<Longrightarrow> stabledom (map_pheap fc fv a) = stabledom a\<close>
  by (force simp add: stabledom_def set_eq_iff split: option.splits)

lemma map_stabledom_permid_eq[simp]:
  \<open>stabledom (map_pheap id fv a) = stabledom a\<close>
  by (force simp add: map_stabledom_eq)

lemma map_stabledom_perm_mult_eq[simp]:
  \<open>k > 0 \<Longrightarrow> stabledom (map_pheap (\<lambda>x. x * k) fv a) = stabledom a\<close>
  by (simp add: map_stabledom_eq zero_less_mult_iff)

lemma map_stabledom_perm_frac_eq[simp]:
  \<open>k > 0 \<Longrightarrow> stabledom (map_pheap (\<lambda>x. x / k) fv a) = stabledom a\<close>
  by (simp add: map_stabledom_eq zero_less_divide_iff)

subsection \<open>zerodom simps\<close>

lemma restrict_zerodom_eq[simp]:
  \<open>zerodom (a |`\<^sub>p A) = zerodom a \<inter> A\<close>
  by (simp add: zerodom_def set_eq_iff)

lemma seq_zerodom_eq[simp]:
  \<open>zerodom (a \<triangleright> b) = zerodom a \<union> (zerodom b - stabledom a)\<close>
    by (fastforce dest: app_pheap_bounded_permD(1)
      simp add: stabledom_def set_eq_iff zerodom_def split: option.splits)

lemma map_zerodom_eq:
  \<open>\<forall>x. fc x > 0 \<longleftrightarrow> x > 0 \<Longrightarrow> zerodom (map_pheap fc fv a) = zerodom a\<close>
  by (clarsimp simp add: zerodom_def set_eq_iff max_eq_k_iff min_le_iff_disj min_eq_k_iff,
      metis app_pheap_bounded_permD(1) less_eq_rat_def linorder_not_less)

lemma map_zerodom_permid_eq[simp]:
  \<open>zerodom (map_pheap id fv a) = zerodom a\<close>
  by (force simp add: map_zerodom_eq)

lemma map_zerodom_perm_mult_eq[simp]:
  \<open>k > 0 \<Longrightarrow> zerodom (map_pheap (\<lambda>x. x * k) fv a) = zerodom a\<close>
  by (simp add: map_zerodom_eq zero_less_mult_iff)

lemma map_zerodom_perm_frac_eq[simp]:
  \<open>k > 0 \<Longrightarrow> zerodom (map_pheap (\<lambda>x. x / k) fv a) = zerodom a\<close>
  by (simp add: map_zerodom_eq zero_less_divide_iff)

subsection \<open> Halve permissions in a set \<close>

text \<open>Halve the permissions in a given set\<close>
definition halve_pheap :: \<open>('a,'b) pheap \<Rightarrow> 'a set \<Rightarrow> ('a,'b) pheap\<close> where
  \<open>halve_pheap a A \<equiv> map_pheap (\<lambda>c. c/2) id (a |`\<^sub>p A) \<triangleright> a\<close>

lemma halve_pheap_iff:
  \<open>halve_pheap a A \<bullet> x =
    (case a \<bullet> x of
        None \<Rightarrow> None
      | Some (c,v) \<Rightarrow>
          if x \<in> A
          then Some (c/2,v)
          else Some (c,v))\<close>
  by (clarsimp split: option.splits
      simp add: halve_pheap_def comp_def max_mult_distrib_right min_mult_distrib_right
      app_pheap_bounded_permD(1) app_pheap_bounded_permD(2)[THEN order.trans, THEN min_absorb2])

lemma halve_pheap_app_eq:
  \<open>halve_pheap a A \<bullet> x = (if x \<in> A then map_pheap (\<lambda>x. x / 2) id a \<bullet> x else a \<bullet> x)\<close>
  by (simp add: halve_pheap_def split: option.splits)

lemma halve_pheap_subheap:
  \<open>halve_pheap a A \<le> a\<close>
  by (force simp add: less_eq_pheap_def less_eq_perm_def halve_pheap_iff split: option.splits
      dest: app_pheap_bounded_permD(1))

lemma stabledom_halve_pheap_eq[simp]:
  \<open>stabledom (halve_pheap a A) = stabledom a\<close>
  by (force simp add: halve_pheap_def dom_pheap_sep)


section \<open> Stable rely-relation \<close>

definition stablerel :: \<open>('a,'b) pheap \<Rightarrow> ('a,'b) pheap \<Rightarrow> bool\<close> where
  \<open>stablerel a b \<equiv> \<forall>x v.
    (\<exists>ca. a \<bullet> x = Some (ca,v) \<and> ca > 0) \<longrightarrow> (\<exists>cb. b \<bullet> x = Some (cb,v) \<and> cb > 0)\<close>

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
       apply (simp add: add_pos_nonneg app_pheap_bounded_permD(1); fail)
      apply (force simp add: disjoint_pheap_def')
     apply (simp add: add_nonneg_pos app_pheap_bounded_permD(1); fail)
    apply (force simp add: disjoint_pheap_def')
   apply (force simp add: disjoint_pheap_def')
  apply (metis add.commute add_nonneg_pos app_pheap_bounded_permD(1) order_less_le)
  done

lemma stablerel_subheap:
  \<open>stablerel a b \<Longrightarrow> a' \<le> a \<Longrightarrow> b' \<le> b \<Longrightarrow> stabledom a' \<subseteq> stabledom b' \<Longrightarrow> stablerel a' b'\<close>
  apply (clarsimp simp add: stablerel_def stabledom_def le_iff_sepadd plus_perm_eq_Some_iff
      set_eq_iff)
  apply (rename_tac a'' b'' x va' ca')
  apply (drule_tac x=x in spec)+
  apply (case_tac \<open>a'' \<bullet> x\<close>; case_tac \<open>b'' \<bullet> x\<close>)
     apply (force simp add: add_pos_nonneg app_pheap_bounded_permD)+
  done

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
  let ?bnew = \<open>dom_pheap b - stabledom a1 - stabledom a2\<close>
  let ?b1=\<open>halve_pheap (b |`\<^sub>p (stabledom a1 \<union> ?bnew)) (stabledom a2 \<union> ?bnew)\<close>
  let ?b2=\<open>halve_pheap (b |`\<^sub>p (stabledom a2 \<union> ?bnew)) (stabledom a1 \<union> ?bnew)\<close>

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
       apply (force simp add: disjoint_pheap_def disjoint_set_pheap_def halve_pheap_iff
        field_All_mult_inverse_iff dom_def stabledom_def dom_pheap_def app_pheap_bounded_permD
        split: option.splits)
      apply (force simp add: pheap_eq_iff halve_pheap_iff dom_pheap_iff app_pheap_bounded_permD
        split: option.splits)
    subgoal
      apply (rule stablerel_subheap, blast)
        apply (force simp add: le_plus)
       apply (simp add: less_eq_pheap_def less_eq_perm_def, force simp add: halve_pheap_def
          stabledom_def dom_pheap_iff not_less app_pheap_bounded_permD min.coboundedI2
          split: option.splits if_splits)
      apply force
      done
    subgoal
      apply (rule stablerel_subheap, blast)
        apply (force simp add: le_plus2)
       apply (simp add: less_eq_pheap_def less_eq_perm_def, force simp add: halve_pheap_def
          stabledom_def dom_pheap_iff not_less app_pheap_bounded_permD min.coboundedI2
          split: option.splits if_splits)
      apply force
      done
    done
qed


(* strongest weaker stable predicate *)
abbreviation swstable_pred_pheap :: \<open>(('a,'b) pheap \<Rightarrow> bool) \<Rightarrow> (('a,'b) pheap \<Rightarrow> bool)\<close> ("\<lfloor> _ \<rfloor>\<^sub>p" 90)
  where
    \<open>\<lfloor> P \<rfloor>\<^sub>p \<equiv> \<lfloor> P \<rfloor>\<^bsub>stablerel\<^esub>\<close>

(* weakest stronger stable predicate *)
abbreviation wsstable_pred_pheap :: \<open>(('a,'b) pheap \<Rightarrow> bool) \<Rightarrow> (('a,'b) pheap \<Rightarrow> bool)\<close> ("\<lceil> _ \<rceil>\<^sub>p" 90)
  where
    \<open>\<lceil> P \<rceil>\<^sub>p \<equiv> \<lceil> P \<rceil>\<^bsub>stablerel\<^esub>\<close>

lemma swstable_pred_pheap_semidistrib:
  \<open>\<lfloor> P \<rfloor>\<^sub>p \<^emph> \<lfloor> Q \<rfloor>\<^sub>p \<le> \<lfloor> P \<^emph> Q \<rfloor>\<^sub>p\<close>
  by (rule swstable_sepconj_semidistrib, simp add: stablerel_additivity_of_update)

lemma wsstable_pred_pheap_semidistrib:
  \<open>\<lceil> P \<^emph> Q \<rceil>\<^sub>p \<le> \<lceil> P \<rceil>\<^sub>p \<^emph> \<lceil> Q \<rceil>\<^sub>p\<close>
  by (rule wsstable_sepconj_semidistrib, simp add: stablerel_additivity_of_update)

end