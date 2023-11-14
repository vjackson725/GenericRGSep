theory PermHeap
  imports Stabilisation
begin

section \<open> Finite Heaps With Permissions \<close>

typedef ('p,'a,'b) pheap =
  \<open>{h::'a \<rightharpoonup> 'p::perm_alg \<times> 'b. finite (dom h)}\<close>
  morphisms app_pheap Abs_pheap
  by (rule exI[where x=Map.empty], force)

setup_lifting type_definition_pheap

lemmas Abs_pheap_inverse' = Abs_pheap_inverse[OF iffD2[OF mem_Collect_eq]]

syntax app_pheap :: \<open>('p::perm_alg,'a,'b) pheap \<Rightarrow> 'a \<Rightarrow> ('p \<times> 'b) option\<close> (infix \<open>\<bullet>\<close> 990)

lift_definition pheap_empty :: \<open>('p::perm_alg,'a,'b) pheap\<close> is \<open>Map.empty\<close>
  by simp

lift_definition upd_pheap
  :: \<open>('p::perm_alg,'a,'b) pheap \<Rightarrow> 'a \<Rightarrow> 'p \<times> 'b \<Rightarrow> ('p,'a,'b) pheap\<close>
  is \<open>\<lambda>h x pv. h(x \<mapsto> pv)\<close>
  by simp

nonterminal pmaplets and pmaplet

syntax
  "_pmaplet"  :: "['a, 'a] \<Rightarrow> pmaplet"             ("_ /\<mapsto>p/ _")
  "_pmaplets" :: "['a, 'a] \<Rightarrow> pmaplet"             ("_ /[\<mapsto>p]/ _")
  ""         :: "pmaplet \<Rightarrow> pmaplets"             ("_")
  "_pMaplets" :: "[pmaplet, pmaplets] \<Rightarrow> pmaplets" ("_,/ _")
  "_pMapUpd"  :: "['a \<rightharpoonup> 'b, pmaplets] \<Rightarrow> 'a \<rightharpoonup> 'b" ("_/'(_')" [900, 0] 900)
  "_pMap"     :: "pmaplets \<Rightarrow> 'a \<rightharpoonup> 'b"            ("(1[_])")

translations
  "_pMapUpd m (_pMaplets xy ms)"  \<rightleftharpoons> "_pMapUpd (_pMapUpd m xy) ms"
  "_pMapUpd m (_pmaplet  x y)"    \<rightleftharpoons> "CONST upd_pheap m x y"
  "_pMap ms"                     \<rightleftharpoons> "_pMapUpd (CONST pheap_empty) ms"
  "_pMap (_pMaplets ms1 ms2)"     \<leftharpoondown> "_pMapUpd (_pMap ms1) ms2"
  "_pMaplets ms1 (_pMaplets ms2 ms3)" \<leftharpoondown> "_pMaplets (_pMaplets ms1 ms2) ms3"


lemma pheap_ext:
  fixes a b :: \<open>('p::perm_alg,'a,'b) pheap\<close>
  shows \<open>(\<And>x. a \<bullet> x = b \<bullet> x) \<Longrightarrow> a = b\<close>
  by (force intro: iffD1[OF app_pheap_inject])

lemma pheap_eq_iff:
  fixes a b :: \<open>('p::perm_alg,'a,'b) pheap\<close>
  shows \<open>a = b \<longleftrightarrow> (\<forall>x. a \<bullet> x = b \<bullet> x)\<close>
  using pheap_ext by blast

lemmas app_pheap' = app_pheap[simplified]

lemma Abs_pheap_inverse_app[simp]:
  \<open>Abs_pheap (app_pheap h) \<bullet> x = h \<bullet> x\<close>
  by (simp add: app_pheap_inverse)

lemma app_Abs_pheap_Option_bind[simp]:
  \<open>finite (dom a) \<Longrightarrow> app_pheap (Abs_pheap (\<lambda>x. Option.bind (a x) f)) x = Option.bind (a x) f\<close>
  by (subst Abs_pheap_inverse; force intro: rev_finite_subset simp add: dom_def bind_eq_Some_conv)

lemma specified_pheap_collapse:
  \<open>(\<forall>x h. P (h \<bullet> x)) \<longleftrightarrow> (\<forall>a. P a)\<close>
  apply (rule iffI)
   apply (clarsimp,
      drule_tac x=\<open>undefined\<close> in spec,
      drule_tac x=\<open>Abs_pheap (\<lambda>y. if y = undefined then a else None)\<close> in spec)
    apply (clarsimp simp add: Abs_pheap_inverse dom_def)
  apply simp
  done

subsection \<open>Basic pheap operations\<close>

subsubsection \<open> Domain \<close>

lift_definition dom_pheap :: \<open>('p::perm_alg,'a,'b) pheap \<Rightarrow> 'a set\<close> is \<open>dom\<close> .

lemma finite_dom_app_pheap[simp]:
  \<open>finite (dom (app_pheap a))\<close>
  using app_pheap by blast

lemma finite_dom_pheap[simp]:
  \<open>finite (dom_pheap a)\<close>
  by (simp add: dom_pheap.rep_eq)

lemma in_dom_pheap_iff:
  \<open>x \<in> dom_pheap a \<longleftrightarrow> (\<exists>c v. a \<bullet> x = Some (c,v))\<close>
  by (simp add: dom_pheap.rep_eq dom_def)

lemma dom_pheap_iff:
  \<open>dom_pheap a = {x. \<exists>c v. a \<bullet> x = Some (c,v)}\<close>
  by (simp add: dom_pheap.rep_eq dom_def)

lemma ex_pheap_iff_ex_finite_mapfn:
  fixes P :: \<open>'a \<Rightarrow> ('p::perm_alg \<times> 'b) option \<Rightarrow> bool\<close>
  shows \<open>(\<exists>h. \<forall>x. P x (h \<bullet> x)) \<longleftrightarrow> (\<exists>hf. finite (dom hf) \<and> (\<forall>x. P x (hf x)))\<close>
  apply (rule iffI)
   apply (clarify, rule_tac x=\<open>app_pheap h\<close> in exI, force)
  apply (clarify, rule_tac x=\<open>Abs_pheap hf\<close> in exI, force simp add: Abs_pheap_inverse')
  done

lemma pheap_choice:
  fixes P :: \<open>'a \<Rightarrow> ('p::perm_alg \<times> 'b) option \<Rightarrow> bool\<close>
  assumes
    \<open>finite {x. (\<exists>y. P x (Some y)) \<and> \<not> P x None}\<close>
    \<open>\<forall>x. \<exists>cx. P x cx\<close>
  shows \<open>\<exists>c. \<forall>x. P x (c \<bullet> x)\<close>
  using assms
  by (simp add: ex_pheap_iff_ex_finite_mapfn finite_map_choice_iff)

subsubsection \<open> Map \<close>

text \<open>change the values of a pheap without changing the domain\<close>

lift_definition map_pheap :: \<open>('p::perm_alg \<Rightarrow> 'p) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('p,'i,'a) pheap \<Rightarrow> ('p,'i,'b) pheap\<close>
  is \<open>\<lambda>fp::('p \<Rightarrow> 'p). \<lambda>fv h. \<lambda>x. map_option (map_prod fp fv) (h x)\<close>
  by (force simp add: dom_map_option)

lemma map_app_pheap_eq[simp]:
  \<open>map_pheap fp fv a \<bullet> x = map_option (map_prod fp fv) (a \<bullet> x)\<close>
  by (metis map_pheap.rep_eq)

lemma dom_map_pheap_eq[simp]:
  \<open>dom_pheap (map_pheap fp fv a) = dom_pheap a\<close>
  by (simp add: dom_pheap_iff map_pheap.rep_eq)

subsubsection \<open> Sequence \<close>

instantiation pheap :: (perm_alg, type, type) monoid_seq
begin

lift_definition seq_pheap :: \<open>('a::perm_alg,'b,'c) pheap \<Rightarrow> ('a,'b,'c) pheap \<Rightarrow> ('a,'b,'c) pheap\<close>is
  \<open>\<lambda>a b. \<lambda>x. case a x of Some y \<Rightarrow> Some y | None \<Rightarrow> b x\<close>
  apply (rename_tac a b)
  apply (rule_tac B=\<open>dom a \<union> dom b\<close> in rev_finite_subset; force split: option.splits)
  done

lemma seq_app_pheap_eq[simp]:
  \<open>(a \<triangleright> b) \<bullet> x = (case a \<bullet> x of Some y \<Rightarrow> Some y | None \<Rightarrow> b \<bullet> x)\<close>
  by (clarsimp simp add: seq_pheap.rep_eq)

lemma dom_seq_pheap_eq[simp]:
  \<open>dom_pheap (a \<triangleright> b) = dom_pheap a \<union> dom_pheap b\<close>
  by (simp add: dom_pheap.rep_eq seq_pheap.rep_eq set_eq_iff dom_def split: option.splits)


lift_definition skip_pheap :: \<open>('a::perm_alg,'b,'c) pheap\<close> is \<open>Map.empty\<close>
  by simp

lemma skip_app_pheap[simp]:
  \<open>SKIP \<bullet> x = None\<close>
  by (simp add: skip_pheap.rep_eq)

instance
  by standard (simp add: pheap_eq_iff split: option.splits)+

end


subsubsection \<open> Restriction \<close>

lift_definition restrict_pheap :: \<open>('a::perm_alg,'b,'c) pheap \<Rightarrow> 'b set \<Rightarrow> ('a,'b,'c) pheap\<close>
  (infixr \<open>|`p\<close> 110) is \<open>(|`)\<close>
  by (clarsimp simp add: restrict_map_def dom_def)

lemma restrict_app_pheap_eq[simp]:
  \<open>(a |`p A) \<bullet> x = (if x \<in> A then a \<bullet> x else None)\<close>
  by (simp add: restrict_pheap.rep_eq)

lemma dom_restrict_pheap_eq[simp]: \<open>dom_pheap (a |`p A) = dom_pheap a \<inter> A\<close>
  by (simp add: dom_pheap.rep_eq seq_pheap.rep_eq set_eq_iff dom_def split: option.splits)

lemma restrict_dom_subset_eq:
  \<open>dom_pheap a \<subseteq> A \<Longrightarrow> a |`p A = a\<close>
  by (rule ccontr, clarsimp simp add: dom_pheap.rep_eq pheap_eq_iff dom_def subset_iff
      split: if_splits)

lemma restrict_sequence_right:
  \<open>(a \<triangleright> b) = (a \<triangleright> b |`p (- dom_pheap a))\<close>
  by (simp add: pheap_eq_iff dom_pheap_iff split: option.splits)

section \<open>Operations on permissions\<close>

subsection \<open> strictly less than \<close>

abbreviation subhperm :: \<open>('p::perm_alg \<times> 'a) option \<Rightarrow> ('p \<times> 'a) option \<Rightarrow> bool\<close>
  (infix \<open>\<subset>\<^sub>d\<close> 50) where
  \<open>a \<subset>\<^sub>d b \<equiv>
    (a = None \<longrightarrow> (\<exists>y. b = Some y)) \<and> (\<forall>pa v. a = Some (pa, v) \<longrightarrow> (\<exists>pb>pa. b = Some (pb, v)))\<close>

lemma subperm_not_refl:
  \<open>a \<subset>\<^sub>d a \<longleftrightarrow> False\<close>
  by (cases a; simp add: map_prod_def split: prod.splits)

lemma subhperm_trans:
  \<open>a \<subset>\<^sub>d b \<Longrightarrow> b \<subset>\<^sub>d c \<Longrightarrow> a \<subset>\<^sub>d c\<close>
  by fastforce

lemma None_subhperm_eq[simp]:
  \<open>None \<subset>\<^sub>d a \<longleftrightarrow> (\<exists>y. a = Some y)\<close>
  by (cases a; simp add: map_prod_def split: prod.splits)

lemma subhperm_None_eq[simp]:
  \<open>a \<subset>\<^sub>d None \<longleftrightarrow> False\<close>
  by (cases a; simp add: map_prod_def split: prod.splits)

lemma Some_subhperm_eq[simp]:
  \<open>Some (pa,va) \<subset>\<^sub>d b \<longleftrightarrow> (\<exists>pb. pa < pb \<and> b = Some (pb, va))\<close>
  by blast

subsection \<open> less than \<close>

abbreviation subhperm_eq :: \<open>('p::perm_alg \<times> 'a) option \<Rightarrow> ('p \<times> 'a) option \<Rightarrow> bool\<close>
  (infix \<open>\<subseteq>\<^sub>d\<close> 50) where
  \<open>subhperm_eq a b \<equiv> \<forall>pa v. a  = Some (pa, v) \<longrightarrow> (\<exists>pb\<ge>pa. b = Some (pb, v))\<close>

lemma subhperm_eq_refl[simp]:
  \<open>a \<subseteq>\<^sub>d a\<close>
  by simp

lemma subhperm_eq_trans:
  \<open>a \<subseteq>\<^sub>d b \<Longrightarrow> b \<subseteq>\<^sub>d c \<Longrightarrow> a \<subseteq>\<^sub>d c\<close>
  by force

lemma subhperm_eq_antisym:
  \<open>a \<subseteq>\<^sub>d b \<Longrightarrow> b \<subseteq>\<^sub>d a \<Longrightarrow> a = b\<close>
  by (cases a; cases b; force)

lemma None_subhperm_eq_eq[simp]:
  \<open>None \<subseteq>\<^sub>d a\<close>
  by simp

lemma subhperm_eq_None_eq[simp]:
  \<open>a \<subseteq>\<^sub>d None \<longleftrightarrow> a = None\<close>
  using not_Some_prod_eq
  by fastforce

lemma Some_subhperm_eq_eq[simp]:
  \<open>Some (pa,va) \<subseteq>\<^sub>d b \<longleftrightarrow> (\<exists>pb\<ge>pa. b = Some (pb, va))\<close>
  by force

lemma subhperm_aa: \<open>a \<subset>\<^sub>d b \<longleftrightarrow> a \<subseteq>\<^sub>d b \<and> \<not>(b \<subseteq>\<^sub>d a)\<close>
  by (fastforce simp add:)

subsection \<open> plus \<close>

definition plus_hperm :: \<open>('p::perm_alg \<times> 'a) option \<Rightarrow> ('p \<times> 'a) option \<Rightarrow> ('p \<times> 'a) option\<close>
  (infixl \<open>\<oplus>\<^sub>p\<close> 65) where
  \<open>plus_hperm a b \<equiv> case b of
                    Some (pb, vb) \<Rightarrow>
                      (case a of
                        Some (pa, va) \<Rightarrow> Some (pa + pb, va)
                        | None \<Rightarrow> b)
                    | None \<Rightarrow> a\<close>

lemma finite_dom_add[simp]:
  \<open>finite (dom (\<lambda>x. a x \<oplus>\<^sub>p b x)) \<longleftrightarrow> finite (dom a) \<and> finite (dom b)\<close>
  by (fastforce simp add: dom_def plus_hperm_def conj_disj_distribL conj_disj_distribR imp_conv_disj
      simp del: imp_conv_disj[symmetric] split: option.splits)

lemma plus_perm_simps[simp]:
  \<open>a \<oplus>\<^sub>p None = a\<close>
  \<open>None \<oplus>\<^sub>p b = b\<close>
  \<open>Some pa \<oplus>\<^sub>p Some pb = Some (fst pa + fst pb, snd pa)\<close>
  by (force simp add: plus_hperm_def split: option.splits prod.splits)+

lemma plus_perm_eq_None_iff[simp]:
  \<open>a \<oplus>\<^sub>p b = None \<longleftrightarrow> a = None \<and> b = None\<close>
  by (force simp add: plus_hperm_def split: option.splits)

lemma plus_perm_eq_Some_iff:
  \<open>\<And>a pb vb c.
    a \<oplus>\<^sub>p Some (pb, vb) = c \<longleftrightarrow>
      (case a of
        None \<Rightarrow> c = Some (pb,vb)
      | Some (pa, va) \<Rightarrow> c = Some (pa + pb, va))\<close>
  \<open>\<And>pa va b c.
    Some (pa, va) \<oplus>\<^sub>p b  = c \<longleftrightarrow>
      (case b of
        None \<Rightarrow> c = Some (pa, va)
      | Some (pb, vb) \<Rightarrow> c = Some (pa + pb, va))\<close>
  \<open>\<And>a b p v.
    (a \<oplus>\<^sub>p b) = Some (p, v) \<longleftrightarrow>
      (b = None \<longrightarrow> a = Some (p, v)) \<and>
      (a = None \<longrightarrow> b = Some (p, v)) \<and>
      (\<forall>pa va. a = Some (pa, va) \<longrightarrow>
        (\<forall>pb vb. b = Some (pb, vb) \<longrightarrow>
          p = pa + pb \<and> v = va))\<close>
  by (force simp add: plus_hperm_def split: option.splits)+

lemma hperm_plus_bind_left[simp]:
  \<open>Option.bind a f \<oplus>\<^sub>p b =
    (case a of
      None \<Rightarrow> b
    | Some x \<Rightarrow> f x \<oplus>\<^sub>p b)\<close>
  by (force simp add: plus_hperm_def Option.bind_eq_Some_conv Option.bind_eq_None_conv
      split: option.splits)

lemma hperm_plus_bind_right[simp]:
  \<open>a \<oplus>\<^sub>p Option.bind b f =
    (case b of
      None \<Rightarrow> a
    | Some x \<Rightarrow> a \<oplus>\<^sub>p f x)\<close>
  by (force simp add: plus_hperm_def Option.bind_eq_Some_conv Option.bind_eq_None_conv
      split: option.splits)

lemmas plus_perm_eq_Some_iff_rev = HOL.trans[OF HOL.eq_commute plus_perm_eq_Some_iff(3)]

subsection \<open> Disjointness \<close>

definition disjoint_set_pheap :: \<open>('p::perm_alg,'a,'b) pheap \<Rightarrow> 'a set \<Rightarrow> ('p,'a,'b) pheap \<Rightarrow> bool\<close>
  ("_ ##\<^bsub>_\<^esub> _" [61,0,61] 60) where
  \<open>a ##\<^bsub>A\<^esub> b \<equiv> \<forall>x\<in>A.
    \<forall>pa va. a \<bullet> x = Some (pa, va) \<longrightarrow>
      (\<forall>pb vb. b \<bullet> x = Some (pb, vb) \<longrightarrow> pa ## pb \<and> va = vb)\<close>

lemma disjoint_set_un_eq[simp]:
  \<open>a ##\<^bsub>A \<union> B\<^esub> b \<longleftrightarrow> a ##\<^bsub>A\<^esub> b \<and> a ##\<^bsub>B\<^esub> b\<close>
  by (simp add: disjoint_set_pheap_def Ball_def, blast)

lemma disjoint_set_antimono_pheap:
  \<open>Y \<subseteq> X \<Longrightarrow> a ##\<^bsub>X\<^esub> b \<Longrightarrow> a ##\<^bsub>Y\<^esub> b\<close>
  by (metis Un_absorb2 disjoint_set_un_eq)

lemma disjoint_restrict_pheap_iff[simp]:
  \<open>a |`p A ##\<^bsub>X\<^esub> b \<longleftrightarrow> a ##\<^bsub>X \<inter> A\<^esub> b\<close>
  \<open>a ##\<^bsub>X\<^esub> b |`p B \<longleftrightarrow> a ##\<^bsub>X \<inter> B\<^esub> b\<close>
  by (force simp add: disjoint_set_pheap_def Ball_def)+

lemma disjoint_skip[iff]:
  \<open>SKIP ##\<^bsub>A\<^esub> b\<close>
  \<open>a ##\<^bsub>A\<^esub> SKIP\<close>
  by (clarsimp simp add: disjoint_set_pheap_def)+

lemma disjoint_seq[simp]:
  \<open>a1 \<triangleright> a2 ##\<^bsub>A\<^esub> b \<longleftrightarrow> a1 ##\<^bsub>A\<^esub> b \<and> a2 ##\<^bsub>A - dom_pheap a1\<^esub> b\<close>
  \<open>b ##\<^bsub>A\<^esub> a1 \<triangleright> a2 \<longleftrightarrow> b ##\<^bsub>A\<^esub> a1 \<and> b ##\<^bsub>A - dom_pheap a1\<^esub> a2\<close>
   apply (clarsimp simp add: disjoint_set_pheap_def dom_pheap_iff Ball_def
      all_conj_distrib[symmetric] split: option.splits)
   apply (rule all_cong1, case_tac \<open>app_pheap a1 x\<close>; force)
   apply (clarsimp simp add: disjoint_set_pheap_def dom_pheap_iff Ball_def
      all_conj_distrib[symmetric] split: option.splits)
   apply (rule all_cong1, case_tac \<open>app_pheap a1 x\<close>; force)
  done

lemma disjoint_set_dom_pheap:
  \<open>dom_pheap a \<inter> X \<inter> dom_pheap b = {} \<Longrightarrow> a ##\<^bsub>X\<^esub> b\<close>
  by (force simp add: disjoint_set_pheap_def Ball_def dom_pheap.rep_eq)


text \<open>Define disjointness on pheaps\<close>
instantiation pheap :: (perm_alg,type,type) disjoint
begin

definition disjoint_pheap :: \<open>('a::perm_alg,'b,'c) pheap \<Rightarrow> ('a,'b,'c) pheap \<Rightarrow> bool\<close> where
  \<open>disjoint_pheap a b \<equiv> a ##\<^bsub>UNIV\<^esub> b\<close>

instance by standard

end

lemmas disjoint_pheap_def' = disjoint_pheap_def disjoint_set_pheap_def

lemma disjoint_pheap_Some_same_valD:
  \<open>a ## b \<Longrightarrow> a \<bullet> x = Some (pa,va) \<Longrightarrow>  b \<bullet> x = Some (pb,vb) \<Longrightarrow> va = vb\<close>
  by (simp add: disjoint_pheap_def disjoint_set_pheap_def)

lemma disjoint_dom_pheap:
  \<open>dom_pheap a \<inter> dom_pheap b = {} \<Longrightarrow> a ## b\<close>
  by (simp add: disjoint_pheap_def disjoint_set_dom_pheap)

subsection \<open> Addition \<close>

text \<open>Define plus on pheaps\<close>
instantiation pheap :: (perm_alg, type, type) plus
begin

lift_definition plus_pheap :: \<open>('a,'b,'c) pheap \<Rightarrow> ('a,'b,'c) pheap \<Rightarrow> ('a,'b,'c) pheap\<close> is
  \<open>\<lambda>ma mb. \<lambda>x. ma x \<oplus>\<^sub>p mb x\<close>
  apply (rename_tac ma mb)
  apply (simp add: dom_def plus_hperm_def split: option.splits)
  apply (rule_tac B=\<open>dom ma \<union> dom mb\<close> in rev_finite_subset; force simp add: dom_def)
  done

instance by standard

end

lemma app_plus_pheap[simp]:
  \<open>(a + b) \<bullet> x = a \<bullet> x \<oplus>\<^sub>p b \<bullet> x\<close>
  by (simp add: disjoint_pheap_def' plus_pheap_def Abs_pheap_inverse)

lemma restrict_pheap_add_eq[simp]:
  \<open>(a + b) |`p A = a |`p A + b |`p A\<close>
  by (simp add: pheap_eq_iff)

lemma dom_plus_pheap_eq[simp]: \<open>dom_pheap (h1 + h2) = dom_pheap h1 \<union> dom_pheap h2\<close>
  by (simp add: dom_pheap.rep_eq plus_hperm_def dom_def set_eq_iff split: option.splits)

lemma appAbs_plus_pheap[simp]:
  \<open>finite (dom a) \<Longrightarrow> finite (dom b) \<Longrightarrow> app_pheap (Abs_pheap (\<lambda>x. a x \<oplus>\<^sub>p b x)) x = a x \<oplus>\<^sub>p b x\<close>
  by (force simp add: Abs_pheap_inverse)

text \<open>Define less than and less than or equal on pheaps\<close>

instantiation pheap :: (perm_alg, type, type) order_bot
begin

definition less_eq_pheap :: \<open>('a::perm_alg,'b,'c) pheap \<Rightarrow> ('a,'b,'c) pheap \<Rightarrow> bool\<close> where
  \<open>less_eq_pheap ma mb \<equiv> \<forall>x. ma \<bullet> x \<subseteq>\<^sub>d mb \<bullet> x\<close>

lemma less_eq_pheap_iff:
  \<open>a \<le> b \<longleftrightarrow> (\<forall>x pa v. a \<bullet> x = Some (pa, v) \<longrightarrow> (\<exists>pb\<ge>pa. b \<bullet> x = Some (pb, v)))\<close>
  by (simp add: less_eq_pheap_def)

definition less_pheap :: \<open>('a::perm_alg,'b,'c) pheap \<Rightarrow> ('a,'b,'c) pheap \<Rightarrow> bool\<close> where
  \<open>less_pheap a b \<equiv> a \<le> b \<and> \<not>(b \<le> a)\<close>

lift_definition bot_pheap :: \<open>('a::perm_alg,'b,'c) pheap\<close> is \<open>Map.empty\<close>
  by simp

lemma app_bot_pheap[simp]:
  \<open>\<bottom> \<bullet> x = None\<close>
  by (simp add: bot_pheap.rep_eq)

instance
  apply standard
      apply (force simp add: less_pheap_def)
     apply (force simp add: less_eq_pheap_def intro: subhperm_eq_refl)
    apply (force dest: subhperm_eq_trans simp add: less_eq_pheap_def)
   apply (force dest: subhperm_eq_antisym simp add: less_eq_pheap_def pheap_eq_iff)
  apply (force simp add: less_eq_pheap_def)
  done

end

subsection \<open> Order and restrict \<close>

lemma restrict_alwas_subheap_eq[simp]:
  \<open>a |`p A \<le> a\<close>
  by (simp add: restrict_pheap_def less_eq_pheap_def Abs_pheap_inverse, simp add: restrict_map_def)


lemma subperm_eq_restrictL[simp]: \<open>(a |`p A) \<bullet> x \<subseteq>\<^sub>d b \<bullet> x \<longleftrightarrow> (x \<in> A \<longrightarrow> a \<bullet> x \<subseteq>\<^sub>d b \<bullet> x)\<close>
  by simp

lemma subperm_eq_restrictR[simp]:
  \<open>a \<bullet> x \<subseteq>\<^sub>d (b |`p B) \<bullet> x \<longleftrightarrow> (if x \<in> B then a \<bullet> x \<subseteq>\<^sub>d b \<bullet> x else a \<bullet> x = None)\<close>
  by (simp add: dom_pheap_def domIff)

lemma subperm_eq_seqL[simp]:
  \<open>(a1 \<triangleright> a2) \<bullet> x \<subseteq>\<^sub>d b \<bullet> x \<longleftrightarrow> a1 \<bullet> x \<subseteq>\<^sub>d b \<bullet> x \<and> (a1 \<bullet> x = None \<longrightarrow> a2 \<bullet> x \<subseteq>\<^sub>d b \<bullet> x)\<close>
  by (simp add: split: option.splits)

lemma subperm_eq_seqR[simp]:
  \<open>a \<bullet> x \<subseteq>\<^sub>d (b1 \<triangleright> b2) \<bullet> x \<longleftrightarrow> (if b1 \<bullet> x = None then a \<bullet> x \<subseteq>\<^sub>d b2 \<bullet> x else a \<bullet> x \<subseteq>\<^sub>d b1 \<bullet> x)\<close>
  by (clarsimp split: option.splits)


lemma le_map_pheapL:
  \<open>map_pheap fp fv a \<le> a \<longleftrightarrow> (\<forall>x p v. app_pheap a x = Some (p, v) \<longrightarrow> fp p \<le> p \<and> fv v = v)\<close>
  by (force simp add: less_eq_pheap_def)

section \<open> Pheaps are a sepalgebra \<close>

instantiation pheap :: (perm_alg,type,type) sep_alg
begin


lift_definition zero_pheap :: \<open>('a::perm_alg,'b,'c) pheap\<close> is \<open>Map.empty\<close>
  by simp

lemma app_zero_pheap[simp]:
  \<open>0 \<bullet> x = None\<close>
  by (simp add: zero_pheap.rep_eq)

lift_definition unitof_pheap :: \<open>('a::perm_alg,'b,'c) pheap \<Rightarrow> ('a::perm_alg,'b,'c) pheap\<close>
  is \<open>\<lambda>_. Map.empty\<close>
  by simp

lemma app_unitof_pheap[simp]:
  \<open>unitof h \<bullet> x = None\<close>
  by (simp add: unitof_pheap.rep_eq)

lemma bot_pheap_eq_zero_pheap:
  \<open>(\<bottom> :: ('a,'b,'c) pheap) = 0\<close>
  by (simp add: zero_pheap.abs_eq bot_pheap.abs_eq)

lemma le_iff_sepadd_helper:
  fixes a b :: \<open>('a::perm_alg,'b,'c) pheap\<close>
  shows \<open>(a \<le> b) = (\<exists>c. a ## c \<and> b = a + c)\<close>
  apply (rule iffI)
  subgoal
    apply (clarsimp simp add: pheap_eq_iff less_eq_pheap_def disjoint_pheap_def')
    apply (simp add: all_conj_distrib[symmetric])
    apply (rule pheap_choice)
     apply (simp add: Collect_conj_eq)
     apply (rule finite_Int, rule disjI2)
     apply (rule rev_finite_subset[of \<open>dom_pheap a \<union> dom_pheap b\<close>], force)
     apply (force simp add: dom_pheap_def)
    apply clarsimp
    apply (drule_tac x=x in spec)
    apply (case_tac \<open>a \<bullet> x\<close>)
     apply force
    apply (clarsimp simp add: order.order_iff_strict)
    apply (erule disjE; force simp add: less_iff_sepadd)
    done
  apply (force simp add: less_eq_pheap_def plus_hperm_def
      disjoint_pheap_def disjoint_set_pheap_def split: option.splits) 
  done

instance
  apply standard
          apply (force simp add: disjoint_pheap_def')
          apply (force simp add: disjoint_pheap_def')
    (* PCM *)
         apply (force simp add: pheap_eq_iff plus_hperm_def disjoint_pheap_def' partial_add_assoc split: option.splits)
        apply (force simp add: plus_hperm_def disjoint_pheap_def' pheap_eq_iff partial_add_commute
      split: option.splits)
    (* separation *)
       apply (force simp add: disjoint_pheap_def' disjoint_symm)
  subgoal
    apply (clarsimp simp add: disjoint_pheap_def' plus_hperm_def split: option.splits)
    apply (drule_tac x=x in spec)+
    apply (meson disjoint_add_rightL)
    done
      (* subgoal *)
    apply (clarsimp simp add: disjoint_pheap_def' plus_hperm_def split: option.splits)
    apply (drule_tac x=x in spec)+
    apply (case_tac \<open>c \<bullet> x\<close>)
     apply (clarsimp simp add: disjoint_symm; fail)
    apply (force dest: disjoint_add_right_commute)
    (* done *)
    (* subgoal *)
     apply (clarsimp simp add: fun_eq_iff pheap_eq_iff all_conj_distrib[symmetric] disjoint_pheap_def')
    apply (drule_tac x=x in spec)+
    apply (case_tac \<open>app_pheap a x\<close>, force)
    apply (case_tac \<open>app_pheap b x\<close>, force)
    apply (case_tac \<open>app_pheap c x\<close>, force)
    apply (force dest: positivity simp add: plus_perm_eq_Some_iff(2) split: option.splits)
    (* done *)
     apply (metis le_iff_sepadd_helper less_le_not_le order_le_imp_less_or_eq)
    apply (force simp add: disjoint_pheap_def')
   apply (force simp add: disjoint_pheap_def' pheap_eq_iff)
  apply (force simp add: pheap_eq_iff)
  done

end

subsection \<open> halving algebra \<close>

instantiation pheap :: (halving_perm_alg,type,type) halving_sep_alg
begin

lift_definition half_pheap :: \<open>('a,'b,'c) pheap \<Rightarrow> ('a,'b,'c) pheap\<close> is
  \<open>\<lambda>h. \<lambda>x. map_option (apfst half) (h x)\<close>
  by (simp add: dom_map_option)

lemma half_pheap_app[simp]:
  fixes h :: \<open>('a,'b,'c) pheap\<close>
  shows \<open>half h \<bullet> x = map_option (apfst half) (h \<bullet> x)\<close>
  by (simp add: half_pheap.rep_eq)

instance
  apply standard
    apply (clarsimp simp add: pheap_eq_iff plus_hperm_def half_additive_split split: option.splits)
   apply (clarsimp simp add: disjoint_pheap_def' half_self_disjoint)
  apply (clarsimp simp add: pheap_eq_iff plus_hperm_def disjoint_pheap_def' half_sepadd_distrib
      split: option.splits)
  done

end

subsection \<open> disjoint parts algebra \<close>

instantiation pheap :: (disjoint_parts_perm_alg,type,type) disjoint_parts_perm_alg
begin

instance
  apply standard
  apply (clarsimp simp add: disjoint_pheap_def')
  apply (drule_tac x=x in spec)+
  apply (case_tac \<open>a \<bullet> x\<close>)
   apply (simp only: plus_perm_simps; fail)
  apply (case_tac \<open>b \<bullet> x\<close>)
   apply (simp only: plus_perm_simps; fail)
  apply (clarsimp simp only: plus_perm_simps option.inject)
  apply (drule spec2, drule mp, rule refl)+
  apply (simp add: disjointness_left_plus_eq)
  done

end

subsection \<open> cancellative algebra \<close>

instantiation pheap :: (cancel_no_unit_perm_alg, type, type) cancel_sep_alg
begin

lemma plus_hperm_partial_right_cancel:
  fixes a b c :: \<open>('a \<times> 'v) option\<close>
  shows
    \<open>(\<forall>a' c'. a = Some a' \<longrightarrow> c = Some c' \<longrightarrow> fst a' ## fst c' \<and> snd a' = snd c') \<Longrightarrow>
      (\<forall>b' c'. b = Some b' \<longrightarrow> c = Some c' \<longrightarrow> fst b' ## fst c' \<and> snd b' = snd c') \<Longrightarrow>
      (a \<oplus>\<^sub>p c = b \<oplus>\<^sub>p c) \<longleftrightarrow> (a = b)\<close>
  by (fastforce simp add: plus_hperm_def split: option.splits prod.splits)

instance
  by standard
    (force simp add: disjoint_pheap_def' pheap_eq_iff plus_hperm_partial_right_cancel)

end

subsection \<open> glb + distributive algebras \<close>

instantiation pheap :: (allcompatible_glb_perm_alg, type, type) glb_sep_alg
begin

lift_definition inf_pheap :: \<open>('a,'b,'c) pheap \<Rightarrow> ('a,'b,'c) pheap \<Rightarrow> ('a,'b,'c) pheap\<close> is
  \<open>\<lambda>ha hb.
    (\<lambda>x. case ha x of Some (pa, va) \<Rightarrow>
          (case hb x of Some (pb, vb) \<Rightarrow>
            if va = vb
            then Some (pa \<sqinter> pb, va)
            else None
          | None \<Rightarrow> None)
        | None \<Rightarrow> None)\<close>
  by (simp add: dom_def option.case_eq_if)

lemma app_inf_pheap_eq:
  fixes a b :: \<open>('a,'b,'c) pheap\<close>
  shows
  \<open>(a \<sqinter> b) \<bullet> x =
    (case a \<bullet> x of Some (pa, va) \<Rightarrow>
          (case b \<bullet> x of Some (pb, vb) \<Rightarrow>
            if va = vb
            then Some (pa \<sqinter> pb, va)
            else None
          | None \<Rightarrow> None)
        | None \<Rightarrow> None)\<close>
  by (simp add: inf_pheap.rep_eq split: option.splits)

instance
  apply standard
    apply (force simp add: less_eq_pheap_def app_inf_pheap_eq split: option.splits)
   apply (force simp add: less_eq_pheap_def app_inf_pheap_eq split: option.splits)

  apply (simp add: all_compatible less_eq_pheap_def app_inf_pheap_eq split: option.splits)
  apply clarsimp
  apply (rule conjI, metis not_Some_prod_eq)
  apply clarsimp
  apply (rename_tac pa va)
  apply (rule conjI, metis not_Some_prod_eq)
  apply clarsimp
  apply (rename_tac pb vb)
  apply (rule conjI)
   apply fastforce
  apply clarsimp
  apply (rule ccontr)
  apply fastforce
  done

end

instantiation pheap :: (distrib_perm_alg, type, type) distrib_sep_alg
begin

(* TODO: not good enough for (0,1] permissions ! *)

instance
  by standard
    (fastforce simp add: disjoint_pheap_def' pheap_eq_iff app_inf_pheap_eq inf_add_distrib1
      split: option.splits)

end

end