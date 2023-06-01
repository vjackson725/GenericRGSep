theory DeallocHeap
  imports PermHeap HOL.Rat
begin

section \<open>Permission Heaps with unstable reads and deallocation\<close>

typedef perm = \<open>{(d,w)::rat \<times> rat|d w. 0 \<le> d \<and> d \<le> 1 \<and> 0 \<le> w \<and> w \<le> 1 \<and> 0 < d + w }\<close>
  by (rule exI[of _ \<open>(1,1)\<close>], simp)

setup_lifting type_definition_perm

lift_definition dperm :: \<open>perm \<Rightarrow> rat\<close> is \<open>fst\<close> .
lift_definition wperm :: \<open>perm \<Rightarrow> rat\<close> is \<open>snd\<close> .

lemmas Rep_perm_constraints = perm.Rep_perm[simplified mem_Collect_eq]

lemma Rep_perm_orient[simp]:
  \<open>(d,w) = Rep_perm a \<longleftrightarrow> Rep_perm a = (d,w)\<close>
  by (simp add: eq_commute)

lemma Rep_perm_parts:
  \<open>Rep_perm a = (dperm a, wperm a)\<close>
  by (simp add: dperm.rep_eq wperm.rep_eq)

lemma Rep_perm_parts_rev:
  \<open>x = dperm a \<Longrightarrow> y = wperm a \<Longrightarrow> (x, y) = Rep_perm a\<close>
  by (simp add: dperm.rep_eq wperm.rep_eq)

lemma wperm_dperm_Abs:
  assumes
    \<open>0 \<le> d\<close>
    \<open>d \<le> 1\<close>
    \<open>0 \<le> w\<close>
    \<open>w \<le> 1\<close>
    \<open>0 < d + w\<close>
  shows
  \<open>wperm (Abs_perm (d,w)) = w\<close>
  \<open>dperm (Abs_perm (d,w)) = d\<close>
  using assms
  by (simp add: wperm.rep_eq dperm.rep_eq Abs_perm_inverse)+

lemma Rep_perm_eq_iff:
  \<open>Rep_perm a = x \<longleftrightarrow>
    fst x = dperm a \<and> snd x = wperm a \<and>
    0 \<le> dperm a \<and> dperm a \<le> 1 \<and>
    0 \<le> wperm a \<and> wperm a \<le> 1 \<and>
    0 < dperm a + wperm a\<close>
  by (metis Rep_perm_constraints dperm.rep_eq wperm.rep_eq fst_conv snd_conv prod.collapse)

lemma Rep_perm_constraintsD:
  \<open>Rep_perm a = (d,w) \<Longrightarrow> 0 \<le> d\<close>
  \<open>Rep_perm a = (d,w) \<Longrightarrow> d \<le> 1\<close>
  \<open>Rep_perm a = (d,w) \<Longrightarrow> 0 \<le> w\<close>
  \<open>Rep_perm a = (d,w) \<Longrightarrow> w \<le> 1\<close>
  \<open>Rep_perm a = (d,w) \<Longrightarrow> 0 < d + w\<close>
  using Rep_perm_constraints[of a]
  by simp+

lemma Rep_perm_constraints_complex:
  assumes \<open>Rep_perm a = (d,w)\<close>
  shows
    \<open>w \<le> 0 \<longleftrightarrow> w = 0\<close>
    \<open>w \<ge> 1 \<longleftrightarrow> w = 1\<close>
    \<open>d \<le> 0 \<longleftrightarrow> d = 0\<close>
    \<open>d \<ge> 1 \<longleftrightarrow> d = 1\<close>
  using assms
  by (fastforce simp add: Rep_perm_constraintsD order.antisym dest: leD)+

lemma dperm_wperm_constraints:
  \<open>0 \<le> dperm p\<close>
  \<open>dperm p \<le> 1\<close>
  \<open>0 \<le> wperm p\<close>
  \<open>wperm p \<le> 1\<close>
  \<open>0 < dperm p + wperm p\<close>
  using Rep_perm_eq_iff
  by blast+

lemma dperm_wperm_constraints_complex:
  \<open>wperm a \<le> 0 \<longleftrightarrow> wperm a = 0\<close>
  \<open>wperm a \<ge> 1 \<longleftrightarrow> wperm a = 1\<close>
  \<open>dperm a \<le> 0 \<longleftrightarrow> dperm a = 0\<close>
  \<open>dperm a \<ge> 1 \<longleftrightarrow> dperm a = 1\<close>
  by (simp add: dperm_wperm_constraints order.antisym not_le)+

lemmas perm_eq_iff = Rep_perm_inject[symmetric]

lemma perm_eq_iff_parts:
  \<open>a = b \<longleftrightarrow> wperm a = wperm b \<and> dperm a = dperm b\<close>
  by (metis Rep_perm_inject dperm.rep_eq prod.expand wperm.rep_eq)

lemma eq_Abs_perm_iff:
  \<open>0 \<le> fst a' \<Longrightarrow> fst a' \<le> 1 \<Longrightarrow>
    0 \<le> snd a' \<Longrightarrow> snd a' \<le> 1 \<Longrightarrow>
    0 < fst a' + snd a' \<Longrightarrow>
    a = Abs_perm a' \<longleftrightarrow> Rep_perm a = a'\<close>
  by (rule Abs_perm_inject[of \<open>Rep_perm _\<close>, simplified Rep_perm_inverse])
   (clarsimp simp add: Rep_perm_constraintsD)+

lemma eq_Abs_perm_iff':
  \<open>0 \<le> fst a' \<Longrightarrow> fst a' \<le> 1 \<Longrightarrow>
    0 \<le> snd a' \<Longrightarrow> snd a' \<le> 1 \<Longrightarrow>
    0 < fst a' + snd a' \<Longrightarrow>
    snd a' \<le> 1 \<Longrightarrow> Abs_perm a' = a \<longleftrightarrow> Rep_perm a = a'\<close>
  by (metis eq_Abs_perm_iff)

lemma ex_perm_Rep_iff:
  \<open>(\<exists>a. P (Rep_perm a) (dperm a) (wperm a)) \<longleftrightarrow>
      (\<exists>a'. 0 \<le> fst a' \<and> fst a' \<le> 1 \<and> 0 \<le> snd a' \<and> snd a' \<le> 1 \<and> 0 < fst a' + snd a' \<and> P a' (fst a') (snd a'))\<close>
  by (metis Rep_perm_eq_iff eq_Abs_perm_iff')

lemma Rep_perm_all_iff_ex:
  \<open>(\<forall>da wa. Rep_perm a = (da, wa) \<longrightarrow> P da wa) \<longleftrightarrow> (\<exists>da wa. Rep_perm a = (da, wa) \<and> P da wa)\<close>
  using Rep_perm_constraints by fastforce

lemma ex_perm_all_components_iff:
  \<open>(\<exists>a. (\<forall>da wa. Rep_perm a = (da, wa) \<longrightarrow> P da wa)) \<longleftrightarrow>
      (\<exists>da wa. 0 \<le> da \<and> da \<le> 1 \<and> 0 \<le> wa \<and> wa \<le> 1 \<and> 0 < da + wa \<and> P da wa)\<close>
  by (simp add: ex_perm_Rep_iff[where P=\<open>\<lambda>x _ _. \<forall>y z. x = f y z \<longrightarrow> P y z\<close> for f])

lemma Abs_perm_wperm_dperm[simp]:
  \<open>w = wperm p \<Longrightarrow> Abs_perm (dperm p, w) = p\<close>
  \<open>d = dperm p \<Longrightarrow> Abs_perm (d, wperm p) = p\<close>
  using Rep_perm_inverse dperm.rep_eq wperm.rep_eq by force+

lemma Abs_perm_inverse'[simp]:
  \<open>0 \<le> x \<Longrightarrow> x \<le> 1 \<Longrightarrow> 0 \<le> y \<Longrightarrow> y \<le> 1 \<Longrightarrow> 0 < x + y \<Longrightarrow> Rep_perm (Abs_perm (x,y)) = (x,y)\<close>
  by (clarsimp simp add: Rep_perm_constraintsD Abs_perm_inverse)

lemma Abs_perm_inject':
  \<open>0 \<le> da \<Longrightarrow> da \<le> 1 \<Longrightarrow> 0 \<le> wa \<Longrightarrow> wa \<le> 1 \<Longrightarrow> 0 < da + wa \<Longrightarrow>
    0 \<le> db \<Longrightarrow> db \<le> 1 \<Longrightarrow> 0 \<le> wb \<Longrightarrow> wb \<le> 1 \<Longrightarrow> 0 < db + wb \<Longrightarrow>
    (Abs_perm (da,wa) = Abs_perm (db,wb)) = ((da,wa) = (db,wb))\<close>
  by (clarsimp simp add: Abs_perm_inject Sigma_def)

subsection \<open> map_perm \<close>

lift_definition map_perm :: \<open>(rat \<Rightarrow> rat) \<Rightarrow> (rat \<Rightarrow> rat) \<Rightarrow> perm \<Rightarrow> perm\<close> is
  \<open>\<lambda>fd fw (d,w).
    if fd d + fw w \<le> 0 then (1,1) else 
      (max 0 (min 1 (fd d)), max 0 (min 1 (fw w)))\<close>
  by (force simp add: max_def min_def split: prod.splits)

lemma map_perm_id[simp]:
  \<open>map_perm id id = id\<close>
  by (simp add: map_perm_def fun_eq_iff Rep_perm_eq_iff split: prod.splits)

lemma map_perm_eq:
  \<open>map_perm fd fw a =
    Abs_perm (if fd (dperm a) + fw (wperm a) \<le> 0 then (1,1) else 
      (max 0 (min 1 (fd (dperm a))), max 0 (min 1 (fw (wperm a)))))\<close>
  by (force simp add: map_perm_def dperm_def wperm_def split: prod.splits)

subsection \<open> Permission Algebra Instance \<close>

instantiation perm :: perm_alg
begin

definition disjoint_perm :: \<open>perm \<Rightarrow> perm \<Rightarrow> bool\<close> where
  \<open>disjoint_perm a b \<equiv> dperm a + dperm b \<le> 1 \<and> wperm a + wperm b \<le> 1\<close>

definition less_eq_perm :: \<open>perm \<Rightarrow> perm \<Rightarrow> bool\<close> where
  \<open>less_eq_perm a b \<equiv> dperm a \<le> dperm b \<and> wperm a \<le> wperm b\<close>

lemma less_eq_permI[intro]:
  \<open>Rep_perm a = (da,wa) \<Longrightarrow> Rep_perm b = (db,wb) \<Longrightarrow>
    da \<le> db \<Longrightarrow> wa \<le> wb \<Longrightarrow>
    a \<le> b\<close>
  by (simp add: dperm.rep_eq less_eq_perm_def wperm.rep_eq)

definition less_perm :: \<open>perm \<Rightarrow> perm \<Rightarrow> bool\<close> where
  \<open>less_perm x y \<equiv> x \<le> y \<and> \<not> y \<le> x\<close>

lemma less_permI[intro]:
  \<open>Rep_perm a = (da,wa) \<Longrightarrow> Rep_perm b = (db,wb) \<Longrightarrow> da \<le> db \<Longrightarrow> wa < wb \<Longrightarrow> a < b\<close>
  \<open>Rep_perm a = (da,wa) \<Longrightarrow> Rep_perm b = (db,wb) \<Longrightarrow> da < db \<Longrightarrow> wa \<le> wb \<Longrightarrow> a < b\<close>
   by (clarsimp simp add: less_perm_def less_eq_perm_def Rep_perm_eq_iff split: prod.splits)+

lift_definition plus_perm :: \<open>perm \<Rightarrow> perm \<Rightarrow> perm\<close> is
  \<open>\<lambda>(da,wa) (db,wb). (min 1 (da + db), min 1 (wa + wb))\<close>
  by (force split: prod.splits)

lemma plus_perm_Abs_inverse[simp]:
  \<open>Rep_perm (a + b) = (min 1 (dperm a + dperm b), min 1 (wperm a + wperm b))\<close>
  by (clarsimp simp add: plus_perm.rep_eq dperm.rep_eq wperm.rep_eq split: prod.splits)

lemma dperm_wperm_plus[simp]:
  \<open>a ## b \<Longrightarrow> dperm (a + b) = dperm a + dperm b\<close>
  \<open>a ## b \<Longrightarrow> wperm (a + b) = wperm a + wperm b\<close>
  by (force simp add: plus_perm.rep_eq dperm.rep_eq wperm.rep_eq disjoint_perm_def)+

lemma wperm_plus_unrestricted:
  \<open>wperm (a + b) = min 1 (wperm a + wperm b)\<close>
  by (force simp add: plus_perm.rep_eq wperm.rep_eq)

lemma dperm_plus_unrestricted:
  \<open>dperm (a + b) = min 1 (dperm a + dperm b)\<close>
  by (force simp add: plus_perm.rep_eq dperm.rep_eq)


instance
  apply standard
            apply (force simp add: less_perm_def split: prod.splits)
           apply (force simp add: less_eq_perm_def)
          apply (force simp add: less_eq_perm_def)
         apply (force simp add: less_eq_perm_def perm_eq_iff_parts)
    (* partial comm monoid *)
        apply (force simp add: perm_eq_iff add.assoc)
       apply (force simp add: perm_eq_iff add.commute)
    (* separation laws *)
      apply (force simp add: disjoint_perm_def add.commute split: prod.splits)
  subgoal
    apply (clarsimp simp add: disjoint_perm_def plus_perm_def dperm.rep_eq wperm.rep_eq split: prod.splits)
    apply (subst (asm) Abs_perm_inverse)
     apply (metis (no_types, lifting) Abs_perm_inverse' Rep_perm Rep_perm_constraintsD(1) Rep_perm_constraintsD(3) add_nonneg_nonneg add_nonneg_pos add_pos_nonneg leI nle_le)
    apply (subst (asm) Abs_perm_inverse)
     apply (metis (no_types, lifting) Abs_perm_inverse' Rep_perm Rep_perm_constraintsD(1) Rep_perm_constraintsD(3) add_nonneg_nonneg add_nonneg_pos add_pos_nonneg leI nle_le)
    apply clarsimp
    apply (rule conjI)
     apply (metis Rep_perm_constraints_complex(3) add.assoc add_increasing2 nle_le)
    apply (metis Rep_perm_constraintsD(3) add.assoc add_increasing2 nle_le)
    done
  subgoal
    apply (clarsimp simp add: disjoint_perm_def plus_perm_def dperm.rep_eq wperm.rep_eq split: prod.splits)
    apply (subst (asm) Abs_perm_inverse)
     apply (metis (no_types, lifting) Abs_perm_inverse' Rep_perm Rep_perm_constraintsD(1) Rep_perm_constraintsD(3) add_nonneg_nonneg add_nonneg_pos add_pos_nonneg leI nle_le)
    apply (subst (asm) Abs_perm_inverse)
     apply (metis (no_types, lifting) Abs_perm_inverse' Rep_perm Rep_perm_constraintsD(1) Rep_perm_constraintsD(3) add_nonneg_nonneg add_nonneg_pos add_pos_nonneg leI nle_le)
    apply (subst Abs_perm_inverse)
      (* TODO *)
     apply (smt (z3) Abs_perm_inverse' Rep_perm Rep_perm_constraintsD(3) Rep_perm_constraintsD(5) Rep_perm_constraints_complex(3) add_nonneg_nonneg add_nonneg_pos add_pos_nonneg leI less_add_same_cancel1 less_numeral_extra(1) min.cobounded1 min_def zero_less_one_class.zero_le_one)
    apply (subst Abs_perm_inverse)
      (* TODO *)
     apply (smt (z3) Abs_perm_inverse' Rep_perm Rep_perm_constraintsD(3) Rep_perm_constraintsD(5) Rep_perm_constraints_complex(3) add_nonneg_nonneg add_nonneg_pos add_pos_nonneg leI less_add_same_cancel1 less_numeral_extra(1) min.cobounded1 min_def zero_less_one_class.zero_le_one)
    apply (force simp add: min_def)
    done
   apply (metis Rep_perm_eq_iff add_cancel_left_left dperm_wperm_plus(1) dperm_wperm_plus(2) less_numeral_extra(3))
  (* subgoal *)
  apply (rule_tac iffI)
   apply (rule conjI, force simp add: less_perm_def)
   apply (simp add: less_perm_def less_eq_perm_def perm_eq_iff disjoint_perm_def dperm.rep_eq wperm.rep_eq)
   apply (subst ex_perm_Rep_iff)
   apply clarsimp
   apply (rule_tac x=\<open>fst (Rep_perm b) - fst (Rep_perm a)\<close> in exI)
   apply clarsimp
   apply (rule conjI, metis Rep_perm_constraints add_increasing2 diff_le_eq fst_conv)
   apply (rule_tac x=\<open>snd (Rep_perm b) - snd (Rep_perm a)\<close> in exI)
   apply clarsimp
   apply (rule conjI, metis Rep_perm_eq_iff diff_0_right diff_mono)
   apply (intro conjI)
      apply fastforce
     apply (metis Rep_perm_eq_iff)
    apply (metis Rep_perm_eq_iff)
   apply (metis Rep_perm_eq_iff min.absorb2 prod_eq_decompose(2))
  apply (clarsimp simp add: less_perm_def less_eq_perm_def perm_eq_iff disjoint_perm_def dperm.rep_eq wperm.rep_eq)
  apply (metis Rep_perm_eq_iff add_cancel_right_right nle_le prod.collapse)
    (* done *)
  done

end

section \<open> Deallocation-permission Heaps \<close>

typedef ('a,'b) dheap = \<open>UNIV::(perm,'a,'b) pheap set\<close>
  morphisms from_dheap to_dheap
  by blast

setup_lifting type_definition_dheap

abbreviation \<open>dom_dheap \<equiv> dom_pheap \<circ> from_dheap\<close>

abbreviation app_dheap :: \<open>('a,'b) dheap \<Rightarrow> 'a \<rightharpoonup> perm \<times> 'b\<close> (infix \<open>\<bullet>d\<close> 990)where
  \<open>app_dheap \<equiv> app_pheap \<circ> from_dheap\<close>

lemma ex_dheap_iff:
  \<open>(\<exists>h. P h) \<longleftrightarrow> (\<exists>ph. P (to_dheap ph))\<close>
  by (metis to_dheap_cases)

lemma disjoint_pheap_Some_bounded_oneD:
  \<open>a ## b \<Longrightarrow> a \<bullet> x = Some (pa,va) \<Longrightarrow> b \<bullet> x = Some (pb,vb) \<Longrightarrow> wperm pa + wperm pb \<le> 1\<close>
  by (simp add: disjoint_pheap_def disjoint_perm_def disjoint_set_pheap_def split: prod.splits)

section \<open> The stable and zero domains \<close>

definition stabledom :: \<open>('a,'b) dheap \<Rightarrow> 'a set\<close> where
  \<open>stabledom a \<equiv> {x. \<exists>p v. from_dheap a \<bullet> x = Some (p,v) \<and> (\<exists>da wa. Rep_perm p = (da,wa) \<and> wa > 0)}\<close>

definition zerodom :: \<open>('a,'b) dheap \<Rightarrow> 'a set\<close> where
  \<open>zerodom a \<equiv> {x. \<exists>p v. from_dheap a \<bullet> x = Some (p,v) \<and> (\<exists>da wa. Rep_perm p = (da,wa) \<and> wa = 0)}\<close>

lemma dom_pheap_sep:
  \<open>dom_dheap a = stabledom a \<union> zerodom a\<close>
  using Rep_perm_constraints
  by (fastforce simp add: dom_pheap_def stabledom_def zerodom_def dom_def set_eq_iff)

lemma stabledom_subseteq_dom_pheap:
  \<open>stabledom a \<subseteq> dom_dheap a\<close>
  using dom_pheap_sep by fastforce


instantiation dheap :: (type,type) stable_sep_alg
begin

lift_definition stableres_dheap :: \<open>('a,'b) dheap \<Rightarrow> ('a,'b) dheap\<close> is
  \<open>\<lambda>a x. Option.bind (a x) (\<lambda>(p,v). if dperm p \<noteq> 0 \<and> wperm p > 0 then Some (p,v) else None)\<close>
  by (force intro: rev_finite_subset simp add: dom_def rev_finite_subset_Collect
      Option.bind_eq_Some_conv)

lemma app_stableres_dheap[simp]:
  \<open>stableres a \<bullet> x =
    Option.bind (a \<bullet> x) (\<lambda>(p,v). if dperm p \<noteq> 0 \<and> wperm p > 0 then Some (p,v) else None)\<close>
  using stableres_dheap.rep_eq by auto

instance
  apply standard
      apply (rule_tac x=\<open>a |`\<^sub>d (- dom_pheap b)\<close> in exI)
      apply (simp add: disjoint_dom_pheap)
  subgoal sorry
     apply (clarsimp simp add: less_eq_dheap_def disjoint_dheap_def' split: option.splits)
     apply (drule_tac x=x in spec)
     apply (meson add_nonneg_eq_0_iff add_nonneg_pos add_strict_increasing dperm_wperm_constraints(1) dperm_wperm_constraints(3) le_plus le_plus2)
    apply (simp add: dheap_eq_iff split: Option.bind_split)
   apply (simp add: less_eq_dheap_def split: Option.bind_split)
    (* subgoal *)
  apply (clarsimp simp add: less_eq_dheap_def)
  apply (drule_tac x=x in spec)+
  apply (clarsimp simp add: bind_eq_Some_conv plus_perm_eq_Some_iff split: if_splits)
  apply (case_tac \<open>a \<bullet> x\<close>)
   apply clarsimp
(* done *)
  sorry

end

(*
lift_definition unstableres :: \<open>('a,'b) dheap \<Rightarrow> ('a,'b) dheap\<close> is
  \<open>\<lambda>a x. Option.bind (a x) (\<lambda>(p,v). if wperm p = 0 then Some (p,v) else None)\<close>
  by (force intro: rev_finite_subset simp add: dom_def rev_finite_subset_Collect bind_eq_Some_conv)

lemma stable_unstableres_disjoint:
  \<open>stableres a ## unstableres a\<close>
  by (clarsimp simp add: disjoint_dheap_def' unstableres_def not_less
      bind_eq_Some_conv not_le_imp_less)

lemma add_stable_unstableres:
  \<open>stableres a + unstableres a = a\<close>
  by (simp add: dheap_eq_iff unstableres_def not_less dperm_wperm_constraints_complex
      split: option.splits prod.splits)
*)

lemma stable_le_mono:
  fixes a b :: \<open>('a,'b) dheap\<close>
  shows \<open>a \<le> b \<Longrightarrow> stableres a \<le> stableres b\<close>
  apply (clarsimp simp add: less_eq_dheap_def bind_eq_Some_conv)
  apply (drule_tac x=x in spec)
  oops

subsection \<open>stabledom simps\<close>

lemma restrict_stabledom_eq[simp]:
  \<open>stabledom (a |`\<^sub>d A) = stabledom a \<inter> A\<close>
  by (simp add: stabledom_def set_eq_iff)

lemma seq_stabledom_eq[simp]:
  \<open>stabledom (a \<triangleright> b) = stabledom a \<union> (stabledom b - zerodom a)\<close>
  using Rep_perm_constraints
  by (fastforce simp add: stabledom_def set_eq_iff zerodom_def less_eq_rat_def split: option.splits)

lemma stabledom_plus[simp]:
  \<open>stabledom (a + b) = stabledom a \<union> stabledom b\<close>
  apply (clarsimp simp add: stabledom_def set_eq_iff plus_perm_eq_Some_iff)
  apply (case_tac \<open>app_dheap a x\<close>)
   apply force
  apply (case_tac \<open>app_dheap b x\<close>)
   apply force
  apply clarsimp
  apply (metis Rep_perm_parts add_increasing add_nonneg_eq_0_iff antisym_conv2 dperm_wperm_constraints(3) snd_eqD)
  done

lemma map_stabledom_reduce1:
  \<open>stabledom (map_dheap (map_perm fd fw) fv a) = stabledom (map_dheap (map_perm id fw) fv a)\<close>
  apply (clarsimp simp add: stabledom_def set_eq_iff split: option.splits)
  apply (rule iffI; clarify)
   apply (simp add: map_perm_def less_max_iff_disj split: prod.splits; fail)
  apply (simp add: map_perm_def Rep_perm_constraintsD split: prod.splits; fail)
  done

lemma map_stabledom_reduce2:
  \<open>\<forall>x. x > 0 \<longleftrightarrow> fw x > 0 \<Longrightarrow>
    stabledom (map_dheap (map_perm fd fw) fv a) = stabledom (map_dheap (map_perm fd id) fv a)\<close>
  apply (clarsimp simp add: stabledom_def set_eq_iff split: option.splits)
  apply (rule iffI; clarify)
   apply (simp add: map_perm_def less_max_iff_disj split: prod.splits; fail)
  apply (simp add: map_perm_def Rep_perm_constraintsD split: prod.splits; fail)
  done

lemma map_stabledom_permid_eq[simp]:
  \<open>stabledom (map_dheap id fv a) = stabledom a\<close>
  by (simp add: stabledom_def set_eq_iff split: option.splits)

lemma map_stabledom_perm_mult_eq[simp]:
  \<open>k > 0 \<Longrightarrow>
    stabledom (map_dheap (map_perm (\<lambda>x. x * k) fs) fv a) =
      stabledom (map_dheap (map_perm id fs) fv a)\<close>
  \<open>k > 0 \<Longrightarrow>
    stabledom (map_dheap (map_perm (\<lambda>x. x * k) fw) fv a) =
      stabledom (map_dheap (map_perm id fw) fv a)\<close>
  using map_stabledom_reduce1[of \<open>\<lambda>x. x * k\<close>] map_stabledom_reduce2[of \<open>\<lambda>x. x * k\<close>]
  by (force simp add: zero_less_mult_iff)+

lemma map_stabledom_perm_frac_eq[simp]:
  \<open>k > 0 \<Longrightarrow>
    stabledom (map_dheap (map_perm (\<lambda>x. x / k) fs) fv a) =
      stabledom (map_dheap (map_perm id fs) fv a)\<close>
  \<open>k > 0 \<Longrightarrow>
    stabledom (map_dheap (map_perm fd (\<lambda>x. x / k)) fv a) =
      stabledom (map_dheap (map_perm fd id) fv a)\<close>
  using map_stabledom_reduce1[of \<open>\<lambda>x. x / k\<close>] map_stabledom_reduce2[of \<open>\<lambda>x. x / k\<close>]
  by (force simp add: zero_less_divide_iff)+

subsection \<open>zerodom simps\<close>

lemma restrict_zerodom_eq[simp]:
  \<open>zerodom (a |`\<^sub>d A) = zerodom a \<inter> A\<close>
  by (simp add: zerodom_def set_eq_iff)

lemma seq_zerodom_eq[simp]:
  \<open>zerodom (a \<triangleright> b) = zerodom a \<union> (zerodom b - stabledom a)\<close>
  using Rep_perm_constraints
  by (fastforce simp add: stabledom_def set_eq_iff zerodom_def not_less split: option.splits)

lemma map_zerodom_reduce1:
  \<open>zerodom (map_dheap (map_perm fd fw) fv a) = zerodom (map_dheap (map_perm id fw) fv a)\<close>
  apply (clarsimp simp add: zerodom_def set_eq_iff split: option.splits)
  apply (rule iffI; clarify)
   apply (simp add: map_perm_def less_max_iff_disj split: prod.splits; fail)
  apply (simp add: map_perm_def Rep_perm_constraintsD split: prod.splits; fail)
  done

lemma map_zerodom_reduce2:
  \<open>\<forall>x. x > 0 \<longleftrightarrow> fw x > 0 \<Longrightarrow>
    zerodom (map_dheap (map_perm fd fw) fv a) = zerodom (map_dheap (map_perm fd id) fv a)\<close>
  apply (clarsimp simp add: zerodom_def set_eq_iff split: option.splits)
  apply (rule iffI; clarify)
   apply (simp add: map_perm_def max_def min_def split: prod.splits if_splits)
    apply (metis dperm_wperm_constraints_complex(2) leI not_one_le_zero order_less_irrefl snd_conv wperm.rep_eq)
   apply (simp add: less_eq_rat_def; fail)
  apply (simp add: map_perm_def Rep_perm_constraintsD max_def split: prod.splits if_splits)
  apply (simp add: order.order_iff_strict; fail)
  done

lemma map_zerodom_permid_eq[simp]:
  \<open>zerodom (map_dheap id fv a) = zerodom a\<close>
  by (simp add: zerodom_def set_eq_iff split: option.splits)

lemma map_zerodom_perm_mult_eq[simp]:
  \<open>k > 0 \<Longrightarrow> zerodom (map_dheap (map_perm (\<lambda>x. x * k) fw) fv a) = zerodom (map_dheap (map_perm id fw) fv a)\<close>
  \<open>k > 0 \<Longrightarrow> zerodom (map_dheap (map_perm fd (\<lambda>x. x * k)) fv a) = zerodom (map_dheap (map_perm fd id) fv a)\<close>
  using map_zerodom_reduce1[of \<open>\<lambda>x. x * k\<close>] map_zerodom_reduce2[of \<open>\<lambda>x. x * k\<close>]
  by (force simp add: zero_less_mult_iff)+

lemma map_zerodom_perm_frac_eq[simp]:
  \<open>k > 0 \<Longrightarrow> zerodom (map_dheap (map_perm (\<lambda>x. x / k) fw) fv a) = zerodom (map_dheap (map_perm id fw) fv a)\<close>
  \<open>k > 0 \<Longrightarrow> zerodom (map_dheap (map_perm fd (\<lambda>x. x / k)) fv a) = zerodom (map_dheap (map_perm fd id) fv a)\<close>
  using map_zerodom_reduce1[of \<open>\<lambda>x. x / k\<close>] map_zerodom_reduce2[of \<open>\<lambda>x. x / k\<close>]
  by (force simp add: zero_less_divide_iff)+

subsection \<open> Halve permissions in a set \<close>

text \<open>Halve the permissions in a given set\<close>
definition halve_dheap :: \<open>('a,'b) dheap \<Rightarrow> 'a set \<Rightarrow> ('a,'b) dheap\<close> where
  \<open>halve_dheap a A \<equiv> map_dheap (map_perm (\<lambda>c. c/2) (\<lambda>c. c/2)) id (a |`\<^sub>d A) \<triangleright> a\<close>

lemma halve_dheap_app_eq:
  \<open>halve_dheap a A \<bullet> x = (if x \<in> A then map_dheap (map_perm (\<lambda>x. x / 2) (\<lambda>x. x / 2)) id a \<bullet> x else a \<bullet> x)\<close>
  by (simp add: halve_dheap_def split: option.splits)

lemma halve_dheap_subheap:
  \<open>halve_dheap a A \<le> a\<close>
  apply (clarsimp simp add: less_eq_dheap_def halve_dheap_app_eq zero_le_mult_iff
      less_eq_perm_def map_perm_def split: option.splits prod.splits)
  apply (rename_tac x b pb wb v p2)
  apply (rule_tac x=b in exI)
  apply (case_tac \<open>2 \<le> wb\<close>)
   apply (meson Rep_perm_constraintsD(4) dual_order.trans numeral_le_one_iff semiring_norm(69))
  apply (case_tac \<open>0 \<le> wb\<close>)
   apply clarsimp
  oops

lemma stabledom_halve_dheap_eq[simp]:
  \<open>stabledom (halve_dheap a A) = stabledom a\<close>
  by (force simp add: halve_dheap_def)

section \<open> Stable rely-relation \<close>

definition stablerel :: \<open>('a,'b) dheap \<Rightarrow> ('a,'b) dheap \<Rightarrow> bool\<close> where
  \<open>stablerel a b \<equiv> \<forall>x v p.
    a \<bullet> x = Some (p,v) \<longrightarrow> 0 < wperm p \<longrightarrow> (\<exists>p'\<ge>p. b \<bullet> x = Some (p',v) \<and> 0 < wperm p')\<close>


lemma stablerel_iff_stableres_le: \<open>stablerel a b \<longleftrightarrow> stableres a \<le> stableres b\<close>
  sorry
(*
  by (force simp add: stablerel_def stableres_dheap_def less_eq_dheap_def
      bind_eq_Some_conv split: if_splits)
*)

lemma stablerel_refl:
  \<open>stablerel a a\<close>
  by (force simp add: stablerel_iff_stableres_le)

lemma stablerel_trans:
  \<open>stablerel a b \<Longrightarrow> stablerel b c \<Longrightarrow> stablerel a c\<close>
  by (force simp add: stablerel_iff_stableres_le)

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

lemma
  fixes a b :: \<open>('a,'b) dheap\<close>
  shows \<open> x = stableres (a + b) \<Longrightarrow>
          y1 = stableres a \<Longrightarrow>
          y2 = stableres b \<Longrightarrow>
          y = y1 + y2 \<Longrightarrow>
          x = y\<close>
  nitpick[card 'a=1, card 'b=1]
  oops

lemma stablerel_add:
  \<open>a1 ## a2 \<Longrightarrow> b1 ## b2 \<Longrightarrow> stablerel a1 b1 \<Longrightarrow> stablerel a2 b2 \<Longrightarrow> stablerel (a1 + a2) (b1 + b2)\<close>
  apply (clarsimp simp add: stablerel_iff_stableres_le le_iff_sepadd)
  sorry

lemma stablerel_subheap:
  \<open>stablerel a b \<Longrightarrow> a' \<le> a \<Longrightarrow> b' \<le> b \<Longrightarrow> stabledom a' \<subseteq> stabledom b' \<Longrightarrow> stablerel a' b'\<close>
  apply (clarsimp simp add: stablerel_def stabledom_def less_eq_dheap_def
      less_eq_perm_def subset_iff wperm_def split: prod.splits)
  oops

lemma stablerel_impl_subseteq_stabledom:
  \<open>stablerel a b \<Longrightarrow> stabledom a \<subseteq> stabledom b\<close>
  by (clarsimp simp add: stablerel_def stabledom_def wperm_def, metis prod.collapse snd_conv)

lemma stablerel_additivity_of_update:
  assumes
    \<open>a1 ## a2\<close>
    \<open>stablerel (a1 + a2) b\<close>
  shows
    \<open>\<exists>b1 b2. b1 ## b2 \<and> b = b1 + b2 \<and> stablerel a1 b1 \<and> stablerel a2 b2\<close>
proof -
  let ?bnew = \<open>dom_pheap b - stabledom a1 - stabledom a2\<close>
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
    oops
    apply (rule_tac x=\<open>?b1\<close> in exI, rule_tac x=\<open>?b2\<close> in exI)
    apply (intro conjI)
       apply (clarsimp simp add: disjoint_dheap_def disjoint_set_dheap_def halve_dheap_app_eq)
       apply (intro conjI impI; force simp add: map_perm_eq disjoint_perm_def
        linordered_field_min_bounded_divide_by order.trans[OF wperm_constraints(2) one_le_numeral]
        split: prod.splits)
      apply (force simp add: halve_dheap_def map_perm_def dom_pheap_def plus_perm_def
          dheap_eq_iff dom_def Rep_perm_constraintsD
          order.trans[OF Rep_perm_constraintsD(3) one_le_numeral]
          linordered_field_min_bounded_divide_by eq_Abs_perm_iff mult.commute
          split: option.splits prod.splits)
    subgoal
      apply (rule stablerel_subheap, assumption)
        apply (force simp add: le_plus)
       apply (clarsimp simp add: halve_dheap_def less_eq_dheap_def order_less_imp_le
          split: option.splits; fail)
      apply force
      done
    subgoal
      apply (rule stablerel_subheap, blast)
        apply (force simp add: le_plus2)
       apply (clarsimp simp add: halve_dheap_def less_eq_dheap_def Rep_perm_constraintsD
          order_less_imp_le split: option.splits; fail)
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
*)

end