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

subsection \<open> full_perm \<close>

lift_definition full_perm :: \<open>perm\<close> is \<open>(1,1)\<close>
  using zero_le_one zero_less_two by blast

lemma full_perm_parts_eq[simp]:
  \<open>dperm full_perm = 1\<close>
  \<open>wperm full_perm = 1\<close>
  by (simp add: full_perm_def dperm.rep_eq wperm.rep_eq)+

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

instance perm :: disjoint_parts_perm_alg
  apply standard
  apply (clarsimp simp add: disjoint_perm_def)
  apply (rule conjI)
  oops

instantiation perm :: halving_perm_alg
begin

lift_definition half_perm :: \<open>perm \<Rightarrow> perm\<close> is
  \<open>\<lambda>(a,b). (a/2,b/2)\<close>
  by fastforce

lemma dperm_half[simp]:
  \<open>dperm (half p) = dperm p / 2\<close>
  by (simp add: dperm.rep_eq half_perm.rep_eq split: prod.splits)

lemma wperm_half[simp]:
  \<open>wperm (half p) = wperm p / 2\<close>
  by (simp add: wperm.rep_eq half_perm.rep_eq split: prod.splits)

instance
  apply standard
   apply (simp add: perm_eq_iff Rep_perm_parts dperm_wperm_constraints(2,4))
   apply (simp add: disjoint_perm_def dperm_wperm_constraints(2,4))
  apply (simp add: disjoint_perm_def dperm_wperm_constraints(2,4))
  done

end

subsection \<open> Type of deallocation permissions \<close>

definition is_full_perm :: \<open>perm \<Rightarrow> bool\<close> where
  \<open>is_full_perm p \<equiv> dperm p = 1 \<and> wperm p = 1\<close>

definition is_write_perm :: \<open>perm \<Rightarrow> bool\<close> where
  \<open>is_write_perm p \<equiv> dperm p = 1 \<and> wperm p > 0 \<or> dperm p > 0 \<and> wperm p = 1\<close>

definition is_stable_read_perm :: \<open>perm \<Rightarrow> bool\<close> where
  \<open>is_stable_read_perm p \<equiv> wperm p > 0 \<and> dperm p > 0\<close>

lemma full_perm_conflict:
  \<open>is_full_perm p1 \<Longrightarrow> \<not> p1 ## p2\<close>
  apply (clarsimp simp add: is_full_perm_def less_eq_perm_def disjoint_perm_def
      dperm_plus_unrestricted wperm_plus_unrestricted)
  apply (metis add_0 dperm_wperm_constraints(5) dperm_wperm_constraints_complex(1) dperm_wperm_constraints_complex(3) order_less_irrefl)
  done

lemma write_write_perm_conflict:
  \<open>is_write_perm p1 \<Longrightarrow> is_write_perm p2 \<Longrightarrow> \<not> p1 ## p2\<close>
  by (force simp add: is_write_perm_def is_stable_read_perm_def less_eq_perm_def
      disjoint_perm_def dperm_plus_unrestricted wperm_plus_unrestricted)

lemma write_stable_read_perm_conflict:
  \<open>is_write_perm p1 \<Longrightarrow> is_stable_read_perm p2 \<Longrightarrow> \<not> p1 ## p2\<close>
  by (clarsimp simp add: is_write_perm_def is_stable_read_perm_def less_eq_perm_def
      disjoint_perm_def dperm_plus_unrestricted wperm_plus_unrestricted)

definition stable_perm :: \<open>perm \<Rightarrow> bool\<close> where
  \<open>stable_perm p \<equiv> dperm p > 0 \<and> wperm p > 0\<close>

lemma full_perm_is_stable:
  \<open>is_full_perm p \<Longrightarrow> stable_perm p\<close>
  by (clarsimp simp add: is_full_perm_def stable_perm_def)

lemma write_perm_is_stable:
  \<open>is_write_perm p \<Longrightarrow> stable_perm p\<close>
  by (force simp add: is_write_perm_def stable_perm_def)

lemma stable_read_perm_is_stable:
  \<open>is_stable_read_perm p \<Longrightarrow> stable_perm p\<close>
  by (clarsimp simp add: is_stable_read_perm_def stable_perm_def)

section \<open> Deallocation-permission Heaps \<close>

typedef ('a,'b) dheap = \<open>UNIV::(perm,'a,'b) pheap set\<close>
  by blast

abbreviation \<open>dom_dheap h \<equiv> dom_pheap (Rep_dheap h)\<close>

abbreviation app_dheap :: \<open>('a,'b) dheap \<Rightarrow> 'a \<rightharpoonup> perm \<times> 'b\<close> (infix \<open>\<bullet>d\<close> 990) where
  \<open>app_dheap h \<equiv> app_pheap (Rep_dheap h)\<close>

abbreviation upd_dheap :: \<open>('a,'b) dheap \<Rightarrow> 'a \<Rightarrow> perm \<times> 'b \<Rightarrow> ('a,'b) dheap\<close> where
  \<open>upd_dheap h x pv \<equiv> Abs_dheap ((Rep_dheap h)(x \<mapsto>p pv))\<close>

abbreviation \<open>dheap_empty \<equiv> Abs_dheap pheap_empty\<close>

nonterminal dmaplets and dmaplet

syntax
  "_dmaplet"  :: "['a, 'a] \<Rightarrow> dmaplet"             ("_ /\<mapsto>d/ _")
  "_dmaplets" :: "['a, 'a] \<Rightarrow> pmaplet"             ("_ /[\<mapsto>d]/ _")
  ""         :: "dmaplet \<Rightarrow> dmaplets"             ("_")
  "_dMaplets" :: "[dmaplet, dmaplets] \<Rightarrow> dmaplets" ("_,/ _")
  "_dMapUpd"  :: "['a \<rightharpoonup> 'b, dmaplets] \<Rightarrow> 'a \<rightharpoonup> 'b" ("_/'(_')" [900, 0] 900)
  "_dMap"     :: "dmaplets \<Rightarrow> 'a \<rightharpoonup> 'b"            ("(1[_])")

translations
  "_dMapUpd m (_dMaplets xy ms)"  \<rightleftharpoons> "_dMapUpd (_dMapUpd m xy) ms"
  "_dMapUpd m (_dmaplet  x y)"    \<rightleftharpoons> "CONST upd_dheap m x y"
  "_dMap ms"                     \<rightleftharpoons> "_dMapUpd (CONST dheap_empty) ms"
  "_dMap (_dMaplets ms1 ms2)"     \<leftharpoondown> "_dMapUpd (_dMap ms1) ms2"
  "_dMaplets ms1 (_dMaplets ms2 ms3)" \<leftharpoondown> "_dMaplets (_dMaplets ms1 ms2) ms3"

abbreviation restrict_dheap :: \<open>('a,'b) dheap \<Rightarrow> 'a set \<Rightarrow> ('a,'b) dheap\<close>
  (infixr \<open>|`d\<close> 110) where
  \<open>m |`d A \<equiv> Abs_dheap (Rep_dheap m |`p A)\<close>


abbreviation \<open>to_dheap h \<equiv> Abs_dheap (Abs_pheap h)\<close>

lemma dheap_eq_iff:
  \<open>h1 = h2 \<longleftrightarrow> (\<forall>x. h1 \<bullet>d x = h2 \<bullet>d x)\<close>
  using Rep_dheap_inject pheap_ext by auto

lemma ex_Abs_dheap_iff:
  \<open>(\<exists>h. P h) \<longleftrightarrow> (\<exists>ph. P (Abs_dheap ph))\<close>
  by (metis Abs_dheap_cases)

lemma ex_from_dheap_iff:
  \<open>(\<exists>h. P (Rep_dheap h)) \<longleftrightarrow> (\<exists>h. P h)\<close>
  by (metis UNIV_I Rep_dheap_cases)

lemma Abs_dheap_inverse'[simp]:
  \<open>Rep_dheap (Abs_dheap a) = a\<close>
  by (simp add: dheap.Abs_dheap_inverse)

declare dheap.Rep_dheap_inverse[simp] Rep_dheap_inject[simp] Abs_dheap_inject[simp]

lemma Abs_dheap_eq_iff[simp]:
  \<open>Abs_dheap a = b \<longleftrightarrow> a = Rep_dheap b\<close>
  by fastforce

lemma eq_Abs_dheap_iff[simp]:
  \<open>b = Abs_dheap a \<longleftrightarrow> Rep_dheap b = a\<close>
  by fastforce

lemma disjoint_pheap_Some_bounded_oneD:
  \<open>a ## b \<Longrightarrow> a \<bullet> x = Some (pa,va) \<Longrightarrow> b \<bullet> x = Some (pb,vb) \<Longrightarrow> wperm pa + wperm pb \<le> 1\<close>
  by (simp add: disjoint_pheap_def disjoint_perm_def disjoint_set_pheap_def split: prod.splits)

section \<open> The stable and zero domains \<close>

definition stabledom :: \<open>('a,'b) dheap \<Rightarrow> 'a set\<close> where
  \<open>stabledom a \<equiv> {x. \<exists>p v. a \<bullet>d x = Some (p,v) \<and> (\<exists>da wa. Rep_perm p = (da,wa) \<and> wa > 0)}\<close>

definition zerodom :: \<open>('a,'b) dheap \<Rightarrow> 'a set\<close> where
  \<open>zerodom a \<equiv> {x. \<exists>p v. a \<bullet>d x = Some (p,v) \<and> (\<exists>da wa. Rep_perm p = (da,wa) \<and> wa = 0)}\<close>

lemma dom_pheap_sep:
  \<open>dom_dheap a = stabledom a \<union> zerodom a\<close>
  using Rep_perm_constraints
  by (fastforce simp add: dom_pheap_def stabledom_def zerodom_def dom_def set_eq_iff)

lemma stabledom_subseteq_dom_pheap:
  \<open>stabledom a \<subseteq> dom_dheap a\<close>
  using dom_pheap_sep by fastforce

instantiation dheap :: (type, type) monoid_seq
begin

definition seq_dheap :: \<open>('a,'b) dheap \<Rightarrow> ('a,'b) dheap \<Rightarrow> ('a,'b) dheap\<close> where
  \<open>seq_dheap a b \<equiv> Abs_dheap (Rep_dheap a \<triangleright> Rep_dheap b)\<close>

definition skip_dheap :: \<open>('a,'b) dheap\<close> where
  \<open>skip_dheap \<equiv> Abs_dheap \<I>\<close>

instance
  by standard (simp add: seq_dheap_def seq_assoc skip_dheap_def)+

end

instantiation dheap :: (type,type) sep_alg
begin

definition plus_dheap :: \<open>('a,'b) dheap \<Rightarrow> ('a,'b) dheap \<Rightarrow> ('a,'b) dheap\<close> where
  \<open>plus_dheap a b \<equiv> Abs_dheap (Rep_dheap a + Rep_dheap b)\<close>

definition bot_dheap :: \<open>('a,'b) dheap\<close> where
  \<open>bot_dheap \<equiv> Abs_dheap bot\<close>
definition zero_dheap :: \<open>('a,'b) dheap\<close> where
  \<open>zero_dheap \<equiv> Abs_dheap 0\<close>

definition less_eq_dheap :: \<open>('a,'b) dheap \<Rightarrow> ('a,'b) dheap \<Rightarrow> bool\<close> where
  \<open>less_eq_dheap a b \<equiv> Rep_dheap a \<le> Rep_dheap b\<close>
lemmas less_eq_dheap_def' = less_eq_dheap_def less_eq_pheap_def

definition less_dheap :: \<open>('a,'b) dheap \<Rightarrow> ('a,'b) dheap \<Rightarrow> bool\<close> where
  \<open>less_dheap a b \<equiv> Rep_dheap a < Rep_dheap b\<close>
definition disjoint_dheap :: \<open>('a,'b) dheap \<Rightarrow> ('a,'b) dheap \<Rightarrow> bool\<close> where
  \<open>disjoint_dheap a b \<equiv> Rep_dheap a ## Rep_dheap b\<close>
lemmas disjoint_dheap_def' = disjoint_dheap_def disjoint_pheap_def'

lemma app_add_dheap[simp]:
  \<open>(a + b) \<bullet>d x = a \<bullet>d x \<oplus>\<^sub>p b \<bullet>d x\<close>
  by (simp add: plus_dheap_def)

lemma Rep_dheap_zero[simp]:
  \<open>Rep_dheap (0::('a,'b) dheap) = 0\<close>
  by (simp add: zero_dheap_def)

instance
  apply standard
                apply (simp add: less_dheap_def less_eq_dheap_def less_le_not_le)
               apply (simp add: less_eq_dheap_def)
              apply (simp add: less_eq_dheap_def)
             apply (simp add: less_eq_dheap_def)
            apply (simp add: bot_dheap_def less_eq_dheap_def)
           apply (simp add: zero_dheap_def disjoint_dheap_def)
          apply (simp add: zero_dheap_def disjoint_dheap_def)
         apply (simp add: zero_dheap_def plus_dheap_def)
         apply (force simp add: disjoint_dheap_def plus_dheap_def partial_add_assoc)
        apply (force simp add: disjoint_dheap_def plus_dheap_def intro: partial_add_commute)
       apply (simp add: disjoint_dheap_def disjoint_symm)
      apply (force simp add: disjoint_dheap_def plus_dheap_def intro: disjoint_add_rightL)
     apply (force simp add: disjoint_dheap_def plus_dheap_def intro: disjoint_add_right_commute)
    apply (force simp add: disjoint_dheap_def plus_dheap_def intro: positivity)
   apply (force simp add: less_dheap_def less_eq_dheap_def plus_dheap_def disjoint_dheap_def
      less_iff_sepadd ex_Abs_dheap_iff)
  apply (force simp add: zero_dheap_def plus_dheap_def)
  done

end

instantiation dheap :: (type,type) halving_sep_alg
begin

definition half_dheap :: \<open>('a,'b) dheap \<Rightarrow> ('a,'b) dheap\<close> where
  \<open>half_dheap a \<equiv> Abs_dheap (half (Rep_dheap a))\<close>

instance
  apply standard
  apply (simp add: half_additive_split half_dheap_def plus_dheap_def)
  apply (simp add: disjoint_dheap_def half_dheap_def half_self_disjoint)
  done

end

instantiation dheap :: (type,type) stable_sep_alg
begin

definition stableres_dheap :: \<open>('a,'b) dheap \<Rightarrow> ('a,'b) dheap\<close> where
  \<open>stableres_dheap a \<equiv>
    to_dheap (\<lambda>x. Option.bind (a \<bullet>d x) (\<lambda>(p,v). if stable_perm p then Some (p,v) else None))\<close>

lemma stableres_dheap_app[simp]:
  fixes a :: \<open>('a,'b) dheap\<close>
  shows
    \<open>stableres a \<bullet>d x = Option.bind (a \<bullet>d x) (\<lambda>(p,v). if stable_perm p then Some (p,v) else None)\<close>
  by (simp add: stableres_dheap_def)

instance
  apply standard
    (* subgoal *)
    apply (clarsimp simp add: less_eq_dheap_def' disjoint_dheap_def' split: option.splits)
    apply (drule_tac x=x in spec)
    apply (case_tac \<open>a \<bullet>d x\<close>, force)
    apply (case_tac \<open>b \<bullet>d x\<close>, force)
    apply (force simp add: dperm_wperm_constraints(1,3) add_nonneg_eq_0_iff add_nonneg_pos
      add_pos_nonneg partial_le_plus partial_le_plus2 stable_perm_def)
    (* done *)
   apply (force simp add: dheap_eq_iff split: Option.bind_splits)
  apply (force simp add: less_eq_dheap_def' split: Option.bind_splits)
  done

end

subsection \<open>stabledom simps\<close>
(*
lemma restrict_stabledom_eq[simp]:
  \<open>stabledom (a |`\<^sub>p A) = stabledom a \<inter> A\<close>
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
  \<open>zerodom (a |`\<^sub>p A) = zerodom a \<inter> A\<close>
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
*)

end