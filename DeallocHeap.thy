theory DeallocHeap
  imports Stabilisation HOL.Rat
begin

section \<open>Permission Heaps with unstable reads and deallocation\<close>

typedef perm = \<open>{(d,w)::rat \<times> rat|d w. (w = 1 \<longrightarrow> 0 \<le> d) \<and> (w = 0 \<longrightarrow> d \<le> 0) \<and> (0 \<le> w \<and> w \<le> 1)}\<close>
  using zero_le_one by blast
setup_lifting type_definition_perm

lift_definition dperm :: \<open>perm \<Rightarrow> rat\<close> is \<open>fst\<close> .
lift_definition wperm :: \<open>perm \<Rightarrow> rat\<close> is \<open>snd\<close> .

lemmas Rep_perm_constraints = perm.Rep_perm[simplified mem_Collect_eq]

lemma Rep_perm_eq_iff:
  \<open>Rep_perm a = x \<longleftrightarrow>
    fst x = dperm a \<and> snd x = wperm a \<and>
    (wperm a = 1 \<longrightarrow> 0 \<le> dperm a) \<and>
    (wperm a = 0 \<longrightarrow> dperm a \<le> 0) \<and>
    0 \<le> wperm a \<and> wperm a \<le> 1\<close>
  by (metis Rep_perm_constraints dperm.rep_eq wperm.rep_eq fst_conv snd_conv prod.collapse)

lemma Rep_perm_constraintsD:
  \<open>Rep_perm a = (d,w) \<Longrightarrow> w = 1 \<Longrightarrow> 0 \<le> d\<close>
  \<open>Rep_perm a = (d,w) \<Longrightarrow> w = 0 \<Longrightarrow> d \<le> 0\<close>
  \<open>Rep_perm a = (d,w) \<Longrightarrow> 0 \<le> w\<close>
  \<open>Rep_perm a = (d,w) \<Longrightarrow> w \<le> 1\<close>
  using Rep_perm_constraints[of a]
  by simp+

lemma dperm_wperm_constraints:
  \<open>wperm p = 1 \<Longrightarrow> 0 \<le> dperm p\<close>
  \<open>wperm p = 0 \<Longrightarrow> dperm p \<le> 0\<close>
  \<open>0 \<le> wperm p\<close>
  \<open>wperm p \<le> 1\<close>
  by (metis wperm.rep_eq dperm.rep_eq Rep_perm_constraintsD prod.collapse)+

lemma Rep_perm_constraints_complex:
  \<open>Rep_perm a = (d,w) \<Longrightarrow> w \<ge> 1 \<longleftrightarrow> w = 1\<close>
  \<open>Rep_perm a = (d,w) \<Longrightarrow> w \<le> 0 \<longleftrightarrow> w = 0\<close>
  \<open>Rep_perm b = (db,wb) \<Longrightarrow> Rep_perm a = (da,1 + wb) \<longleftrightarrow> Rep_perm a = (da,1) \<and> wb = 0\<close>
  by (fastforce simp add: Rep_perm_constraintsD order.antisym)+
    (fastforce dest: Rep_perm_constraintsD)

lemma perm_eq_iff:
  \<open>a = b \<longleftrightarrow> wperm a = wperm b \<and> dperm a = dperm b\<close>
  by (metis Rep_perm_inject dperm.rep_eq prod.expand wperm.rep_eq)

lemma eq_Abs_perm_iff:
  \<open>snd a' = 1 \<longrightarrow> 0 \<le> fst a' \<Longrightarrow>
    snd a' = 0 \<longrightarrow> fst a' \<le> 0 \<Longrightarrow>
    0 \<le> snd a' \<Longrightarrow>
    snd a' \<le> 1 \<Longrightarrow>
    a = Abs_perm a' \<longleftrightarrow> Rep_perm a = a'\<close>
  by (rule Abs_perm_inject[of \<open>Rep_perm _\<close>, simplified Rep_perm_inverse])
   (clarsimp simp add: Rep_perm_constraintsD)+

lemma eq_Abs_perm_iff':
  \<open>snd a' = 1 \<longrightarrow> 0 \<le> fst a' \<Longrightarrow>
    snd a' = 0 \<longrightarrow> fst a' \<le> 0 \<Longrightarrow>
    0 \<le> snd a' \<Longrightarrow>
    snd a' \<le> 1 \<Longrightarrow> Abs_perm a' = a \<longleftrightarrow> Rep_perm a = a'\<close>
  by (metis eq_Abs_perm_iff)

lemma ex_perm_Rep_iff:
  \<open>(\<exists>a. P (Rep_perm a)) \<longleftrightarrow>
      (\<exists>a'. (snd a' = 1 \<longrightarrow> 0 \<le> fst a') \<and> (snd a' = 0 \<longrightarrow> fst a' \<le> 0) \<and>
      0 \<le> snd a' \<and> snd a' \<le> 1 \<and> P a')\<close>
  by (metis Rep_perm_eq_iff eq_Abs_perm_iff)

lemma Rep_perm_all_iff_ex:
  \<open>(\<forall>da wa. Rep_perm a = (da, wa) \<longrightarrow> P da wa) \<longleftrightarrow> (\<exists>da wa. Rep_perm a = (da, wa) \<and> P da wa)\<close>
  using Rep_perm_constraints by fastforce

lemma ex_perm_all_components_iff:
  \<open>(\<exists>a. (\<forall>da wa. Rep_perm a = (da, wa) \<longrightarrow> P da wa)) \<longleftrightarrow>
      (\<exists>da wa. (wa = 1 \<longrightarrow> 0 \<le> da) \<and> (wa = 0 \<longrightarrow> da \<le> 0) \<and> 0 \<le> wa \<and> wa \<le> 1 \<and> P da wa)\<close>
  by (simp add: ex_perm_Rep_iff[where P=\<open>\<lambda>x. \<forall>y z. x = f y z \<longrightarrow> P y z\<close> for f])

lemma Abs_perm_wperm_dperm[simp]:
  \<open>w = wperm p \<Longrightarrow> Abs_perm (dperm p, w) = p\<close>
  \<open>d = dperm p \<Longrightarrow> Abs_perm (d, wperm p) = p\<close>
  using Rep_perm_inverse dperm.rep_eq wperm.rep_eq by force+

lemma Abs_perm_inverse'[simp]:
  \<open>y = 1 \<longrightarrow> 0 \<le> x \<Longrightarrow>
    y = 0 \<longrightarrow> x \<le> 0 \<Longrightarrow>
    0 \<le> y \<Longrightarrow>
    y \<le> 1 \<Longrightarrow> Rep_perm (Abs_perm (x,y)) = (x,y)\<close>
  by (clarsimp simp add: Rep_perm_constraintsD Abs_perm_inverse)

lemma Abs_perm_inject':
  \<open>wa = 1 \<longrightarrow> 0 \<le> da \<Longrightarrow> wa = 0 \<longrightarrow> da \<le> 0 \<Longrightarrow> 0 \<le> wa \<Longrightarrow> wa \<le> 1 \<Longrightarrow>
    wb = 1 \<longrightarrow> 0 \<le> db \<Longrightarrow> wb = 0 \<longrightarrow> db \<le> 0 \<Longrightarrow> 0 \<le> wb \<Longrightarrow> wb \<le> 1 \<Longrightarrow>
    (Abs_perm (da,wa) = Abs_perm (db,wb)) = ((da,wa) = (db,wb))\<close>
  by (clarsimp simp add: Abs_perm_inject Sigma_def)


lift_definition map_perm :: \<open>(rat \<Rightarrow> rat) \<Rightarrow> (rat \<Rightarrow> rat) \<Rightarrow> perm \<Rightarrow> perm\<close> is
  \<open>\<lambda>fd fw (d,w).
    (if fw w \<le> 0 then min 0 (fd d) else if fw w \<ge> 1 then max 0 (fd d) else fd d,
      max 0 (min 1 (fw w)))\<close>
  by (clarsimp split: prod.splits)

lemma map_perm_id[simp]:
  \<open>map_perm id id = id\<close>
  by (simp add: map_perm_def fun_eq_iff Rep_perm_eq_iff split: prod.splits)

lemma map_perm_eq:
  \<open>map_perm fd fw a =
    Abs_perm (if fw (wperm a) \<le> 0 then min 0 (fd (dperm a))
      else if fw (wperm a) \<ge> 1 then max 0 (fd (dperm a))
      else fd (dperm a),
      max 0 (min 1 (fw (wperm a))))\<close>
  by (force simp add: map_perm_def dperm_def wperm_def split: prod.splits)

instantiation perm :: sepalg
begin

lift_definition disjoint_perm :: \<open>perm \<Rightarrow> perm \<Rightarrow> bool\<close> is
  \<open>\<lambda>(da,wa) (db,wb). (wa + wb = 1 \<longrightarrow> 0 \<le> da + db) \<and> wa + wb \<le> 1\<close> .

lift_definition bot_perm :: perm is \<open>(0,0)\<close>
  by simp

lemma dperm_wperm_bot[simp]:
  \<open>dperm bot = 0\<close>
  \<open>wperm bot = 0\<close>
  by (simp add: bot_perm_def dperm_def wperm_def)+

lift_definition zero_perm :: \<open>perm\<close> is \<open>(0,0)\<close>
  by simp

lemma dperm_wperm_zero[simp]:
  \<open>dperm 0 = 0\<close>
  \<open>wperm 0 = 0\<close>
  by (simp add: zero_perm_def dperm_def wperm_def)+

lemma helpers:
  \<open>\<And>P Q a b. 0 \<le> a + b \<and> P (max 0 (a + b)) \<and> Q \<longleftrightarrow> 0 \<le> a + b \<and> P (a + b) \<and> Q\<close>
  \<open>\<And>P Q k x. (k::'a::order) \<le> x \<and> P \<and> x \<le> k \<and> Q \<longleftrightarrow> x = k \<and> P \<and> Q\<close>
  by (force simp add: max_def)+

lift_definition less_eq_perm :: \<open>perm \<Rightarrow> perm \<Rightarrow> bool\<close> is
  \<open>\<lambda>(da,wa) (db,wb).
    (wb - wa = 1 \<longrightarrow> da \<le> db) \<and> (wb - wa = 0 \<longrightarrow> db \<le> da) \<and> 0 \<le> wb - wa \<and> wb - wa \<le> 1\<close> .

lemma less_eq_permI[intro]:
  \<open>Rep_perm a = (da,wa) \<Longrightarrow> Rep_perm b = (db,wb) \<Longrightarrow>
    (wb - wa = 1 \<longrightarrow> da \<le> db) \<Longrightarrow> (wb - wa = 0 \<longrightarrow> db \<le> da) \<Longrightarrow> 0 \<le> wb - wa \<Longrightarrow> wb - wa \<le> 1 \<Longrightarrow>
    a \<le> b\<close>
  by (simp add: less_eq_perm.rep_eq)+

lemma less_eq_perm_trans_helpers:
  fixes wb wx dx :: rat (* \<open>'a :: linordered_field\<close>*)
  shows
  \<open>0 \<le> wa \<Longrightarrow> wc \<le> 1 \<Longrightarrow> wb - wa = 1 \<Longrightarrow> wc - wb = 1 \<Longrightarrow> wc - wa = 1\<close>
  \<open>
  0 \<le> wx \<Longrightarrow> 0 \<le> wy \<Longrightarrow>
  wy - wx = 1 \<longrightarrow> dx \<le> dy \<Longrightarrow>
       wy = wx \<longrightarrow> dy \<le> dx \<Longrightarrow>
       wx \<le> wy \<Longrightarrow>
       wy - wx \<le> 1 \<Longrightarrow>
       wz - wy = 1 \<longrightarrow> dy \<le> dz \<Longrightarrow>
       wz = wy \<longrightarrow> dz \<le> dy \<Longrightarrow>
       wy \<le> wz \<Longrightarrow> wz - wy \<le> 1 \<Longrightarrow> wz - wx = 1 \<longleftrightarrow> wz - wy = 1 \<and> wy = wz \<or> wz = wy \<and> wz - wy = 1\<close>
   apply force
  nitpick
oops

definition less_perm :: \<open>perm \<Rightarrow> perm \<Rightarrow> bool\<close> where
  \<open>less_perm x y \<equiv> x \<le> y \<and> \<not> y \<le> x\<close>

lemma less_permI[intro]:
  \<open>Rep_perm a = (da,wa) \<Longrightarrow> Rep_perm b = (db,wb) \<Longrightarrow>
    wa = 1 + wb \<Longrightarrow> da < db \<Longrightarrow> a < b\<close>
  \<open>Rep_perm a = (da,w) \<Longrightarrow> Rep_perm b = (db,w) \<Longrightarrow> db < da \<Longrightarrow> a < b\<close>
  \<open>Rep_perm a = (da,wa) \<Longrightarrow> Rep_perm b = (db,wb) \<Longrightarrow>
    wb - wa = 1 \<longrightarrow> da \<le> db \<Longrightarrow> wb - wa \<le> 1 \<Longrightarrow> wa < wb \<Longrightarrow> a < b\<close>
  by (clarsimp simp add: less_perm_def less_eq_perm.rep_eq Rep_perm_eq_iff split: prod.splits)+ 

lift_definition plus_perm :: \<open>perm \<Rightarrow> perm \<Rightarrow> perm\<close> is
  \<open>\<lambda>(da,wa) (db,wb). ((if 1 \<le> wa + wb then max 0 else id) (da + db), min 1 (wa+wb))\<close>
  by (clarsimp split: prod.splits)

lemma plus_perm_Abs_inverse[simp]:
  \<open>Rep_perm a = (da,wa) \<Longrightarrow>
    Rep_perm b = (db,wb) \<Longrightarrow>
    Rep_perm (Abs_perm ((if 1 \<le> wa + wb then max 0 else id) (da + db), min 1 (wa + wb))) =
      ((if 1 \<le> wa + wb then max 0 else id) (da + db), min 1 (wa + wb))\<close>
  by (clarsimp simp add: Rep_perm_constraintsD Abs_perm_inverse add_nonneg_eq_0_iff
      add_nonpos_nonpos split: prod.splits)

lemma plus_perm_Rep[simp]:
  \<open>Rep_perm (a + b) =
    ((if 1 \<le> wperm a + wperm b then max 0 else id) (dperm a + dperm b), min 1 (wperm a + wperm b))\<close>
  by (simp add: plus_perm.rep_eq Rep_perm_constraintsD
      add_nonneg_eq_0_iff add_nonpos_nonpos dperm.rep_eq wperm.rep_eq split: prod.splits)

lemma dperm_wperm_plus[simp]:
  \<open>a ## b \<Longrightarrow> dperm (a + b) = dperm a + dperm b\<close>
  \<open>a ## b \<Longrightarrow> wperm (a + b) = wperm a + wperm b\<close>
  by (clarsimp simp add: plus_perm_def dperm_def wperm_def disjoint_perm_def split: prod.splits)+


instance
  apply standard
               apply (force simp add: less_perm_def split: prod.splits)
               apply (force simp add: less_eq_perm.rep_eq)
              apply (simp only: less_eq_perm.rep_eq split: prod.splits, clarify)
              apply (clarsimp simp add: less_eq_perm.rep_eq)
  apply (rename_tac dy wy dx wx dz wz)
              apply (intro conjI)
  
thm less_eq_perm_trans_helpers
(*
              apply (clarsimp simp add: Rep_perm_eq_iff diff_eq_eq less_eq_perm.rep_eq
      order.order_iff_strict[of \<open>wperm _\<close> 1], elim disjE; force)
*)
             apply (force simp add: less_eq_perm.rep_eq intro: iffD1[OF Rep_perm_inject])
            apply (clarsimp simp add: less_eq_perm.rep_eq bot_perm_def Rep_perm_constraintsD)
            apply (case_tac \<open>wb = 1\<close>)
             apply (simp add: Rep_perm_constraintsD)
            apply (case_tac \<open>wb = 0\<close>)
             apply (simp add: Rep_perm_constraintsD order_antisym_conv)
             prefer 2
             apply (simp add: Rep_perm_constraintsD order_neq_less_conv)
  
  apply clarsimp
  subgoal sorry
          apply (force simp add: disjoint_perm_def zero_perm_def Rep_perm_constraintsD split: prod.splits)
          apply (force simp add: disjoint_perm_def zero_perm_def Rep_perm_constraintsD split: prod.splits)
        (* partial comm monoid *)
         apply (simp add: perm_eq_iff)
  sledgehammer
  using dperm.rep_eq dperm_wperm_plus(1) dperm_wperm_plus(2) wperm.rep_eq apply force
  oops
         apply (clarsimp simp add: plus_perm.rep_eq Abs_perm_inject Rep_perm_constraintsD
      ordered_comm_monoid_add_add_min_assoc split: prod.splits)
        apply (force simp add: plus_perm_def perm.Abs_perm_inject Rep_perm_constraintsD
      add.commute split: prod.splits)
       apply (simp add: zero_perm_def plus_perm_def perm.Abs_perm_inject Rep_perm_constraintsD
      split: prod.splits, metis Rep_perm_inverse)
    (* separation laws *)
      apply (force simp add: disjoint_perm_def Rep_perm_constraintsD split: prod.splits)
     apply (simp add: disjoint_perm_def plus_perm_def Rep_perm_constraintsD split: prod.splits)
     apply (metis Rep_perm_constraintsD(2) add_le_cancel_left dual_order.trans le_add_same_cancel1)
    apply (force simp add: disjoint_perm_def plus_perm_def Rep_perm_constraintsD)
   apply (clarsimp simp add: disjoint_perm_def plus_perm_def Rep_perm_constraintsD eq_Abs_perm_iff'
      add_nonneg_eq_0_iff Rep_perm_inject[symmetric] split: prod.splits; fail)
  subgoal
    apply (clarsimp simp add: disjoint_perm_def plus_perm_def less_eq_perm.rep_eq Rep_perm_constraintsD split: prod.splits)
    apply (rule iffI; clarify)
    apply (drule iffD1[OF linordered_semidom_ge0_le_iff_add])+
    apply clarsimp
    apply (rename_tac da wa dc wc)
    apply (rule_tac x=\<open>Abs_perm (dc,wc)\<close> in exI)
    apply (force simp add: Rep_perm_constraintsD Rep_perm_constraints_addD eq_Abs_perm_iff)
    apply (force simp add: Rep_perm_all_iff_ex Rep_perm_constraintsD)
    done
  done

lemma map_perm_le_decreasing[simp]:
  \<open>(\<And>x. 0 \<le> x \<Longrightarrow> fd x \<le> x) \<Longrightarrow> (\<And>x. 0 \<le> x \<Longrightarrow> x \<le> 1 \<Longrightarrow> fw x \<le> x) \<Longrightarrow> map_perm fd fw a \<le> a\<close>
  by (force simp add: map_perm_def less_eq_perm.rep_eq Rep_perm_constraintsD min.coboundedI2
      split: prod.splits)

end

typedef ('a,'b) dheap =
  \<open>{h::'a \<rightharpoonup> perm \<times> 'b. finite (dom h)}\<close>
  morphisms app_dheap Abs_dheap
  by (rule exI[where x=Map.empty], force)

lemmas Abs_dheap_inverse' = Abs_dheap_inverse[OF iffD2[OF mem_Collect_eq]]

syntax app_dheap :: \<open>('a,'b) dheap \<Rightarrow> 'a \<Rightarrow> (perm \<times> 'b) option\<close> (infix \<open>\<bullet>\<close> 990)

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

lemma Abs_dheap_inverse_app[simp]:
  \<open>Abs_dheap (app_dheap h) \<bullet> x = h \<bullet> x\<close>
  by (simp add: app_dheap_inverse)

lemma app_Abs_dheap_Option_bind[simp]:
  \<open>finite (dom a) \<Longrightarrow> app_dheap (Abs_dheap (\<lambda>x. Option.bind (a x) f)) x = Option.bind (a x) f\<close>
  by (subst Abs_dheap_inverse; force intro: rev_finite_subset simp add: dom_def bind_eq_Some_conv)

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

lift_definition map_dheap :: \<open>(perm \<Rightarrow> perm) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('i,'a) dheap \<Rightarrow> ('i,'b) dheap\<close> is
  \<open>\<lambda>fp::(perm \<Rightarrow> perm). \<lambda>fv h. \<lambda>x. map_option (map_prod fp fv) (h x)\<close>
  by (force simp add: dom_map_option)

lemma map_app_dheap_eq[simp]:
  \<open>map_dheap fp fv a \<bullet> x = map_option (map_prod fp fv) (a \<bullet> x)\<close>
  by (metis map_dheap.rep_eq)

lemma dom_map_dheap_eq[simp]:
  \<open>dom_dheap (map_dheap fp fv a) = dom_dheap a\<close>
  by (simp add: dom_dheap_iff map_dheap.rep_eq)

subsubsection \<open> Sequence \<close>

instantiation dheap :: (type, type) monoid_seq
begin

lift_definition seq_dheap :: \<open>('a,'b) dheap \<Rightarrow> ('a,'b) dheap \<Rightarrow> ('a,'b) dheap\<close>is
  \<open>\<lambda>a b. \<lambda>x. case a x of Some y \<Rightarrow> Some y | None \<Rightarrow> b x\<close>
  apply (rename_tac a b)
  apply (rule_tac B=\<open>dom a \<union> dom b\<close> in rev_finite_subset; force split: option.splits)
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

subsection \<open> strictly less than \<close>

definition subhperm :: \<open>(perm \<times> 'a) option \<Rightarrow> (perm \<times> 'a) option \<Rightarrow> bool\<close> (infix \<open>\<subset>\<^sub>d\<close> 50) where
  \<open>a \<subset>\<^sub>d b \<equiv>
    (a = None \<longrightarrow> (\<exists>y. b = Some y)) \<and> (\<forall>pa v. a = Some (pa, v) \<longrightarrow> (\<exists>pb>pa. b = Some (pb, v)))\<close>

lemma subperm_not_refl:
  \<open>a \<subset>\<^sub>d a \<longleftrightarrow> False\<close>
  by (cases a; simp add: subhperm_def map_prod_def split: prod.splits)

lemma subhperm_trans:
  \<open>a \<subset>\<^sub>d b \<Longrightarrow> b \<subset>\<^sub>d c \<Longrightarrow> a \<subset>\<^sub>d c\<close>
  by (fastforce simp add: subhperm_def)

lemma None_subhperm_eq[simp]:
  \<open>None \<subset>\<^sub>d a \<longleftrightarrow> (\<exists>y. a = Some y)\<close>
  by (cases a; simp add: subhperm_def map_prod_def split: prod.splits)

lemma subhperm_None_eq[simp]:
  \<open>a \<subset>\<^sub>d None \<longleftrightarrow> False\<close>
  by (cases a; simp add: subhperm_def map_prod_def split: prod.splits)

lemma Some_subhperm_eq[simp]:
  \<open>Some (pa,va) \<subset>\<^sub>d b \<longleftrightarrow> (\<exists>pb. pa < pb \<and> b = Some (pb, va))\<close>
  by (force simp add: subhperm_def Rep_perm_all_iff_ex Rep_perm_constraintsD less_perm_def)

subsection \<open> less than \<close>

definition subhperm_eq :: \<open>(perm \<times> 'a) option \<Rightarrow> (perm \<times> 'a) option \<Rightarrow> bool\<close>
  (infix \<open>\<subseteq>\<^sub>d\<close> 50) where
  \<open>subhperm_eq a b \<equiv> \<forall>pa v. a  = Some (pa, v) \<longrightarrow> (\<exists>pb\<ge>pa. b = Some (pb, v))\<close>

lemma subhperm_eq_refl[simp]:
  \<open>a \<subseteq>\<^sub>d a\<close>
  by (simp add: subhperm_eq_def)

lemma subhperm_eq_trans:
  \<open>a \<subseteq>\<^sub>d b \<Longrightarrow> b \<subseteq>\<^sub>d c \<Longrightarrow> a \<subseteq>\<^sub>d c\<close>
  by (force simp add: subhperm_eq_def)

lemma subhperm_eq_antisym:
  \<open>a \<subseteq>\<^sub>d b \<Longrightarrow> b \<subseteq>\<^sub>d a \<Longrightarrow> a = b\<close>
  by (cases a; cases b; force simp add: subhperm_eq_def)

lemma None_subhperm_eq_eq[simp]:
  \<open>None \<subseteq>\<^sub>d a\<close>
  by (simp add: subhperm_eq_def)

lemma subhperm_eq_None_eq[simp]:
  \<open>a \<subseteq>\<^sub>d None \<longleftrightarrow> a = None\<close>
  using not_Some_prod_eq
  by (fastforce simp add: subhperm_eq_def)

lemma Some_subhperm_eq_eq[simp]:
  \<open>Some (pa,va) \<subseteq>\<^sub>d b \<longleftrightarrow> (\<exists>pb\<ge>pa. b = Some (pb, va))\<close>
  by (clarsimp simp add: subhperm_eq_def)

lemma subhperm_aa: \<open>a \<subset>\<^sub>d b \<longleftrightarrow> a \<subseteq>\<^sub>d b \<and> \<not>(b \<subseteq>\<^sub>d a)\<close>
  by (fastforce simp add: subhperm_def subhperm_eq_def)

subsection \<open> plus \<close>

definition plus_hperm :: \<open>(perm \<times> 'a) option \<Rightarrow> (perm \<times> 'a) option \<Rightarrow> (perm \<times> 'a) option\<close>
  (infixl \<open>\<oplus>\<^sub>d\<close> 65) where
  \<open>plus_hperm a b \<equiv> case b of
                    Some (pb, vb) \<Rightarrow>
                      (case a of
                        Some (pa, va) \<Rightarrow> Some (pa + pb, va)
                        | None \<Rightarrow> b)
                    | None \<Rightarrow> a\<close>

lemma finite_dom_add[simp]:
  \<open>finite (dom (\<lambda>x. a x \<oplus>\<^sub>d b x)) \<longleftrightarrow> finite (dom a) \<and> finite (dom b)\<close>
  by (fastforce simp add: dom_def plus_hperm_def conj_disj_distribL conj_disj_distribR imp_conv_disj
      simp del: imp_conv_disj[symmetric] split: option.splits)

lemma plus_perm_simps[simp]:
  \<open>a \<oplus>\<^sub>d None = a\<close>
  \<open>None \<oplus>\<^sub>d b = b\<close>
  \<open>Some (pa, va) \<oplus>\<^sub>d Some (pb, vb) = Some (pa + pb, va)\<close>
  by (force simp add: plus_hperm_def split: option.splits)+

lemma plus_perm_eq_None_iff[simp]:
  \<open>a \<oplus>\<^sub>d b = None \<longleftrightarrow> a = None \<and> b = None\<close>
  by (force simp add: plus_hperm_def split: option.splits)

lemma plus_perm_eq_Some_iff:
  \<open>\<And>a pb vb c.
    a \<oplus>\<^sub>d Some (pb, vb) = c \<longleftrightarrow>
      (case a of
        None \<Rightarrow> c = Some (pb,vb)
      | Some (pa, va) \<Rightarrow> c = Some (pa + pb, va))\<close>
  \<open>\<And>pa va b c.
    Some (pa, va) \<oplus>\<^sub>d b  = c \<longleftrightarrow>
      (case b of
        None \<Rightarrow> c = Some (pa, va)
      | Some (pb, vb) \<Rightarrow> c = Some (pa + pb, va))\<close>
  \<open>\<And>a b p v.
    (a \<oplus>\<^sub>d b) = Some (p, v) \<longleftrightarrow>
      (b = None \<longrightarrow> a = Some (p, v)) \<and>
      (a = None \<longrightarrow> b = Some (p, v)) \<and>
      (\<forall>pa va. a = Some (pa, va) \<longrightarrow>
        (\<forall>pb vb. b = Some (pb, vb) \<longrightarrow>
          p = pa + pb \<and> v = va))\<close>
  by (force simp add: plus_hperm_def split: option.splits)+

lemma hperm_plus_bind_left[simp]:
  \<open>Option.bind a f \<oplus>\<^sub>d b =
    (case a of
      None \<Rightarrow> b
    | Some x \<Rightarrow> f x \<oplus>\<^sub>d b)\<close>
  by (force simp add: plus_hperm_def Option.bind_eq_Some_conv Option.bind_eq_None_conv
      split: option.splits)

lemma hperm_plus_bind_right[simp]:
  \<open>a \<oplus>\<^sub>d Option.bind b f =
    (case b of
      None \<Rightarrow> a
    | Some x \<Rightarrow> a \<oplus>\<^sub>d f x)\<close>
  by (force simp add: plus_hperm_def Option.bind_eq_Some_conv Option.bind_eq_None_conv
      split: option.splits)

lemmas plus_perm_eq_Some_iff_rev = HOL.trans[OF HOL.eq_commute plus_perm_eq_Some_iff(3)]

subsection \<open> Disjointness \<close>

definition disjoint_set_dheap :: \<open>('a,'b) dheap \<Rightarrow> 'a set \<Rightarrow> ('a,'b) dheap \<Rightarrow> bool\<close>
  ("_ ##\<^bsub>_\<^esub> _" [61,0,61] 60) where
  \<open>a ##\<^bsub>A\<^esub> b \<equiv> \<forall>x\<in>A.
    \<forall>pa va. a \<bullet> x = Some (pa, va) \<longrightarrow>
      (\<forall>pb vb. b \<bullet> x = Some (pb, vb) \<longrightarrow> pa ## pb \<and> va = vb)\<close>

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

lemma disjoint_dheap_Some_same_valD:
  \<open>a ## b \<Longrightarrow> a \<bullet> x = Some (pa,va) \<Longrightarrow>  b \<bullet> x = Some (pb,vb) \<Longrightarrow> va = vb\<close>
  by (simp add: disjoint_dheap_def disjoint_set_dheap_def)

lemma disjoint_dheap_Some_bounded_oneD:
  \<open>a ## b \<Longrightarrow> a \<bullet> x = Some (pa,va) \<Longrightarrow> b \<bullet> x = Some (pb,vb) \<Longrightarrow> wperm pa + wperm pb \<le> 1\<close>
  by (simp add: disjoint_dheap_def disjoint_set_dheap_def disjoint_perm_def
      less_eq_perm.rep_eq wperm_def split: prod.splits, metis prod.collapse)

subsection \<open> Addition \<close>

text \<open>Define plus on dheaps\<close>
instantiation dheap :: (type, type) plus
begin

lift_definition plus_dheap :: \<open>('a,'b) dheap \<Rightarrow> ('a,'b) dheap \<Rightarrow> ('a,'b) dheap\<close> is
  \<open>\<lambda>ma mb. \<lambda>x. ma x \<oplus>\<^sub>d mb x\<close>
  apply (rename_tac ma mb)
  apply (simp add: dom_def plus_hperm_def split: option.splits)
  apply (rule_tac B=\<open>dom ma \<union> dom mb\<close> in rev_finite_subset; force simp add: dom_def)
  done

instance by standard

end

lemma app_plus_dheap[simp]:
  \<open>(a + b) \<bullet> x = a \<bullet> x \<oplus>\<^sub>d b \<bullet> x\<close>
  by (simp add: disjoint_dheap_def' plus_dheap_def Abs_dheap_inverse)

lemma restrict_dheap_add_eq[simp]:
  \<open>(a + b) |`\<^sub>d A = a |`\<^sub>d A + b |`\<^sub>d A\<close>
  by (simp add: dheap_eq_iff)

lemma dom_plus_dheap_eq[simp]: \<open>dom_dheap (h1 + h2) = dom_dheap h1 \<union> dom_dheap h2\<close>
  by (simp add: dom_dheap.rep_eq plus_hperm_def dom_def set_eq_iff split: option.splits)

lemma appAbs_plus_dheap[simp]:
  \<open>finite (dom a) \<Longrightarrow> finite (dom b) \<Longrightarrow> app_dheap (Abs_dheap (\<lambda>x. a x \<oplus>\<^sub>d b x)) x = a x \<oplus>\<^sub>d b x\<close>
  by (force simp add: Abs_dheap_inverse)

text \<open>Define less than and less than or equal on dheaps\<close>

instantiation dheap :: (type, type) order_bot
begin

definition less_eq_dheap :: \<open>('a,'b) dheap \<Rightarrow> ('a,'b) dheap \<Rightarrow> bool\<close> where
  \<open>less_eq_dheap ma mb \<equiv> \<forall>x. ma \<bullet> x \<subseteq>\<^sub>d mb \<bullet> x\<close>

lemma less_eq_dheap_iff:
  \<open>a \<le> b \<longleftrightarrow> (\<forall>x pa v. a \<bullet> x = Some (pa, v) \<longrightarrow> (\<exists>pb\<ge>pa. b \<bullet> x = Some (pb, v)))\<close>
  by (simp add: less_eq_dheap_def subhperm_eq_def)

definition less_dheap :: \<open>('a,'b) dheap \<Rightarrow> ('a,'b) dheap \<Rightarrow> bool\<close> where
  \<open>less_dheap a b \<equiv> a \<le> b \<and> \<not>(b \<le> a)\<close>

lift_definition bot_dheap :: \<open>('a,'b) dheap\<close> is \<open>Map.empty\<close>
  by simp

lemma app_bot_dheap[simp]:
  \<open>\<bottom> \<bullet> x = None\<close>
  by (simp add: bot_dheap.rep_eq)

instance
  apply standard
      apply (force simp add: less_dheap_def)
     apply (force simp add: less_eq_dheap_def intro: subhperm_eq_refl)
    apply (force dest: subhperm_eq_trans simp add: less_eq_dheap_def)
   apply (force dest: subhperm_eq_antisym simp add: less_eq_dheap_def dheap_eq_iff)
  apply (force simp add: less_eq_dheap_def)
  done

end

lemma subperm_eq_restrictL[simp]: \<open>(a |`\<^sub>d A) \<bullet> x \<subseteq>\<^sub>d b \<bullet> x \<longleftrightarrow> (x \<in> A \<longrightarrow> a \<bullet> x \<subseteq>\<^sub>d b \<bullet> x)\<close>
  by simp

lemma subperm_eq_restrictR[simp]:
  \<open>a \<bullet> x \<subseteq>\<^sub>d (b |`\<^sub>d B) \<bullet> x \<longleftrightarrow> (if x \<in> B then a \<bullet> x \<subseteq>\<^sub>d b \<bullet> x else a \<bullet> x = None)\<close>
  by (simp add: dom_dheap_def domIff)

lemma subperm_eq_seqL[simp]:
  \<open>(a1 \<triangleright> a2) \<bullet> x \<subseteq>\<^sub>d b \<bullet> x \<longleftrightarrow> a1 \<bullet> x \<subseteq>\<^sub>d b \<bullet> x \<and> (a1 \<bullet> x = None \<longrightarrow> a2 \<bullet> x \<subseteq>\<^sub>d b \<bullet> x)\<close>
  by (simp add: split: option.splits)

lemma subperm_eq_seqR[simp]:
  \<open>a \<bullet> x \<subseteq>\<^sub>d (b1 \<triangleright> b2) \<bullet> x \<longleftrightarrow> (if b1 \<bullet> x = None then a \<bullet> x \<subseteq>\<^sub>d b2 \<bullet> x else a \<bullet> x \<subseteq>\<^sub>d b1 \<bullet> x)\<close>
  by (clarsimp split: option.splits)


lemma le_map_dheapL:
  \<open>map_dheap fp fv a \<le> a \<longleftrightarrow> (\<forall>x p v. app_dheap a x = Some (p, v) \<longrightarrow> fp p \<le> p \<and> fv v = v)\<close>
  by (force simp add: less_eq_dheap_def subhperm_eq_def)

text \<open> if \<open>a \<oplus> b = c\<close>, then \<open>antiplus_perm c b = a\<close> \<close>
definition antiplus_hperm :: \<open>(perm \<times> 'a) option \<Rightarrow> (perm \<times> 'a) option \<Rightarrow> (perm \<times> 'a) option\<close> where
  \<open>antiplus_hperm a b \<equiv>
    case a of
      Some (pa, va) \<Rightarrow>
        (case b of
          Some (pb, vb) \<Rightarrow>
            Some ((if pb \<le> pa then (SOME pc. pb ## pc \<and> pa = pb + pc) else undefined), vb)
        | None \<Rightarrow> a)
    | None \<Rightarrow> b\<close>

lemma antiplus_dheap_eq[simp]:
  \<open>antiplus_hperm a None = a\<close>
  \<open>antiplus_hperm None b = b\<close>
  \<open>antiplus_hperm (Some (pa, va)) (Some (pb, vb)) =
    Some ((if pb \<le> pa then (SOME pc. pb ## pc \<and> pa = pb + pc) else undefined), vb)\<close>
  by (simp add: antiplus_hperm_def split: option.splits)+


lemma app_Abs_antiplus_dheap:
  \<open>\<forall>x. b \<bullet> x \<subseteq>\<^sub>d a \<bullet> x \<Longrightarrow>
    Abs_dheap (\<lambda>x. antiplus_hperm (a \<bullet> x) (b \<bullet> x)) \<bullet> x = antiplus_hperm (a \<bullet> x) (b \<bullet> x)\<close>
  apply (subst Abs_dheap_inverse')
    apply (rule rev_finite_subset[of \<open>dom_dheap a \<union> dom_dheap b\<close>])
     apply force
    apply (force simp add: dom_dheap_def antiplus_hperm_def split: option.splits)
  apply (clarsimp simp add: all_conj_distrib[symmetric])
  done

lemma plus_antiplus_eq:
  \<open>\<forall>x. a \<bullet> x \<subseteq>\<^sub>d b \<bullet> x \<Longrightarrow> a \<bullet> x \<oplus>\<^sub>d antiplus_hperm (b \<bullet> x) (a \<bullet> x) = b \<bullet> x\<close>
  apply (simp add: antiplus_hperm_def plus_hperm_def split: option.splits)
  apply (intro conjI impI allI; (drule_tac x=x in spec, force)?) (* 1 \<leadsto> 1 *)
  apply (drule_tac x=x in spec)
  apply (clarsimp simp add: le_iff_sepadd)
  apply (rule_tac a=c in someI2; force)
  done

instantiation dheap :: (type,type) sepalg
begin

lift_definition zero_dheap :: \<open>('a,'b) dheap\<close> is \<open>Map.empty\<close>
  by simp

lemma app_zero_dheap[simp]:
  \<open>0 \<bullet> x = None\<close>
  by (simp add: zero_dheap.rep_eq)

lemma bot_dheap_eq_zero_dheap:
  \<open>(\<bottom> :: ('a,'b) dheap) = 0\<close>
  by (simp add: zero_dheap.abs_eq bot_dheap.abs_eq)

lemma le_iff_sepadd_helper:
  fixes a b :: \<open>('a,'b) dheap\<close>
  shows \<open>(a \<le> b) = (\<exists>c. a ## c \<and> b = a + c)\<close>
  apply (rule iffI)
   apply (clarsimp simp add: dheap_eq_iff less_eq_dheap_def disjoint_dheap_def')
   apply (rule exI[of _ \<open>Abs_dheap (\<lambda>x. antiplus_hperm (b \<bullet> x) (a \<bullet> x))\<close>])
   apply (clarsimp simp add: dheap_eq_iff disjoint_dheap_def' less_eq_dheap_def
      all_conj_distrib[symmetric] split: option.splits)
   apply (clarsimp simp add: app_Abs_antiplus_dheap)
   apply (rule conjI)
    apply (drule_tac x=x in spec)
    apply (clarsimp simp add: le_iff_sepadd)
    apply (rule_tac a=c in someI2; force)
   apply (simp add: plus_antiplus_eq; fail)
  apply (force simp add: less_eq_dheap_def plus_hperm_def subhperm_eq_def
      disjoint_dheap_def disjoint_set_dheap_def le_plus split: option.splits) 
  done

instance
  apply standard
          apply (force simp add: disjoint_dheap_def')
          apply (force simp add: disjoint_dheap_def')
    (* PCM *)
         apply (force simp add: dheap_eq_iff plus_hperm_def disjoint_dheap_def' partial_add_assoc split: option.splits)
        apply (force simp add: plus_hperm_def disjoint_dheap_def' dheap_eq_iff partial_add_commute
      split: option.splits)
       apply (simp add: dheap_eq_iff; fail)
    (* separation *)
      apply (force simp add: disjoint_dheap_def' disjoint_symm)
  subgoal
    apply (clarsimp simp add: disjoint_dheap_def' plus_hperm_def split: option.splits)
    apply (drule_tac x=x in spec)+
    apply (meson disjoint_add_rightL)
    done
      (* subgoal *)
    apply (clarsimp simp add: disjoint_dheap_def' plus_hperm_def split: option.splits)
    apply (drule_tac x=x in spec)+
    apply (case_tac \<open>c \<bullet> x\<close>)
     apply (clarsimp simp add: disjoint_symm; fail)
    apply (force dest: disjoint_add_right_commute)
    (* done *)
  subgoal
    apply (clarsimp simp add: Abs_dheap_inject fun_eq_iff dheap_eq_iff all_conj_distrib[symmetric]
        disjoint_dheap_def')
    apply (drule_tac x=x in spec)+
    apply (clarsimp simp add: disjoint_perm_def plus_hperm_def plus_perm_def Rep_perm_constraintsD
        Abs_perm_inject eq_Abs_perm_iff' add_nonneg_eq_0_iff
        split: option.splits prod.splits)
    done
  apply (simp add: le_iff_sepadd_helper; fail)
  done

end


lemma disjoint_restrict_dheap_iff[simp]:
  \<open>a |`\<^sub>d A ##\<^bsub>X\<^esub> b \<longleftrightarrow> a ##\<^bsub>X \<inter> A\<^esub> b\<close>
  \<open>a ##\<^bsub>X\<^esub> b |`\<^sub>d B \<longleftrightarrow> a ##\<^bsub>X \<inter> B\<^esub> b\<close>
  by (force simp add: disjoint_set_dheap_def Ball_def)+


section \<open> The stable and zero domains \<close>

definition stabledom :: \<open>('a,'b) dheap \<Rightarrow> 'a set\<close> where
  \<open>stabledom a \<equiv> {x. \<exists>p v. a \<bullet> x = Some (p,v) \<and> (\<exists>da wa. Rep_perm p = (da,wa) \<and> wa > 0)}\<close>

definition zerodom :: \<open>('a,'b) dheap \<Rightarrow> 'a set\<close> where
  \<open>zerodom a \<equiv> {x. \<exists>p v. a \<bullet> x = Some (p,v) \<and> (\<exists>da wa. Rep_perm p = (da,wa) \<and> wa = 0)}\<close>

lemma dom_dheap_sep:
  \<open>dom_dheap a = stabledom a \<union> zerodom a\<close>
  using Rep_perm_constraints 
  by (fastforce simp add: dom_dheap_def stabledom_def zerodom_def dom_def set_eq_iff)

lemma stabledom_subseteq_dom_dheap:
  \<open>stabledom a \<subseteq> dom_dheap a\<close>
  by (simp add: dom_dheap_sep)

find_theorems Option.bind

instantiation dheap :: (type,type) stable_sepalg
begin

lift_definition stableres_dheap :: \<open>('a,'b) dheap \<Rightarrow> ('a,'b) dheap\<close> is
  \<open>\<lambda>a x. Option.bind (a x) (\<lambda>(p,v). if wperm p > 0 then Some (p,v) else None)\<close>
  by (force intro: rev_finite_subset simp add: dom_def rev_finite_subset_Collect
      Option.bind_eq_Some_conv)

lemma app_stableres_dheap[simp]:
  \<open>stableres a \<bullet> x = Option.bind (a \<bullet> x) (\<lambda>(p,v). if wperm p > 0 then Some (p,v) else None)\<close>
  using stableres_dheap.rep_eq by auto

instance
  apply standard
     apply (force simp add: stableres_dheap_def disjoint_dheap_def' bind_eq_Some_conv)
    apply (force simp add: stableres_dheap_def disjoint_dheap_def' less_eq_dheap_def
      bind_eq_Some_conv antisym_conv2 le_plus le_plus2 split: option.splits)
   apply (force simp add: dheap_eq_iff split: Option.bind_split)
  apply (clarsimp simp add: stableres_dheap_def less_eq_dheap_def split: Option.bind_split)
  done


end


lift_definition unstableres :: \<open>('a,'b) dheap \<Rightarrow> ('a,'b) dheap\<close> is
  \<open>\<lambda>a x. Option.bind (a x) (\<lambda>(p,v). if wperm p = 0 then Some (p,v) else None)\<close>
  by (force intro: rev_finite_subset simp add: dom_def rev_finite_subset_Collect bind_eq_Some_conv)

lemma stable_unstableres_disjoint:
  \<open>stableres a ## unstableres a\<close>
  by (clarsimp simp add: disjoint_dheap_def' unstableres_def not_less
      bind_eq_Some_conv not_le_imp_less)

lemma add_stable_unstableres:
  \<open>stableres a + unstableres a = a\<close>
  by (simp add: dheap_eq_iff unstableres_def not_less split: option.splits prod.splits)

lemma stable_le_mono:
  fixes a b :: \<open>('a,'b) dheap\<close>
  shows \<open>a \<le> b \<Longrightarrow> stableres a \<le> stableres b\<close>
  apply (clarsimp simp add: less_eq_dheap_def subhperm_eq_def bind_eq_Some_conv)
  apply (drule_tac x=x in spec)
  apply (force intro: order_less_le_trans simp add: wperm_def less_eq_perm.rep_eq split: prod.splits)
  done

lemma stable_plus_distrib:
  fixes a b :: \<open>('a,'b) dheap\<close>
  shows \<open>a ## b \<Longrightarrow> stableres a + stableres b \<le> stableres (a + b)\<close>
  apply (clarsimp simp add: less_eq_dheap_def subhperm_eq_def disjoint_dheap_def' not_less
      split: option.splits)
  apply (drule_tac x=x in spec)
  apply (simp add: wperm_def disjoint_perm_def plus_perm_def less_eq_perm.rep_eq
      Rep_perm_constraintsD eq_Abs_perm_iff' split: prod.splits)
  done

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
  apply (metis Rep_perm_constraintsD(2) add_cancel_right_left add_pos_nonneg order_le_imp_less_or_eq
      prod.collapse snd_conv)
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
    apply (metis Rep_perm_constraintsD(2) leD linorder_neqE_linordered_idom not_one_le_zero order_less_irrefl)
   apply (simp add: less_eq_rat_def; fail)
  apply (simp add: map_perm_def Rep_perm_constraintsD max_def split: prod.splits if_splits)
   apply (simp add: order.order_iff_strict; fail)
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
  apply (clarsimp simp add: less_eq_dheap_def subhperm_eq_def halve_dheap_app_eq zero_le_mult_iff
      less_eq_perm.rep_eq map_perm_def split: option.splits prod.splits)
  apply (clarsimp simp add: Rep_perm_all_iff_ex min_def)
  apply (simp add: Rep_perm_constraintsD)
  done

lemma stabledom_halve_dheap_eq[simp]:
  \<open>stabledom (halve_dheap a A) = stabledom a\<close>
  by (force simp add: halve_dheap_def)

section \<open> Stable rely-relation \<close>

definition stablerel :: \<open>('a,'b) dheap \<Rightarrow> ('a,'b) dheap \<Rightarrow> bool\<close> where
  \<open>stablerel a b \<equiv> \<forall>x v p.
    a \<bullet> x = Some (p,v) \<longrightarrow> 0 < wperm p \<longrightarrow> (\<exists>p'\<ge>p. b \<bullet> x = Some (p',v) \<and> 0 < wperm p')\<close>

lemma stablerel_iff_stableres_le: \<open>stablerel a b \<longleftrightarrow> stableres a \<le> stableres b\<close>
  by (force simp add: stablerel_def stableres_dheap_def less_eq_dheap_def subhperm_eq_def
      bind_eq_Some_conv split: if_splits)

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
  apply (simp add: stablerel_iff_stableres_le)
  apply (clarsimp simp add: disjoint_dheap_def' stablerel_iff_stableres_le less_eq_dheap_iff
      split: Option.bind_splits if_splits)
  apply (drule_tac x=x in spec)+
  apply (case_tac \<open>app_dheap a1 x\<close>; case_tac \<open>app_dheap a2 x\<close>;
      case_tac \<open>app_dheap b1 x\<close>; case_tac \<open>app_dheap b2 x\<close>)
                 apply force
                apply force
               apply force
              apply (simp; fail)
             apply (simp; fail)
            apply (simp, metis)
           apply (simp; fail)
          apply clarsimp
(*
       apply (force simp add: disjoint_dheap_def')
      apply (force intro: add_nonneg_pos)
     apply (force simp add: wperm.rep_eq)
    apply (clarsimp simp add: not_less)
    apply (force dest: disjoint_dheap_Some_same_valD)
   apply (fastforce simp add: disjoint_dheap_def')
  apply clarsimp
  apply (metis add_nonneg_eq_0_iff add_nonneg_nonneg order_le_imp_less_or_eq wperm_constraints(1))
*)
  oops

lemma stablerel_subheap:
  \<open>stablerel a b \<Longrightarrow> a' \<le> a \<Longrightarrow> b' \<le> b \<Longrightarrow> stabledom a' \<subseteq> stabledom b' \<Longrightarrow> stablerel a' b'\<close>
  apply (clarsimp simp add: stablerel_def stabledom_def less_eq_dheap_def subhperm_eq_def
      less_eq_perm.rep_eq subset_iff wperm_def split: prod.splits)

  done

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
       apply (clarsimp simp add: disjoint_dheap_def disjoint_set_dheap_def halve_dheap_app_eq)
       apply (intro conjI impI; force simp add: map_perm_eq disjoint_perm_def
        linordered_field_min_bounded_divide_by order.trans[OF wperm_constraints(2) one_le_numeral]
        split: prod.splits)
      apply (force simp add: halve_dheap_def map_perm_def dom_dheap_def plus_perm_def
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




end