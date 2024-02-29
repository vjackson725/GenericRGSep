theory SepAlgInstances
  imports SepLogic HOL.Rat
begin

section \<open> Instances \<close>

instantiation prod :: (perm_alg,perm_alg) perm_alg
begin

definition plus_prod :: \<open>'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b\<close> where
  \<open>plus_prod a b \<equiv> (fst a + fst b, snd a + snd b)\<close>
declare plus_prod_def[simp]

definition disjoint_prod :: \<open>'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool\<close> where
  \<open>disjoint_prod a b \<equiv> (fst a ## fst b \<and> snd a ## snd b)\<close>
declare disjoint_prod_def[simp]

(* these definitions are horrible because we don't have a 0, and thus can't prove the addition
    property with a pointwise definition. *)
definition less_eq_prod :: \<open>'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool\<close> where
  \<open>less_eq_prod a b \<equiv>
    a = b \<or>
      ((fst a \<noteq> fst b \<or> snd a \<noteq> snd b) \<and>
        (\<exists>c. fst a ## c \<and> fst b = fst a + c) \<and>
        (\<exists>c. snd a ## c \<and> snd b = snd a + c))\<close>

definition less_prod :: \<open>'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool\<close> where
  \<open>less_prod a b \<equiv>
    (fst a \<noteq> fst b \<or> snd a \<noteq> snd b) \<and>
      (\<exists>c. fst a ## c \<and> fst b = fst a + c) \<and>
      (\<exists>c. snd a ## c \<and> snd b = snd a + c)\<close>

instance
  apply standard
            apply (simp add: less_prod_def less_eq_prod_def)
            apply (metis order_antisym_conv partial_le_plus)
           apply (force simp add: less_prod_def less_eq_prod_def)
          apply (simp add: less_prod_def less_eq_prod_def, metis disjoint_add_swap_lr partial_add_assoc2 prod.expand)
         apply (metis less_eq_prod_def order_antisym_conv partial_le_plus)
        apply (force simp add: partial_add_assoc)
       apply (force dest: partial_add_commute)
      apply (force simp add: disjoint_sym_iff)
     apply (force dest: disjoint_add_rightL)
    apply (force dest: disjoint_add_right_commute)
   apply (force dest: positivity)
  apply (clarsimp simp add: less_iff_sepadd)
  apply (simp add: less_prod_def less_eq_prod_def, blast)
  done

lemma less_eq_prod1:
  \<open>fst a < fst b \<Longrightarrow> snd a ## c \<Longrightarrow> snd b = snd a + c \<Longrightarrow> a \<le> b\<close>
  by (force simp add: less_prod_def less_eq_prod_def less_iff_sepadd le_iff_sepadd_weak)

lemma less_eq_prod2:
  \<open>fst a ## c \<Longrightarrow> fst b = fst a + c \<Longrightarrow> snd a < snd b \<Longrightarrow> a \<le> b\<close>
  by (force simp add: less_prod_def less_eq_prod_def less_iff_sepadd le_iff_sepadd_weak)

end

instantiation prod :: (multiunit_sep_alg,multiunit_sep_alg) multiunit_sep_alg
begin

definition unitof_prod :: \<open>'a \<times> 'b \<Rightarrow> 'a \<times> 'b\<close> where
  \<open>unitof a \<equiv> (unitof (fst a), unitof (snd a))\<close>
declare unitof_prod_def[simp]

instance
  by standard force+

lemma mu_less_eq_prod_def[simp]:
  fixes a b :: \<open>_::multiunit_sep_alg \<times> _::multiunit_sep_alg\<close>
  shows \<open>a \<le> b \<longleftrightarrow> fst a \<le> fst b \<and> snd a \<le> snd b\<close>
  apply (simp add: less_eq_prod_def le_iff_sepadd_weak)
  apply (metis prod.expand unitof_disjoint2 unitof_is_unitR2)
  done

lemma mu_less_prod_def[simp]:
  fixes a b :: \<open>_::multiunit_sep_alg \<times> _::multiunit_sep_alg\<close>
  shows \<open>a < b \<longleftrightarrow> fst a \<le> fst b \<and> snd a < snd b \<or> fst a < fst b \<and> snd a \<le> snd b\<close>
  by (metis less_le_not_le mu_less_eq_prod_def)

end

instantiation prod :: (sep_alg,sep_alg) sep_alg
begin

definition zero_prod :: \<open>'a \<times> 'b\<close> where
  \<open>zero_prod \<equiv> (0, 0)\<close>
declare zero_prod_def[simp]

definition bot_prod :: \<open>'a \<times> 'b\<close> where
  \<open>bot_prod \<equiv> (\<bottom>, \<bottom>)\<close>
declare bot_prod_def[simp]

instance
  by standard force+

end

subsubsection \<open> extend part-addition to perm_alg-s \<close>

lemma perm_alg_plus_fst_accum[simp]:
  fixes x :: \<open>'a :: perm_alg\<close>
  shows \<open>fst xy ## x \<Longrightarrow> fst xy ## x' \<Longrightarrow> x ## x' \<Longrightarrow> (xy +\<^sub>L x) +\<^sub>L x' = xy +\<^sub>L (x + x')\<close>
  by (cases xy, simp add: partial_add_assoc)

lemma perm_alg_plus_snd_accum[simp]:
  fixes y :: \<open>'a :: perm_alg\<close>
  shows \<open>snd xy ## y \<Longrightarrow> snd xy ## y' \<Longrightarrow> y ## y' \<Longrightarrow> (xy +\<^sub>R y) +\<^sub>R y' = xy +\<^sub>R (y + y')\<close>
  by (cases xy, simp add: partial_add_assoc)

lemma perm_alg_plus_fst_plus_snd_eq[simp]:
  fixes y :: \<open>'a :: perm_alg\<close>
  shows
    \<open>xy +\<^sub>L x +\<^sub>R y = xy + (x, y)\<close>
    \<open>xy +\<^sub>R y +\<^sub>L x = xy + (x, y)\<close>
  by simp+


subsection \<open> unit \<close>

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


instantiation option :: (perm_alg) sep_alg
begin

definition less_eq_option :: \<open>'a option \<Rightarrow> 'a option \<Rightarrow> bool\<close> where
  \<open>less_eq_option a b \<equiv>
    case a of None \<Rightarrow> True | Some x \<Rightarrow> (case b of None \<Rightarrow> False | Some y \<Rightarrow> x \<le> y)\<close>

lemma less_eq_option_simps[simp]:
  \<open>None \<le> a\<close>
  \<open>Some x \<le> None \<longleftrightarrow> False\<close>
  \<open>Some x \<le> Some y \<longleftrightarrow> x \<le> y\<close>
  by (simp add: less_eq_option_def)+

definition less_option :: \<open>'a option \<Rightarrow> 'a option \<Rightarrow> bool\<close> where
  \<open>less_option a b \<equiv>
    case a of None \<Rightarrow> b \<noteq> None | Some x \<Rightarrow> (case b of None \<Rightarrow> False | Some y \<Rightarrow> x < y)\<close>

lemma less_option_simps[simp]:
  \<open>None < None \<longleftrightarrow> False\<close>
  \<open>None < Some x\<close>
  \<open>Some x < None \<longleftrightarrow> False\<close>
  \<open>Some x < Some y \<longleftrightarrow> x < y\<close>
  by (simp add: less_option_def)+

definition plus_option :: \<open>'a option \<Rightarrow> 'a option \<Rightarrow> 'a option\<close> where
  \<open>plus_option a b \<equiv>
    case a of None \<Rightarrow> b | Some x \<Rightarrow> (case b of None \<Rightarrow> a | Some y \<Rightarrow> Some (x + y))\<close>

lemma plus_option_simps[simp]:
  \<open>Some x + Some y = Some (x + y)\<close>
  \<open>None + b = b\<close>
  \<open>a + None = a\<close>
  by (simp add: plus_option_def split: option.splits)+

lemma plus_None_iff[simp]:
  \<open>a + b = None \<longleftrightarrow> a = None \<and> b = None\<close>
  by (simp add: plus_option_def split: option.splits)

definition disjoint_option :: \<open>'a option \<Rightarrow> 'a option \<Rightarrow> bool\<close> where
  \<open>disjoint_option a b \<equiv>
    case a of None \<Rightarrow> True | Some x \<Rightarrow> (case b of None \<Rightarrow> True | Some y \<Rightarrow> x ## y)\<close>

lemma disjoint_option_simps[simp]:
  \<open>Some x ## Some y \<longleftrightarrow> x ## y\<close>
  \<open>None ## b\<close>
  \<open>a ## None\<close>
  by (simp add: disjoint_option_def split: option.splits)+

definition unitof_option :: \<open>'a option \<Rightarrow> 'a option\<close> where
  \<open>unitof_option x \<equiv> None\<close>
declare unitof_option_def[simp]

definition zero_option :: \<open>'a option\<close> where
  \<open>zero_option \<equiv> None\<close>
declare zero_option_def[simp]

definition bot_option :: \<open>'a option\<close> where
  \<open>bot_option \<equiv> None\<close>
declare bot_option_def[simp]

instance
  apply standard
                  apply (force simp add: less_eq_option_def split: option.splits)+
           apply (force simp add: disjoint_option_def plus_option_def partial_add_assoc
      split: option.splits)
           apply (force simp add: disjoint_option_def plus_option_def dest: partial_add_commute
      split: option.splits)
         apply (metis disjoint_option_def disjoint_sym option.case_eq_if)
        apply (force simp add: disjoint_option_def dest: disjoint_add_rightL split: option.splits)
       apply (simp add: disjoint_option_def split: option.splits,
      metis disjoint_sym, metis disjoint_add_right_commute)
      apply (simp add: disjoint_option_def plus_option_def split: option.splits, metis positivity)
     apply (simp add: less_option_def disjoint_option_def less_iff_sepadd split: option.splits,
      blast)
    apply simp+
  done

end


instantiation "fun" :: (type, multiunit_sep_alg) multiunit_sep_alg
begin

definition disjoint_fun :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool\<close> where
  \<open>disjoint_fun f g \<equiv> \<forall>x. f x ## g x\<close>

lemma disjoint_funI[intro!]:
  \<open>\<forall>x. f x ## g x \<Longrightarrow> f ## g\<close>
  by (simp add: disjoint_fun_def)

definition plus_fun :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)\<close> where
  \<open>plus_fun f g \<equiv> \<lambda>x. f x + g x\<close>

lemma plus_fun_apply[simp]:
  \<open>(f + g) x = (f x + g x)\<close>
  by (simp add: plus_fun_def)

definition unitof_fun :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)\<close> where
  \<open>unitof_fun f \<equiv> \<lambda>x. unitof (f x)\<close>
declare unitof_fun_def[simp]

instance
  apply standard
           apply (simp add: disjoint_fun_def plus_fun_def fun_eq_iff, metis partial_add_assoc)
          apply (simp add: disjoint_fun_def plus_fun_def fun_eq_iff, metis partial_add_commute)
         apply (simp add: disjoint_fun_def, metis disjoint_sym)
        apply (simp add: disjoint_fun_def plus_fun_def, metis disjoint_add_rightL)
       apply (simp add: disjoint_fun_def plus_fun_def, metis disjoint_add_right_commute)
      apply (simp add: disjoint_fun_def plus_fun_def fun_eq_iff, metis positivity)
  subgoal
    apply (simp add: less_fun_def plus_fun_def le_fun_def disjoint_fun_def le_iff_sepadd)
    apply (intro iffI conjI)
       apply blast
      apply metis (* n.b. uses choice *)
     apply blast
    apply (clarsimp, metis less_le less_le_not_le partial_le_plus)
    done
   apply force
  apply (simp add: disjoint_fun_def plus_fun_def; fail)
  done

end

instantiation "fun" :: (type, sep_alg) sep_alg
begin

definition zero_fun :: \<open>('a \<Rightarrow> 'b)\<close> where
  \<open>zero_fun \<equiv> \<lambda>x. 0\<close>
declare zero_fun_def[simp]

definition bot_fun :: \<open>('a \<Rightarrow> 'b)\<close> where
  \<open>bot_fun \<equiv> \<lambda>x. 0\<close>
declare bot_fun_def[simp]

instance
  apply standard
    apply force+
  done

end

section \<open> Discrete Algebra \<close>

typedef 'a discr = \<open>UNIV :: 'a set\<close>
  morphisms the_discr Discr
  by blast

lemmas Discr_inverse_iff[simp] = Discr_inverse[simplified]
lemmas Discr_inject_iff[simp] = Discr_inject[simplified]

instantiation discr :: (type) perm_alg
begin

definition less_eq_discr :: \<open>'a discr \<Rightarrow> 'a discr \<Rightarrow> bool\<close> where
  \<open>less_eq_discr a b \<equiv> the_discr a = the_discr b\<close>

lemma less_eq_discr_iff[simp]:
  \<open>Discr x \<le> Discr y \<longleftrightarrow> x = y\<close>
  by (simp add: less_eq_discr_def)

definition less_discr :: \<open>'a discr \<Rightarrow> 'a discr \<Rightarrow> bool\<close> where
  \<open>less_discr a b \<equiv> False\<close>

declare less_discr_def[simp]

definition plus_discr :: \<open>'a discr \<Rightarrow> 'a discr \<Rightarrow> 'a discr\<close> where
  \<open>plus_discr a b \<equiv> undefined\<close>

definition disjoint_discr :: \<open>'a discr \<Rightarrow> 'a discr \<Rightarrow> bool\<close> where
  \<open>disjoint_discr a b \<equiv> False\<close>
declare disjoint_discr_def[simp]

instance
  apply standard
            apply (force simp add: less_eq_discr_def the_discr_inject)+
  done

end


section \<open> Self-additive discrete Algebra \<close>

typedef 'a add_discr = \<open>UNIV :: 'a set\<close>
  morphisms the_add_discr AddDiscr
  by blast

lemmas AddDiscr_inverse_iff[simp] = AddDiscr_inverse[simplified]
lemmas AddDiscr_inject_iff[simp] = AddDiscr_inject[simplified]

instantiation add_discr :: (type) perm_alg
begin

definition less_eq_add_discr :: \<open>'a add_discr \<Rightarrow> 'a add_discr \<Rightarrow> bool\<close> where
  \<open>less_eq_add_discr a b \<equiv> the_add_discr a = the_add_discr b\<close>

lemma less_eq_add_discr_iff[simp]:
  \<open>Discr x \<le> Discr y \<longleftrightarrow> x = y\<close>
  by (simp add: less_eq_add_discr_def)

definition less_add_discr :: \<open>'a add_discr \<Rightarrow> 'a add_discr \<Rightarrow> bool\<close> where
  \<open>less_add_discr a b \<equiv> False\<close>

declare less_add_discr_def[simp]

definition plus_add_discr :: \<open>'a add_discr \<Rightarrow> 'a add_discr \<Rightarrow> 'a add_discr\<close> where
  \<open>plus_add_discr a b \<equiv> a\<close>

definition disjoint_add_discr :: \<open>'a add_discr \<Rightarrow> 'a add_discr \<Rightarrow> bool\<close> where
  \<open>disjoint_add_discr a b \<equiv> a = b\<close>
declare disjoint_add_discr_def[simp]

instance
  by (standard; force simp add: less_eq_add_discr_def plus_add_discr_def the_add_discr_inject)

end


section \<open> Fractional FPermissions \<close>

typedef(overloaded) ('a::linordered_semidom) fperm = \<open>{x. (0::'a) < x \<and> x \<le> 1}\<close>
  morphisms fperm_val FPerm
  using zero_less_one by blast

setup_lifting type_definition_fperm

lemmas FPerm_inverse_iff[simp] = FPerm_inverse[simplified]
lemmas FPerm_inject_iff[simp] = FPerm_inject[simplified]
lemmas fperm_eq_iff_fperm_val_eq = fperm_val_inject[symmetric]

lemma FPerm_eq_iff:
  \<open>0 < a \<Longrightarrow> a \<le> 1 \<Longrightarrow> FPerm a = pa \<longleftrightarrow> fperm_val pa = a\<close>
  using fperm_val_inverse by fastforce

lemma eq_FPerm_iff:
  \<open>0 < a \<Longrightarrow> a \<le> 1 \<Longrightarrow> pa = FPerm a \<longleftrightarrow> fperm_val pa = a\<close>
  by (metis FPerm_inverse_iff fperm_val_inverse)

lemma fperm_val_conditions:
  \<open>0 < fperm_val x\<close>
  \<open>fperm_val x \<le> 1\<close>
  using fperm_val by force+

lemma fperm_val_never_zero[simp]:
  \<open>fperm_val x = 0 \<longleftrightarrow> False\<close>
  by (metis less_irrefl fperm_val_conditions(1))

lemma fperm_val_less_then_fperm_conditions_sub:
  \<open>fperm_val a < fperm_val b \<Longrightarrow> 0 < fperm_val b - fperm_val a\<close>
  \<open>fperm_val a < fperm_val b \<Longrightarrow> fperm_val b - fperm_val a \<le> 1\<close>
  apply (metis add_le_same_cancel2 leD leI le_add_diff_inverse2 order_less_imp_le)
  apply (metis fperm_val_conditions leD leI le_add_diff_inverse order_less_imp_le pos_add_strict)
  done

lemma fperm_val_add_gt0:
  \<open>0 < fperm_val x + fperm_val y\<close>
  by (simp add: add_pos_pos fperm_val_conditions(1))


instantiation fperm :: (linordered_semidom) perm_alg
begin

definition disjoint_fperm :: \<open>'a fperm \<Rightarrow> 'a fperm \<Rightarrow> bool\<close> where
  \<open>disjoint_fperm a b \<equiv> fperm_val a + fperm_val b \<le> 1\<close>

definition less_eq_fperm :: \<open>'a fperm \<Rightarrow> 'a fperm \<Rightarrow> bool\<close> where
  \<open>less_eq_fperm a b \<equiv> fperm_val a \<le> fperm_val b\<close>

lemma less_eq_fperm_iff[simp]:
  \<open>0 < x \<Longrightarrow> x \<le> 1 \<Longrightarrow> 0 < y \<Longrightarrow> y \<le> 1 \<Longrightarrow> FPerm x \<le> FPerm y \<longleftrightarrow> x \<le> y\<close>
  by (simp add: less_eq_fperm_def)

definition less_fperm :: \<open>'a fperm \<Rightarrow> 'a fperm \<Rightarrow> bool\<close> where
  \<open>less_fperm a b \<equiv> fperm_val a < fperm_val b\<close>

lemma less_fperm_iff[simp]:
  \<open>0 < x \<Longrightarrow> x \<le> 1 \<Longrightarrow> 0 < y \<Longrightarrow> y \<le> 1 \<Longrightarrow> FPerm x < FPerm y \<longleftrightarrow> x < y\<close>
  by (simp add: less_fperm_def)

lift_definition plus_fperm :: \<open>'a fperm \<Rightarrow> 'a fperm \<Rightarrow> 'a fperm\<close> is \<open>\<lambda>x y. min 1 (x + y)\<close>
  by (simp add: pos_add_strict)

lemma plus_fperm_iff[simp]:
  \<open>0 < x \<Longrightarrow> x \<le> 1 \<Longrightarrow> 0 < y \<Longrightarrow> y \<le> 1 \<Longrightarrow> FPerm x + FPerm y = FPerm (min 1 (x + y))\<close>
  by (simp add: plus_fperm.abs_eq eq_onp_same_args)

lemma plus_fperm_eq:
  \<open>x + y = FPerm (min 1 (fperm_val x + fperm_val y))\<close>
  by (metis fperm_val_inverse plus_fperm.rep_eq)

instance
  apply standard
            apply (simp add: less_eq_fperm_def less_fperm_def fperm_val_inject; force)+ 
        apply (force simp add: fperm_eq_iff_fperm_val_eq add.assoc disjoint_fperm_def plus_fperm.rep_eq)
       apply (force simp add: fperm_eq_iff_fperm_val_eq add.commute disjoint_fperm_def plus_fperm.rep_eq)
      apply (simp add: disjoint_fperm_def add.commute; fail)
     apply (simp add: disjoint_fperm_def plus_fperm.rep_eq add.assoc[symmetric])
     apply (metis fperm_val_conditions(1) ge0_plus_le_then_left_le add_pos_pos order_less_imp_le)
    apply (simp add: disjoint_fperm_def plus_fperm.rep_eq add.left_commute min.coboundedI2
      min_add_distrib_right; fail)
   apply (simp add: disjoint_fperm_def plus_fperm_eq FPerm_eq_iff fperm_val_conditions)
   apply (metis FPerm_inverse_iff add_cancel_right_right fperm_val_add_gt0 fperm_val_never_zero)
  apply (rule iffI)
   apply (clarsimp simp add: less_fperm_def disjoint_fperm_def plus_fperm_eq)
   apply (rule conjI, blast)
   apply (rule_tac x=\<open>FPerm (fperm_val b - fperm_val a)\<close> in exI)
   apply (simp add: fperm_val_less_then_fperm_conditions_sub eq_FPerm_iff fperm_val_conditions; fail)
  apply (clarsimp simp add: plus_fperm_eq disjoint_fperm_def less_fperm_def eq_FPerm_iff
      fperm_val_add_gt0 fperm_val_conditions; fail)
  done

end


section \<open> Useful Sepalgebra Constructions \<close>

type_synonym ('i,'v) heap = \<open>'i \<rightharpoonup> 'v discr\<close>

type_synonym ('i,'v) perm_heap = \<open>'i \<rightharpoonup> (rat fperm \<times> 'v add_discr)\<close>


section \<open> Results \<close>

text \<open> sepdomeq of two maps (with discrete elements) holds exactly when their domains are equal. \<close>
lemma sepdomeq_fun:
  fixes f g :: \<open>('a,'b) heap\<close>
  shows \<open>sepdomeq f g \<longleftrightarrow> dom f = dom g\<close>
  apply (simp add: sepdomeq_def disjoint_fun_def disjoint_option_def split: option.splits)
  apply (rule iffI)
   apply (frule_tac x=\<open>\<lambda>x. if x \<notin> dom f then Some undefined else None\<close> in spec)
   apply (drule_tac x=\<open>\<lambda>x. if x \<notin> dom g then Some undefined else None\<close> in spec)
   apply (clarsimp simp add: if_splits dom_def set_eq_iff, metis not_Some_eq)
  apply blast
  done

end