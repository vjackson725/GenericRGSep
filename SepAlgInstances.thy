theory SepAlgInstances
  imports SepLogic HOL.Rat
begin

section \<open> Product \<close>

subsection \<open> perm_alg \<close>

instantiation prod :: (perm_alg,perm_alg) perm_alg
begin

definition plus_prod :: \<open>'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b\<close> where
  \<open>plus_prod a b \<equiv> (fst a + fst b, snd a + snd b)\<close>
declare plus_prod_def[simp]

definition disjoint_prod :: \<open>'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool\<close> where
  \<open>disjoint_prod a b \<equiv> (fst a ## fst b \<and> snd a ## snd b)\<close>
declare disjoint_prod_def[simp]

(* this definition is horrible because we don't have a 0,
    and thus can't prove the relation between addition and < with a pointwise definition. *)
definition less_prod :: \<open>'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool\<close> where
  \<open>less_prod a b \<equiv>
    (fst a \<noteq> fst b \<or> snd a \<noteq> snd b) \<and>
      (\<exists>c. fst a ## c \<and> fst b = fst a + c) \<and>
      (\<exists>c. snd a ## c \<and> snd b = snd a + c)\<close>

definition less_eq_prod :: \<open>'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool\<close> where
  \<open>less_eq_prod a b \<equiv> a = b \<or> a < b\<close>

lemma less_eq_prod_def2:
  \<open>a \<le> b \<longleftrightarrow> a = b \<or>
    ((fst a \<noteq> fst b \<or> snd a \<noteq> snd b) \<and>
      (\<exists>c. fst a ## c \<and> fst b = fst a + c) \<and>
      (\<exists>c. snd a ## c \<and> snd b = snd a + c))\<close>
  unfolding less_prod_def less_eq_prod_def by force

instance
  apply standard
          apply (force simp add: partial_add_assoc)
         apply (force dest: partial_add_commute)
        apply (force simp add: disjoint_sym_iff)
       apply (force dest: disjoint_add_rightL)
      apply (force dest: disjoint_add_right_commute)
     apply (force dest: dup_sub_closure)
    apply (force dest: positivity)
   apply (force simp add: less_prod_def less_eq_prod_def)
  apply (force simp add: less_prod_def less_eq_prod_def)
  done

lemma less_eq_prod1:
  \<open>fst a < fst b \<Longrightarrow> snd a ## c \<Longrightarrow> snd b = snd a + c \<Longrightarrow> a \<le> b\<close>
  by (force simp add: less_prod_def less_eq_prod_def less_iff_sepadd le_iff_sepadd_weak)

lemma less_eq_prod2:
  \<open>fst a ## c \<Longrightarrow> fst b = fst a + c \<Longrightarrow> snd a < snd b \<Longrightarrow> a \<le> b\<close>
  by (force simp add: less_prod_def less_eq_prod_def less_iff_sepadd le_iff_sepadd_weak)

end

subsection \<open> mu_sep_alg \<close>

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
  apply (simp add: less_eq_prod_def2 le_iff_sepadd_weak less_iff_sepadd)
  apply (metis prod.expand unitof_disjoint2 unitof_is_unitR2)
  done

lemma mu_less_prod_def[simp]:
  fixes a b :: \<open>_::multiunit_sep_alg \<times> _::multiunit_sep_alg\<close>
  shows \<open>a < b \<longleftrightarrow> fst a \<le> fst b \<and> snd a < snd b \<or> fst a < fst b \<and> snd a \<le> snd b\<close>
  by (metis less_le_not_le mu_less_eq_prod_def)

end

subsection \<open> sep_alg \<close>

instantiation prod :: (sep_alg,sep_alg) sep_alg
begin

definition zero_prod :: \<open>'a \<times> 'b\<close> where
  \<open>zero_prod \<equiv> (0, 0)\<close>
declare zero_prod_def[simp]

definition bot_prod :: \<open>'a \<times> 'b\<close> where
  \<open>bot_prod \<equiv> (\<bottom>, \<bottom>)\<close>
declare bot_prod_def[simp]

instance
  by standard (simp add: fun_eq_iff zero_is_bot)+

end

subsubsection \<open> add_fst & add_snd for tuple perm_alg \<close>

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

subsubsection \<open> Sepconj-conj \<close>

definition sepconj_conj
  :: \<open>('a::perm_alg \<times> 'b::perm_alg \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'b \<Rightarrow> bool)\<close>
  (infixr \<open>\<^emph>\<and>\<close> 70) where
  \<open>p \<^emph>\<and> q \<equiv> \<lambda>h. \<exists>a b c. a ## b \<and> h = (a + b, c) \<and> p (a, c) \<and> q (b, c)\<close>

lemma sepconj_conjI:
  \<open>p (a, y) \<Longrightarrow> q (b, y) \<Longrightarrow> a ## b \<Longrightarrow> x = a + b \<Longrightarrow> (p \<^emph>\<and> q) (x, y)\<close>
  by (force simp add: sepconj_conj_def)

lemma sepconj_conj_assoc:
  \<open>(p \<^emph>\<and> q) \<^emph>\<and> r = p \<^emph>\<and> (q \<^emph>\<and> r)\<close>
  apply (clarsimp simp add: sepconj_conj_def fun_eq_iff)
  apply (rule iffI)
   apply (metis disjoint_add_leftR disjoint_add_swap_lr partial_add_assoc2)
  apply (metis disjoint_add_rightL disjoint_add_swap_rl partial_add_assoc3)
  done

lemma sepconj_conj_mono:
  \<open>p \<le> p' \<Longrightarrow> q \<le> q' \<Longrightarrow> p \<^emph>\<and> q \<le> p' \<^emph>\<and> q'\<close>
  by (force simp add: sepconj_conj_def)

lemma sepconj_conj_monoL:
  \<open>p \<le> p' \<Longrightarrow> p \<^emph>\<and> q \<le> p' \<^emph>\<and> q\<close>
  by (force simp add: sepconj_conj_def)

lemma sepconj_conj_monoR:
  \<open>q \<le> q' \<Longrightarrow> p \<^emph>\<and> q \<le> p \<^emph>\<and> q'\<close>
  by (force simp add: sepconj_conj_def)


section \<open> (additive) unit \<close>

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


section \<open> (multiplicative) unit \<close>

typedef munit = \<open>{()}\<close>
  by blast

abbreviation munit :: munit (\<open>\<one>\<close>) where
  \<open>\<one> \<equiv> Abs_munit ()\<close>

lemma eq_munit_iff[iff]:
  \<open>a = (b::munit)\<close>
  using Rep_munit_inject by auto

instantiation munit :: order
begin

definition less_eq_munit :: \<open>munit \<Rightarrow> munit \<Rightarrow> bool\<close> where
  \<open>less_eq_munit a b \<equiv> True\<close>
declare less_eq_munit_def[simp]

definition less_munit :: \<open>munit \<Rightarrow> munit \<Rightarrow> bool\<close> where
  \<open>less_munit a b \<equiv> False\<close>
declare less_munit_def[simp]

instance
  by standard simp+

end

instantiation munit :: perm_alg
begin

definition plus_munit :: \<open>munit \<Rightarrow> munit \<Rightarrow> munit\<close> where
  \<open>plus_munit a b \<equiv> undefined\<close>
declare plus_munit_def[simp]

definition disjoint_munit :: \<open>munit \<Rightarrow> munit \<Rightarrow> bool\<close> where
  \<open>disjoint_munit a b \<equiv> False\<close>
declare disjoint_munit_def[simp]

instance
  by standard simp+

end


section \<open> option \<close>

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

lemma less_eq_option_def2:
  \<open>a \<le> b \<longleftrightarrow> a = None \<or> b \<noteq> None \<and> the a \<le> the b\<close>
  by (cases a; cases b; simp)


definition less_option :: \<open>'a option \<Rightarrow> 'a option \<Rightarrow> bool\<close> where
  \<open>less_option a b \<equiv>
    case a of None \<Rightarrow> b \<noteq> None | Some x \<Rightarrow> (case b of None \<Rightarrow> False | Some y \<Rightarrow> x < y)\<close>

lemma less_option_simps[simp]:
  \<open>None < None \<longleftrightarrow> False\<close>
  \<open>None < Some x\<close>
  \<open>Some x < None \<longleftrightarrow> False\<close>
  \<open>Some x < Some y \<longleftrightarrow> x < y\<close>
  by (simp add: less_option_def)+

lemma less_option_def2:
  \<open>a < b \<longleftrightarrow> b \<noteq> None \<and> (a = None \<or> the a < the b)\<close>
  by (cases a; cases b; simp)

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

lemma disjoint_option_def2:
  \<open>a ## b \<longleftrightarrow> a = None \<or> b = None \<or> the a ## the b\<close>
  by (cases a; cases b; simp)


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
              apply (force simp add: disjoint_option_def plus_option_def partial_add_assoc
      split: option.splits)
             apply (force simp add: disjoint_option_def plus_option_def dest: partial_add_commute
      split: option.splits)
            apply (metis disjoint_option_def disjoint_sym option.case_eq_if)
           apply (force simp add: disjoint_option_def dest: disjoint_add_rightL split: option.splits)
          apply (simp add: disjoint_option_def split: option.splits,
      metis disjoint_sym, metis disjoint_add_right_commute)
         apply (simp add: disjoint_option_def plus_option_def split: option.splits,
      metis dup_sub_closure)
        apply (force simp add: disjoint_option_def plus_option_def split: option.splits
      dest: positivity)
       apply (simp add: less_option_def disjoint_option_def less_iff_sepadd split: option.splits,
      blast)
      apply (clarsimp simp add: less_eq_option_def less_eq_sepadd_def split: option.splits)
      apply (intro conjI allI impI iffI) (* +2 *)
        apply (metis not_eq_None plus_None_iff)
       apply (metis disjoint_option_simps(1) plus_option_simps(1))
      apply (metis disjoint_option_def2 plus_option_simps(1,3)
      option.distinct(1) option.exhaust_sel option.sel)
     apply force+
  done

end


section \<open> functions \<close>
                                         
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
      apply (simp add: disjoint_fun_def plus_fun_def fun_eq_iff, metis dup_sub_closure)
     apply (simp add: disjoint_fun_def plus_fun_def fun_eq_iff, metis positivity)
  subgoal
    apply (simp add: less_fun_def plus_fun_def le_fun_def disjoint_fun_def le_iff_sepadd)
    apply (intro iffI conjI)
       apply blast
      apply metis (* n.b. uses choice *)
     apply blast
    apply (clarsimp, metis less_le less_le_not_le partial_le_plus)
    done
  subgoal
    apply (intro iffI disjCI2)
     apply (clarsimp simp add: le_fun_def fun_eq_iff disjoint_fun_def le_iff_sepadd)
     apply metis (* n.b. uses choice *)
    apply (force simp add: le_fun_def less_eq_sepadd_def disjoint_fun_def)
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
  by standard (simp add: fun_eq_iff zero_is_bot le_fun_def)+

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
declare less_eq_discr_def[simp]

lemma less_eq_discr_iff[simp]:
  \<open>Discr x \<le> Discr y \<longleftrightarrow> x = y\<close>
  by simp

definition less_discr :: \<open>'a discr \<Rightarrow> 'a discr \<Rightarrow> bool\<close> where
  \<open>less_discr a b \<equiv> False\<close>
declare less_discr_def[simp]

definition plus_discr :: \<open>'a discr \<Rightarrow> 'a discr \<Rightarrow> 'a discr\<close> where
  \<open>plus_discr a b \<equiv> a\<close>
declare plus_discr_def[simp]

definition disjoint_discr :: \<open>'a discr \<Rightarrow> 'a discr \<Rightarrow> bool\<close> where
  \<open>disjoint_discr a b \<equiv> a = b\<close>
declare disjoint_discr_def[simp]

instance
  by standard (force simp add: the_discr_inject)+

end

instantiation discr :: (type) multiunit_sep_alg
begin

definition unitof_discr :: \<open>'a discr \<Rightarrow> 'a discr\<close> where
  \<open>unitof_discr x = x\<close>
declare unitof_discr_def[simp]

instance
  by standard simp+

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

lemma fperm_val_less_then_fperm_conditions_sub2:
  \<open>fperm_val a \<le> fperm_val b \<Longrightarrow> fperm_val a \<noteq> fperm_val b \<Longrightarrow> 0 < fperm_val b - fperm_val a\<close>
  \<open>fperm_val a \<le> fperm_val b \<Longrightarrow> fperm_val a \<noteq> fperm_val b \<Longrightarrow> fperm_val b - fperm_val a \<le> 1\<close>
   apply (simp add: fperm_val_less_then_fperm_conditions_sub(1))
  apply (simp add: fperm_val_less_then_fperm_conditions_sub(2))
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
          apply (force simp add: fperm_eq_iff_fperm_val_eq add.assoc disjoint_fperm_def plus_fperm.rep_eq)
         apply (force simp add: fperm_eq_iff_fperm_val_eq add.commute disjoint_fperm_def plus_fperm.rep_eq)
        apply (simp add: disjoint_fperm_def add.commute; fail)
       apply (simp add: disjoint_fperm_def plus_fperm.rep_eq add.assoc[symmetric])
       apply (metis fperm_val_conditions(1) ge0_plus_le_then_left_le add_pos_pos order_less_imp_le)
      apply (simp add: disjoint_fperm_def plus_fperm.rep_eq add.left_commute min.coboundedI2
      min_add_distrib_right; fail)
     apply (simp add: disjoint_fperm_def plus_fperm_eq FPerm_eq_iff fperm_val_conditions)
     apply (metis FPerm_inverse_iff add_cancel_right_right fperm_val_add_gt0 fperm_val_never_zero)
    apply (simp add: disjoint_fperm_def FPerm_eq_iff fperm_val_conditions)
    apply (metis fperm_val_conditions(1) less_add_same_cancel1 min.absorb_iff2 not_less_iff_gr_or_eq
      plus_fperm.rep_eq)
    (* subgoal *)
   apply (rule iffI)
    apply (clarsimp simp add: less_fperm_def disjoint_fperm_def plus_fperm_eq)
    apply (rule conjI, blast)
    apply (rule_tac x=\<open>FPerm (fperm_val b - fperm_val a)\<close> in exI)
    apply (simp add: fperm_val_less_then_fperm_conditions_sub fperm_val_conditions(2)
      fperm_val_inverse; fail)
   apply (clarsimp simp add: less_fperm_def disjoint_fperm_def plus_fperm_eq
      fperm_val_add_gt0 fperm_val_conditions; fail)
    (* done *)
  (* subgoal *)
   apply (intro iffI disjCI2)
   apply (clarsimp simp add: less_fperm_def disjoint_fperm_def plus_fperm_eq)
   apply (rule_tac x=\<open>FPerm (fperm_val b - fperm_val a)\<close> in exI)
   apply (metis FPerm_inverse_iff fperm_val_conditions(2) fperm_val_inverse
      fperm_val_less_then_fperm_conditions_sub2(1) fperm_val_less_then_fperm_conditions_sub2(2)
      le_add_diff_inverse less_eq_fperm_def min.absorb_iff2)
  apply (metis disjoint_fperm_def plus_fperm.rep_eq fperm_val_conditions(1) less_add_same_cancel1
      less_eq_fperm_def min.absorb2 order_eq_iff order_less_imp_le)
    (* done *)
  done

end


section \<open> mfault \<close>

text \<open> TODO: turn this into error \<close>

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

context perm_alg
begin

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

definition emp_mfault :: \<open>('a \<Rightarrow> bool) mfault\<close> ("emp\<^sub>f") where
  \<open>emp\<^sub>f \<equiv> Success emp\<close>

end

section \<open> Useful Sepalgebra Constructions \<close>

type_synonym ('i,'v) heap = \<open>'i \<rightharpoonup> (munit \<times> 'v discr)\<close>

type_synonym ('i,'v) perm_heap = \<open>'i \<rightharpoonup> (rat fperm \<times> 'v discr)\<close>


section \<open> Results \<close>

text \<open> sepdomeq of two maps (with discrete elements) holds exactly when their domains are equal. \<close>
lemma sepdomeq_fun:
  fixes f g :: \<open>('a,'b) heap\<close>
  shows \<open>sepdomeq f g \<longleftrightarrow> dom f = dom g\<close>
  apply (simp add: sepdomeq_def disjoint_fun_def disjoint_option_def split: option.splits)
  apply (rule iffI)
   apply (frule_tac x=\<open>\<lambda>x. if x \<notin> dom f then Some undefined else None\<close> in spec)
   apply (drule_tac x=\<open>\<lambda>x. if x \<notin> dom g then Some undefined else None\<close> in spec)
   apply (clarsimp simp add: dom_def set_eq_iff not_Some_prod_eq[symmetric]
      simp del: not_Some_prod_eq split: if_splits, metis)
  apply blast
  done

end