theory SepAlgInstances
  imports SepLogic HOL.Rat
begin


section \<open> Product \<close>

subsection \<open> order \<close>

instantiation prod :: (order, order) order
begin

definition less_eq_prod :: \<open>'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool\<close> where
  \<open>less_eq_prod a b \<equiv> fst a \<le> fst b \<and> snd a \<le> snd b\<close>
declare less_eq_prod_def[simp]

definition less_prod :: \<open>'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool\<close> where
  \<open>less_prod a b \<equiv> fst a \<le> fst b \<and> snd a < snd b \<or> fst a < fst b \<and> snd a \<le> snd b\<close>

instance
  by standard
    (force simp add: less_prod_def order.strict_iff_not)+

end

subsection \<open> perm_alg \<close>

instantiation prod :: (perm_alg,perm_alg) perm_alg
begin

definition plus_prod :: \<open>'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b\<close> where
  \<open>plus_prod a b \<equiv> (fst a + fst b, snd a + snd b)\<close>
declare plus_prod_def[simp]

definition disjoint_prod :: \<open>'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool\<close> where
  \<open>disjoint_prod a b \<equiv> (fst a ## fst b \<and> snd a ## snd b)\<close>
declare disjoint_prod_def[simp]

instance
  apply standard
       apply (force simp add: partial_add_assoc)
      apply (force dest: partial_add_commute)
     apply (force simp add: disjoint_sym_iff)
    apply (force dest: disjoint_add_rightL)
   apply (force dest: disjoint_add_right_commute)
  apply (force dest: positivity)
  done

end

lemma less_sepadd_prod_eq:
  \<open>a \<prec> b \<longleftrightarrow> (fst a \<noteq> fst b \<or> snd a \<noteq> snd b) \<and> fst a \<lesssim> fst b \<and> snd a \<lesssim> snd b\<close>
  by (cases a; cases b; force simp add: less_sepadd_def part_of_def)

lemma less_eq_sepadd_prod_eq:
  \<open>a \<preceq> b \<longleftrightarrow> fst a = fst b \<and> snd a = snd b \<or> fst a \<lesssim> fst b \<and> snd a \<lesssim> snd b\<close>
  by (cases a; cases b; force simp add: less_eq_sepadd_def part_of_def)

lemma part_of_prod_eq:
  \<open>a \<lesssim> b \<longleftrightarrow> fst a \<lesssim> fst b \<and> snd a \<lesssim> snd b\<close>
  by (cases a; cases b; force simp add: part_of_def)

subsection \<open> mu_sep_alg \<close>

instantiation prod :: (multiunit_sep_alg,multiunit_sep_alg) multiunit_sep_alg
begin

definition unitof_prod :: \<open>'a \<times> 'b \<Rightarrow> 'a \<times> 'b\<close> where
  \<open>unitof \<equiv> map_prod unitof unitof\<close>
declare unitof_prod_def[simp]

instance
  apply standard
    apply (simp add: less_eq_sepadd_def)+
  apply (force simp add: le_iff_sepadd)
  done

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

subsection \<open> Extended sep-alg instances \<close>

instance prod :: (dupcl_perm_alg, dupcl_perm_alg) dupcl_perm_alg
  by standard (force dest: dup_sub_closure)

subsection \<open> add_fst & add_snd for tuple perm_alg \<close>

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
  by standard force+

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


section \<open> Sum \<close>

subsection \<open> order \<close>

instantiation sum :: (order, order) order
begin

definition less_eq_sum :: \<open>'a + 'b \<Rightarrow> 'a + 'b \<Rightarrow> bool\<close> where
  \<open>less_eq_sum a b \<equiv>
    (\<exists>x y. a = Inl x \<and> b = Inl y \<and> x \<le> y) \<or>
    (\<exists>x y. a = Inr x \<and> b = Inr y \<and> x \<le> y)\<close>

lemma less_eq_sum_simps[simp]:
  \<open>\<And>x y. Inl x \<le> Inl y \<longleftrightarrow> x \<le> y\<close>
  \<open>\<And>x y. Inr x \<le> Inr y \<longleftrightarrow> x \<le> y\<close>
  \<open>\<And>x y. Inl x \<le> Inr y \<longleftrightarrow> False\<close>
  \<open>\<And>x y. Inr x \<le> Inl y \<longleftrightarrow> False\<close>
  by (simp add: less_eq_sum_def)+

definition less_sum :: \<open>'a + 'b \<Rightarrow> 'a + 'b \<Rightarrow> bool\<close> where
  \<open>less_sum a b \<equiv>
    (\<exists>x y. a = Inl x \<and> b = Inl y \<and> x < y) \<or>
    (\<exists>x y. a = Inr x \<and> b = Inr y \<and> x < y)\<close>

lemma less_sum_simps[simp]:
  \<open>\<And>x y. Inl x < Inl y \<longleftrightarrow> x < y\<close>
  \<open>\<And>x y. Inr x < Inr y \<longleftrightarrow> x < y\<close>
  \<open>\<And>x y. Inl x < Inr y \<longleftrightarrow> False\<close>
  \<open>\<And>x y. Inr x < Inl y \<longleftrightarrow> False\<close>
  by (simp add: less_sum_def less_eq_sum_def)+

instance
  apply standard
     apply (case_tac x; case_tac y; simp add: less_le_not_le)
    apply (case_tac x; simp)
   apply (case_tac x; case_tac y; case_tac z; simp)
  apply (case_tac x; case_tac y; simp)
  done

end

subsection \<open> perm_alg \<close>

instantiation sum :: (perm_alg,perm_alg) perm_alg
begin

definition disjoint_sum :: \<open>'a + 'b \<Rightarrow> 'a + 'b \<Rightarrow> bool\<close> where
  \<open>disjoint_sum a b \<equiv>
    (\<exists>x y. a = Inl x \<and> b = Inl y \<and> x ## y) \<or>
    (\<exists>x y. a = Inr x \<and> b = Inr y \<and> x ## y)\<close>

lemma disjoint_sum_simps[simp]:
  \<open>\<And>x y. Inl x ## Inl y = x ## y\<close>
  \<open>\<And>x y. Inr x ## Inr y = x ## y\<close>
  \<open>\<And>x y. Inl x ## Inr y = False\<close>
  \<open>\<And>x y. Inr x ## Inl y = False\<close>
  by (simp add: disjoint_sum_def)+

definition plus_sum :: \<open>'a + 'b \<Rightarrow> 'a + 'b \<Rightarrow> 'a + 'b\<close> where
  \<open>plus_sum a b \<equiv>
      case a of
        Inl x \<Rightarrow>
          (case b of
            Inl y \<Rightarrow> Inl (x + y)
          | Inr y \<Rightarrow> undefined)
      | Inr x \<Rightarrow>
          (case b of
            Inl y \<Rightarrow> undefined
          | Inr y \<Rightarrow> Inr (x + y))\<close>

lemma plus_sum_simps[simp]:
  \<open>\<And>x y. Inl x + Inl y = Inl (x + y)\<close>
  \<open>\<And>x y. Inr x + Inr y = Inr (x + y)\<close>
  by (simp add: plus_sum_def)+

instance
  apply standard
       apply (simp add: disjoint_sum_def)
       apply (elim disjE; force simp add: partial_add_assoc)
      apply (simp add: disjoint_sum_def)
      apply (elim disjE; force dest: partial_add_commute)
     apply (simp add: disjoint_sum_def)
     apply (elim disjE exE conjE; force dest: disjoint_sym)
    apply (simp add: disjoint_sum_def)
    apply (elim disjE exE conjE; force dest: disjoint_add_rightL)
   apply (simp add: disjoint_sum_def)
   apply (elim disjE exE conjE; force dest: disjoint_add_right_commute)
  apply (simp add: disjoint_sum_def)
  apply (elim disjE exE conjE; force dest: positivity)
  done

end

lemma part_of_sum_simps[simp]:
  \<open>\<And>x y. Inl x \<lesssim> Inl y \<longleftrightarrow> x \<lesssim> y\<close>
  \<open>\<And>x y. Inr x \<lesssim> Inr y \<longleftrightarrow> x \<lesssim> y\<close>
  \<open>\<And>x y. Inl x \<lesssim> Inr y \<longleftrightarrow> False\<close>
  \<open>\<And>x y. Inr x \<lesssim> Inl y \<longleftrightarrow> False\<close>
     apply (simp add: part_of_def disjoint_sum_def plus_sum_def split: sum.splits)
     apply (metis Inl_inject obj_sumE sum.distinct(1))
    apply (simp add: part_of_def disjoint_sum_def plus_sum_def split: sum.splits)
    apply (metis Inr_inject obj_sumE sum.distinct(1))
   apply (simp add: part_of_def disjoint_sum_def plus_sum_def split: sum.splits)
  apply (simp add: part_of_def disjoint_sum_def plus_sum_def split: sum.splits)
  done

lemma less_eq_sepadd_sum_simps[simp]:
  \<open>\<And>x y. Inl x \<preceq> Inl y \<longleftrightarrow> x \<preceq> y\<close>
  \<open>\<And>x y. Inr x \<preceq> Inr y \<longleftrightarrow> x \<preceq> y\<close>
  \<open>\<And>x y. Inl x \<preceq> Inr y \<longleftrightarrow> False\<close>
  \<open>\<And>x y. Inr x \<preceq> Inl y \<longleftrightarrow> False\<close>
  by (simp add: less_eq_sepadd_def)+

lemma less_sepadd_sum_simps[simp]:
  \<open>\<And>x y. Inl x \<prec> Inl y \<longleftrightarrow> x \<prec> y\<close>
  \<open>\<And>x y. Inr x \<prec> Inr y \<longleftrightarrow> x \<prec> y\<close>
  \<open>\<And>x y. Inl x \<prec> Inr y \<longleftrightarrow> False\<close>
  \<open>\<And>x y. Inr x \<prec> Inl y \<longleftrightarrow> False\<close>
  by (simp add: less_sepadd_def)+

subsection \<open> mu_sep_alg \<close>

instantiation sum :: (multiunit_sep_alg,multiunit_sep_alg) multiunit_sep_alg
begin

definition unitof_sum :: \<open>'a + 'b \<Rightarrow> 'a + 'b\<close> where
  \<open>unitof_sum \<equiv> map_sum unitof unitof\<close>

lemmas unitof_simps[simp] =
  map_sum.simps[
    of \<open>unitof :: 'a \<Rightarrow> _\<close> \<open>unitof :: 'b \<Rightarrow> _\<close>,
    unfolded unitof_sum_def[symmetric]]

instance
  apply standard
    apply (case_tac a; simp)
   apply (case_tac a; case_tac b; simp)
  apply (fastforce simp add: less_eq_sum_def le_iff_sepadd disjoint_sum_def)
  done

end

subsection \<open> Extended instances \<close>

instance sum :: (dupcl_perm_alg, dupcl_perm_alg) dupcl_perm_alg
  apply standard
  apply (simp add: disjoint_sum_def)
  apply (elim disjE exE conjE; force dest: dup_sub_closure)
  done


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
    case a of None \<Rightarrow> True | Some x \<Rightarrow>
      (case b of None \<Rightarrow> False | Some y \<Rightarrow> x \<preceq> y)\<close>

lemma less_eq_option_simps[simp]:
  \<open>None \<le> a\<close>
  \<open>Some x \<le> None \<longleftrightarrow> False\<close>
  \<open>Some x \<le> Some y \<longleftrightarrow> x \<preceq> y\<close>
  by (simp add: less_eq_option_def)+

lemma less_eq_option_def2:
  \<open>a \<le> b \<longleftrightarrow> a = None \<or> (b \<noteq> None \<and> the a \<preceq> the b)\<close>
  by (cases a; cases b; simp)

definition less_option :: \<open>'a option \<Rightarrow> 'a option \<Rightarrow> bool\<close> where
  \<open>less_option a b \<equiv>
    case a of None \<Rightarrow> b \<noteq> None | Some x \<Rightarrow>
      (case b of None \<Rightarrow> False | Some y \<Rightarrow> x \<prec> y)\<close>

lemma less_option_simps[simp]:
  \<open>None < Some x\<close>
  \<open>a < None \<longleftrightarrow> False\<close>
  \<open>Some x < Some y \<longleftrightarrow> x \<prec> y\<close>
  by (simp add: less_option_def split: option.splits)+

lemma less_option_def2:
  \<open>a < b \<longleftrightarrow> b \<noteq> None \<and> (a = None \<or> the a \<prec> the b)\<close>
  by (cases a; cases b; simp)

definition disjoint_option :: \<open>'a option \<Rightarrow> 'a option \<Rightarrow> bool\<close> where
  \<open>disjoint_option a b \<equiv>
    case a of None \<Rightarrow> True | Some x \<Rightarrow>
      (case b of None \<Rightarrow> True | Some y \<Rightarrow> x ## y)\<close>

lemma disjoint_option_simps[simp]:
  \<open>Some x ## Some y \<longleftrightarrow> x ## y\<close>
  \<open>None ## b\<close>
  \<open>a ## None\<close>
  by (simp add: disjoint_option_def split: option.splits)+

lemma disjoint_option_iff:
  \<open>Some x ## b \<longleftrightarrow> b = None \<or> (\<exists>y. b = Some y \<and> x ## y)\<close>
  \<open>a ## Some y \<longleftrightarrow> a = None \<or> (\<exists>x. a = Some x \<and> x ## y)\<close>
  by (simp add: disjoint_option_def split: option.splits)+

lemma disjoint_option_def2:
  \<open>a ## b \<longleftrightarrow> a = None \<or> b = None \<or> the a ## the b\<close>
  by (cases a; cases b; simp)

definition plus_option :: \<open>'a option \<Rightarrow> 'a option \<Rightarrow> 'a option\<close> where
  \<open>plus_option a b \<equiv>
    case a of None \<Rightarrow> b | Some x \<Rightarrow>
      (case b of None \<Rightarrow> a | Some y \<Rightarrow> Some (x + y))\<close>

lemma plus_option_simps[simp]:
  \<open>Some x + Some y = Some (x + y)\<close>
  \<open>None + b = b\<close>
  \<open>a + None = a\<close>
  by (simp add: plus_option_def split: option.splits)+

lemma plus_option_iff:
  \<open>Some x + b = Some z \<longleftrightarrow> (b = None \<and> x = z \<or> (\<exists>y. b = Some y \<and> z = x + y))\<close>
  \<open>a + Some y = Some z \<longleftrightarrow> (a = None \<and> y = z \<or> (\<exists>x. a = Some x \<and> z = x + y))\<close>
  \<open>a + b = None \<longleftrightarrow> a = None \<and> b = None\<close>
  by (force simp add: disjoint_option_def plus_option_def split: option.splits)+

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
                apply (metis less_eq_option_def2 less_option_def2 resource_order.strict_iff_not)
               apply (force simp add: less_eq_option_def2)
              apply (force simp add: less_eq_option_def2)
             apply (force simp add: less_eq_option_def2)
            apply (simp add: disjoint_option_def plus_option_def partial_add_assoc
      split: option.splits; fail)
           apply (simp add: disjoint_option_def plus_option_def split: option.splits,
      metis partial_add_commute; fail)
          apply (metis disjoint_option_def2 disjoint_sym)
         apply (simp add: less_option_def disjoint_option_def split: option.splits,
      metis disjoint_add_rightL; fail)
        apply (simp add: less_option_def disjoint_option_def disjoint_sym_iff
      disjoint_add_right_commute split: option.splits; fail)
       apply (simp add: less_option_def disjoint_option_def positivity split: option.splits; fail)
      apply (simp; fail)
     apply (simp; fail)
    apply (force simp add: less_eq_option_def fun_eq_iff disjoint_option_def less_eq_sepadd_def'
      split: option.splits)
   apply (force simp add: less_eq_option_def)+
  done

end

lemma less_eq_sepadd_option_simps[simp]:
  \<open>None \<preceq> a\<close>
  \<open>Some x \<preceq> None \<longleftrightarrow> False\<close>
  \<open>Some x \<preceq> Some y \<longleftrightarrow> x \<preceq> y\<close>
  by (force simp add: less_eq_sepadd_def' disjoint_option_iff)+

lemma less_sepadd_option_simps[simp]:
  \<open>a \<prec> None \<longleftrightarrow> False\<close>
  \<open>None \<prec> Some x\<close>
  \<open>Some x \<prec> Some y \<longleftrightarrow> x \<prec> y\<close>
  by (simp add: less_sepadd_def' disjoint_option_iff plus_option_iff; blast?; force)+


subsection \<open> Extended instances \<close>

instance option :: (dupcl_perm_alg) dupcl_perm_alg
  by standard
    (simp add: less_option_def disjoint_option_def split: option.splits,
      metis dup_sub_closure)


section \<open> functions \<close>

instantiation "fun" :: (type, perm_alg) perm_alg
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

instance
  apply standard
       apply (simp add: disjoint_fun_def plus_fun_def fun_eq_iff, metis partial_add_assoc)
      apply (simp add: disjoint_fun_def plus_fun_def fun_eq_iff, metis partial_add_commute)
     apply (simp add: disjoint_fun_def, metis disjoint_sym)
    apply (simp add: disjoint_fun_def plus_fun_def, metis disjoint_add_rightL)
   apply (simp add: disjoint_fun_def plus_fun_def, metis disjoint_add_right_commute)
  apply (simp add: disjoint_fun_def plus_fun_def fun_eq_iff, metis positivity)
  done

end

instantiation "fun" :: (type, multiunit_sep_alg) multiunit_sep_alg
begin
 
definition unitof_fun :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)\<close> where
  \<open>unitof_fun f \<equiv> \<lambda>x. unitof (f x)\<close>
declare unitof_fun_def[simp]

instance
  by standard
    (simp add: disjoint_fun_def plus_fun_def le_fun_def fun_eq_iff le_iff_sepadd; metis)+

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


subsection \<open> Extended instances \<close>

instance "fun" :: (type, dupcl_perm_alg) dupcl_perm_alg
  by standard
    (simp add: disjoint_fun_def plus_fun_def fun_eq_iff,
      metis dup_sub_closure)

instance "fun" :: (type, cancel_perm_alg) cancel_perm_alg
  by standard
    (simp add: disjoint_fun_def plus_fun_def fun_eq_iff)


section \<open> Discrete Algebra \<close>

typedef 'a discr = \<open>UNIV :: 'a set\<close>
  morphisms the_discr Discr
  by blast

lemmas Discr_inverse_iff[simp] = Discr_inverse[simplified]
lemmas Discr_inject_iff[simp] = Discr_inject[simplified]

instantiation discr :: (type) order
begin

definition less_eq_discr :: \<open>'a discr \<Rightarrow> 'a discr \<Rightarrow> bool\<close> where
  \<open>less_eq_discr a b \<equiv> the_discr a = the_discr b\<close>
declare less_eq_discr_def[simp]

definition less_discr :: \<open>'a discr \<Rightarrow> 'a discr \<Rightarrow> bool\<close> where
  \<open>less_discr a b \<equiv> False\<close>
declare less_discr_def[simp]

instance
  by standard (simp add: the_discr_inject)+

end

instantiation discr :: (type) perm_alg
begin

definition plus_discr :: \<open>'a discr \<Rightarrow> 'a discr \<Rightarrow> 'a discr\<close> where
  \<open>plus_discr a b \<equiv> a\<close>
declare plus_discr_def[simp]

definition disjoint_discr :: \<open>'a discr \<Rightarrow> 'a discr \<Rightarrow> bool\<close> where
  \<open>disjoint_discr a b \<equiv> a = b\<close>
declare disjoint_discr_def[simp]

instance
  by standard (force simp add: the_discr_inject)+

end

lemma less_eq_discr_iff[simp]:
  \<open>Discr x \<preceq> Discr y \<longleftrightarrow> x = y\<close>
  by (simp add: less_eq_sepadd_def')

instantiation discr :: (type) multiunit_sep_alg
begin

definition unitof_discr :: \<open>'a discr \<Rightarrow> 'a discr\<close> where
  \<open>unitof_discr x = x\<close>
declare unitof_discr_def[simp]

instance
  by standard
    (force simp add: the_discr_inject)+

end

section \<open> Fractional FPermissions \<close>

typedef(overloaded) ('a::linordered_semidom) fperm = \<open>{x. (0::'a) < x \<and> x \<le> 1}\<close>
  morphisms fperm_val FPerm
  using zero_less_one by blast

setup_lifting type_definition_fperm

lemmas FPerm_inverse_iff[simp] = FPerm_inverse[simplified]
lemmas FPerm_inject_iff[simp] = FPerm_inject[simplified]
lemmas fperm_val_inject_rev = fperm_val_inject[symmetric]

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

instantiation fperm :: (linordered_semidom) order
begin

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

instance
  apply standard
     apply (force simp add: less_eq_fperm_def less_fperm_def)+
  apply (fastforce simp add: less_eq_fperm_def fperm_val_inject)
  done

end

instantiation fperm :: (linordered_semidom) perm_alg
begin

definition disjoint_fperm :: \<open>'a fperm \<Rightarrow> 'a fperm \<Rightarrow> bool\<close> where
  \<open>disjoint_fperm a b \<equiv> fperm_val a + fperm_val b \<le> 1\<close>

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
       apply (force simp add: fperm_val_inject_rev add.assoc disjoint_fperm_def plus_fperm.rep_eq)
      apply (force simp add: fperm_val_inject_rev add.commute disjoint_fperm_def plus_fperm.rep_eq)
     apply (simp add: disjoint_fperm_def add.commute; fail)
    apply (simp add: disjoint_fperm_def plus_fperm.rep_eq add.assoc[symmetric])
    apply (metis fperm_val_conditions(1) ge0_plus_le_then_left_le add_pos_pos order_less_imp_le)
   apply (simp add: disjoint_fperm_def plus_fperm.rep_eq add.left_commute min.coboundedI2
      min_add_distrib_right; fail)
  apply (metis disjoint_fperm_def plus_fperm.rep_eq fperm_val_conditions(1) less_add_same_cancel1
      min.absorb2 not_less_iff_gr_or_eq)
  done


lemma fprem_leq_is_resource_leq:
  \<open>((\<le>) :: 'a fperm \<Rightarrow> 'a fperm \<Rightarrow> bool) = (\<preceq>)\<close>
  apply (clarsimp simp add: fun_eq_iff less_eq_fperm_def less_eq_sepadd_def' plus_fperm_def
      disjoint_fperm_def fperm_val_add_gt0 fperm_val_inject_rev)
  apply (metis FPerm_inverse_iff order.refl dual_order.strict_iff_order fperm_val_conditions
      fperm_val_less_then_fperm_conditions_sub2(2) le_add_diff_inverse less_add_same_cancel1
      min.absorb2)
  done

lemma fperm_less_is_resource_less:
  \<open>((<) :: 'a fperm \<Rightarrow> 'a fperm \<Rightarrow> bool) = (\<prec>)\<close>
    apply (clarsimp simp add: fun_eq_iff less_fperm_def less_sepadd_def' plus_fperm_def
      disjoint_fperm_def fperm_val_add_gt0 fperm_val_inject_rev)
  apply (metis FPerm_inverse_iff order.strict_iff_order fperm_val_conditions less_add_same_cancel1
      fperm_val_less_then_fperm_conditions_sub(2) le_add_diff_inverse min.absorb2)
  done

end


subsection \<open> Extended instances \<close>

instance fperm :: (linordered_semidom) dupcl_perm_alg
  apply standard
  apply (simp add: disjoint_fperm_def plus_fperm_eq FPerm_eq_iff fperm_val_conditions)
  apply (metis FPerm_inverse_iff add_cancel_right_right fperm_val_add_gt0 fperm_val_never_zero)
  done


section \<open> Error monad \<close>

datatype 'a error =
  Val (the_val: 'a)
  | Error

instantiation error :: (ord) ord
begin

fun less_eq_error :: \<open>'a error \<Rightarrow> 'a error \<Rightarrow> bool\<close> where
  \<open>less_eq_error _ Error = True\<close>
| \<open>less_eq_error Error (Val b) = False\<close>
| \<open>less_eq_error (Val a) (Val b) = (a \<le> b)\<close>

lemma less_eq_error_def:
  \<open>a \<le> b =
    (case b of
      Error \<Rightarrow> True
    | Val b \<Rightarrow>
      (case a of
        Error \<Rightarrow> False
      | Val a \<Rightarrow> a \<le> b))\<close>
  by (cases a; cases b; force)

fun less_error :: \<open>'a error \<Rightarrow> 'a error \<Rightarrow> bool\<close> where
  \<open>less_error Error _ = False\<close>
| \<open>less_error (Val a) Error = True\<close>
| \<open>less_error (Val a) (Val b) = (a < b)\<close>

lemma less_error_def:
  \<open>a < b =
    (case a of
      Error \<Rightarrow> False
    | Val a \<Rightarrow>
      (case b of
        Error \<Rightarrow> True
      | Val b \<Rightarrow> a < b))\<close>
  by (cases a; cases b; force)

instance proof qed

end

instantiation error :: (preorder) preorder
begin

instance proof
  fix x y z :: \<open>'a :: preorder error\<close>
  show \<open>(x < y) = (x \<le> y \<and> \<not> y \<le> x)\<close>
    by (simp add: less_eq_error_def less_error_def error.case_eq_if less_le_not_le)
  show \<open>x \<le> x\<close>
    by (simp add: less_eq_error_def error.case_eq_if)
  show \<open>x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z\<close>
    by (force dest: order_trans simp add: less_eq_error_def split: error.splits)
qed

end


instantiation error :: (order) order_top
begin

definition \<open>top_error \<equiv> Error\<close>

instance proof
  fix x y z :: \<open>'a :: order error\<close>
  show \<open>x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y\<close>
    by (simp add: less_eq_error_def split: error.splits)
  show \<open>x \<le> top\<close>
    by (simp add: top_error_def)
qed

end

instantiation error :: (order_bot) order_bot
begin

definition \<open>bot_error = Val bot\<close>

instance proof
  fix a :: \<open>'a :: order_bot error\<close>
  show \<open>\<bottom> \<le> a\<close>
    by (simp add: bot_error_def less_eq_error_def error.case_eq_if)
qed

end

instantiation error :: (all_disjoint_perm_alg) perm_alg
begin

definition disjoint_error :: \<open>'a error \<Rightarrow> 'a error \<Rightarrow> bool\<close> where
  \<open>disjoint_error a b \<equiv>
    a = Error \<or> b = Error \<or> (\<exists>x y. a = Val x \<and> b = Val y \<and> x ## y)\<close>

lemma disjoint_error_def2:
  \<open>a ## b \<longleftrightarrow> a = Error \<or> b = Error \<or> the_val a ## the_val b\<close>
  by (simp add: disjoint_error_def, metis error.exhaust)

lemma disjoint_error_simps[simp]:
  \<open>Error ## b\<close>
  \<open>a ## Error\<close>
  \<open>Val x ## Val y \<longleftrightarrow> x ## y\<close>
  by (simp add: disjoint_error_def)+


definition plus_error :: \<open>'a error \<Rightarrow> 'a error \<Rightarrow> 'a error\<close> where
  \<open>a + b \<equiv> case a of Val x \<Rightarrow> (case b of Val y \<Rightarrow> Val (x + y) | Error \<Rightarrow> Error) | Error \<Rightarrow> Error\<close>

lemma plus_error_def2:
  \<open>a + b = (if a = Error \<or> b = Error then Error else Val (the_val a + the_val b))\<close>
  by (simp add: error.case_eq_if plus_error_def)

lemma plus_error_simps[simp]:
  \<open>Error + b = Error\<close>
  \<open>a + Error = Error\<close>
  \<open>Val x + Val y = Val (x + y)\<close>
  by (force simp add: plus_error_def split: error.splits)+


instance
  apply standard
       apply (force simp add: disjoint_error_def plus_error_def partial_add_assoc
      split: error.splits)
      apply (force simp add: disjoint_error_def plus_error_def partial_add_commute
      split: error.splits)
     apply (force simp add: disjoint_error_def plus_error_def disjoint_sym_iff)
    apply (simp add: disjoint_error_def plus_error_def disjoint_add_rightL split: error.splits;
      metis error.exhaust)
   apply (force simp add: disjoint_add_right_commute disjoint_error_def)
  apply (force simp add: disjoint_error_def positivity)
  done

end


section \<open> Heaps and Permission-heaps \<close>

type_synonym ('i,'v) heap = \<open>'i \<rightharpoonup> (munit \<times> 'v discr)\<close>

type_synonym ('i,'v) perm_heap = \<open>'i \<rightharpoonup> (rat fperm \<times> 'v discr)\<close>

(* this also works for resources *)
definition points_to :: \<open>'a \<Rightarrow> 'b \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> bool\<close> (infix \<open>\<^bold>\<mapsto>\<close> 55) where
  \<open>p \<^bold>\<mapsto> v \<equiv> \<lambda>h. h p = Some v\<close>


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