theory SepLogicInstances
  imports SepLogic
begin

section \<open> Instances \<close>

instantiation prod :: (perm_alg,perm_alg) perm_alg
begin

definition plus_prod  :: \<open>'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b\<close> where
  \<open>plus_prod a b \<equiv> (fst a + fst b, snd a + snd b)\<close>
declare plus_prod_def[simp]

definition disjoint_prod  :: \<open>'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool\<close> where
  \<open>disjoint_prod a b \<equiv> (fst a ## fst b \<and> snd a ## snd b)\<close>
declare disjoint_prod_def[simp]

(* these definitions are horrible because we don't have a 0, and thus can't prove the addition
    property with a pointwise definition. *)
definition less_eq_prod  :: \<open>'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool\<close> where
  \<open>less_eq_prod a b \<equiv>
    a = b \<or>
      ((fst a \<noteq> fst b \<or> snd a \<noteq> snd b) \<and>
        (\<exists>c. fst a ## c \<and> fst b = fst a + c) \<and>
        (\<exists>c. snd a ## c \<and> snd b = snd a + c))\<close>

definition less_prod  :: \<open>'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool\<close> where
  \<open>less_prod a b \<equiv>
    (fst a \<noteq> fst b \<or> snd a \<noteq> snd b) \<and>
      (\<exists>c. fst a ## c \<and> fst b = fst a + c) \<and>
      (\<exists>c. snd a ## c \<and> snd b = snd a + c)\<close>

instance
  apply standard
            apply (simp add: less_prod_def less_eq_prod_def)
            apply (metis order_antisym_conv partial_le_plus)
           apply (force simp add: less_prod_def less_eq_prod_def)
          apply (simp add: less_prod_def less_eq_prod_def, metis disjoint_add_swap2 partial_add_assoc2 prod.expand)
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

definition unitof_prod  :: \<open>'a \<times> 'b \<Rightarrow> 'a \<times> 'b\<close> where
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

instantiation prod  :: (sep_alg,sep_alg) sep_alg
begin

definition zero_prod  :: \<open>'a \<times> 'b\<close> where
  \<open>zero_prod \<equiv> (0, 0)\<close>
declare zero_prod_def[simp]

definition bot_prod  :: \<open>'a \<times> 'b\<close> where
  \<open>bot_prod \<equiv> (\<bottom>, \<bottom>)\<close>
declare bot_prod_def[simp]

instance
  by standard force+

end


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

definition less_eq_option  :: \<open>'a option \<Rightarrow> 'a option \<Rightarrow> bool\<close> where
  \<open>less_eq_option a b \<equiv>
    case a of None \<Rightarrow> True | Some x \<Rightarrow> (case b of None \<Rightarrow> False | Some y \<Rightarrow> x \<le> y)\<close>

lemma less_eq_option_simps[simp]:
  \<open>None \<le> a\<close>
  \<open>Some x \<le> None \<longleftrightarrow> False\<close>
  \<open>Some x \<le> Some y \<longleftrightarrow> x \<le> y\<close>
  by (simp add: less_eq_option_def)+

definition less_option  :: \<open>'a option \<Rightarrow> 'a option \<Rightarrow> bool\<close> where
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


instantiation "fun" :: (type, sep_alg) sep_alg
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
  \<open>unitof_fun f \<equiv> \<lambda>x. 0\<close>
declare unitof_fun_def[simp]

definition zero_fun :: \<open>('a \<Rightarrow> 'b)\<close> where
  \<open>zero_fun \<equiv> \<lambda>x. 0\<close>
declare zero_fun_def[simp]

definition bot_fun :: \<open>('a \<Rightarrow> 'b)\<close> where
  \<open>bot_fun \<equiv> \<lambda>x. 0\<close>
declare bot_fun_def[simp]

instance
  apply standard
             apply (force simp add: disjoint_fun_def plus_fun_def)
            apply (force simp add: disjoint_fun_def plus_fun_def)
           apply (simp add: disjoint_fun_def plus_fun_def fun_eq_iff, metis partial_add_assoc)
          apply (simp add: disjoint_fun_def plus_fun_def fun_eq_iff, metis partial_add_commute)
         apply (simp add: disjoint_fun_def, metis disjoint_sym)
        apply (simp add: disjoint_fun_def plus_fun_def, metis disjoint_add_rightL)
       apply (simp add: disjoint_fun_def plus_fun_def, metis disjoint_add_right_commute)
      apply (simp add: disjoint_fun_def plus_fun_def fun_eq_iff, metis positivity)
     apply (simp add: less_fun_def plus_fun_def le_fun_def disjoint_fun_def le_iff_sepadd)
  subgoal
    apply (intro iffI conjI)
       apply blast
      apply metis (* n.b. uses choice *)
     apply blast
    apply (clarsimp, metis less_le less_le_not_le partial_le_plus)
    done
    apply force+
  done

end

end