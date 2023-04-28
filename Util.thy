theory Util
  imports Main
begin

unbundle lattice_syntax

section \<open>Helper Lemmas\<close>

subsection \<open>Logic\<close>

lemmas conj_left_mp[simp] = SMT.verit_bool_simplify(7)
lemmas conj_right_mp[simp] = SMT.verit_bool_simplify(8)

lemma conj_imp_distribR:
  \<open>(p \<longrightarrow> q) \<and> r \<longleftrightarrow> (\<not> p \<and> r) \<or> (q \<and> r)\<close>
  by force

lemma conj_imp_distribL:
  \<open>p \<and> (q \<longrightarrow> r) \<longleftrightarrow> (p \<and> \<not> q) \<or> (p \<and> r)\<close>
  by force

lemma all_simps2[simp]:
  \<open>(\<forall>x y. P y \<longrightarrow> Q x y) = (\<forall>y. P y \<longrightarrow> (\<forall>x. Q x y))\<close>
  by force

lemma all_conj_ex1:
  \<open>(\<forall>x. P x \<longrightarrow> Q x) \<and> Ex P \<longleftrightarrow> (\<exists>x. P x \<and> Q x) \<and> (\<forall>x. P x \<longrightarrow> Q x)\<close>
  by blast

lemma exsome_conj_some_imp:
  \<open>(\<exists>x. y = Some x) \<and> (\<forall>x. y = Some x \<longrightarrow> P x) \<longleftrightarrow> (\<exists>x. y = Some x \<and> P x)\<close>
  by blast

lemma prod_eq_decompose:
  \<open>a = (b,c) \<longleftrightarrow> fst a = b \<and> snd a = c\<close>
  \<open>(b,c) = a \<longleftrightarrow> fst a = b \<and> snd a = c\<close>
  by force+

lemma upt_add_eq_append:
  assumes \<open>i \<le> j\<close> \<open>j \<le> k\<close>
  shows \<open>[i..<k] = [i..<j] @ [j..<k]\<close>
  using assms
proof (induct k arbitrary: i j)
  case 0 then show ?case by simp
next
  case (Suc k)
  show ?case
  proof (cases \<open>j \<le> k\<close>)
    case True
    have \<open>[i..<Suc k] = [i..<k] @ [k]\<close>
      using Suc.prems True
      by simp
    also have \<open>... = [i..<j] @ [j..<k] @ [k]\<close>
      using Suc.prems True
      by (subst Suc.hyps[where j=j]; simp)
    also have \<open>... = [i..<j] @ [j..<Suc k]\<close>
      using True
      by simp
    finally show ?thesis .
  next
    case False
    then show ?thesis
      using Suc.prems
      by (clarsimp simp add: le_Suc_eq)
  qed
qed

subsection \<open> Function Properties \<close>

lemmas bij_betw_disjoint_insert =
  bij_betw_disjoint_Un[where A=\<open>{b}\<close> and C=\<open>{d}\<close> for b d, simplified]

lemma bij_betw_insert_ignore:
  \<open>bij_betw f B D \<Longrightarrow> b \<in> B \<Longrightarrow> d \<in> D \<Longrightarrow> bij_betw f (insert b B) (insert d D)\<close>
  by (simp add: insert_absorb)

lemma bij_betw_singleton:
  \<open>f a = b \<Longrightarrow> bij_betw f {a} {b}\<close>
  by (simp add: bij_betw_def)

lemmas bij_betw_combine_insert =
  bij_betw_combine[where A=\<open>{b}\<close> and B=\<open>{d}\<close> for b d, simplified]

subsection \<open> Options \<close>

lemma not_eq_None[simp]: \<open>None \<noteq> x \<longleftrightarrow> (\<exists>z. x = Some z)\<close>
  using option.exhaust_sel by auto

text \<open> We need to do this with cases to avoid infinite simp loops \<close>
lemma option_eq_iff:
  \<open>x = y \<longleftrightarrow> (case x of
                None \<Rightarrow> (case y of None \<Rightarrow> True | Some _ \<Rightarrow> False)
              | Some x' \<Rightarrow> (case y of None \<Rightarrow> False | Some y' \<Rightarrow> x' = y'))\<close>
  by (force split: option.splits)

subsection \<open> Partial Maps \<close>

lemma map_le_restrict_eq: \<open>ma \<subseteq>\<^sub>m mb \<Longrightarrow> mb |` dom ma = ma\<close>
  by (rule ext, metis domIff map_le_def restrict_map_def)

lemma map_restrict_un_eq:
  \<open>m |` (A \<union> B) = m |` A ++ m |` B\<close>
  by (force simp add: restrict_map_def map_add_def split: option.splits)

lemma map_le_split:
  assumes \<open>ma \<subseteq>\<^sub>m mb\<close>
  shows \<open>mb = ma ++ mb |` (- dom ma)\<close>
  using assms
  by (subst map_le_restrict_eq[OF assms, symmetric], force simp add: map_restrict_un_eq[symmetric])

lemma map_disjoint_dom_cancel_right:
  assumes disjoint_ac: \<open>dom a \<inter> dom c = {}\<close>
    and disjoint_ac: \<open>dom b \<inter> dom c = {}\<close>
  shows \<open>(a ++ c = b ++ c) \<longleftrightarrow> a = b\<close>
  using assms
  by (metis (no_types, lifting) Int_Un_distrib Int_commute Un_Int_eq(3)
      disjoint_ac dom_map_add map_add_comm map_le_iff_map_add_commute map_le_restrict_eq)

lemma map_disjoint_dom_cancel_left:
  assumes disjoint_ac: \<open>dom a \<inter> dom b = {}\<close>
    and disjoint_ac: \<open>dom a \<inter> dom c = {}\<close>
  shows \<open>(a ++ b = a ++ c) \<longleftrightarrow> b = c\<close>
  using assms
  by (metis (no_types, lifting) Int_Un_distrib Int_commute Un_Int_eq(3)
      disjoint_ac dom_map_add map_add_comm map_le_iff_map_add_commute map_le_restrict_eq)

lemma le_map_le_iff_sepadd:
  \<open>(a \<subseteq>\<^sub>m b) = (\<exists>c. dom a \<inter> dom c = {} \<and> b = a ++ c)\<close>
  by (metis dom_restrict inf_compl_bot_right map_add_comm map_le_map_add map_le_split)

lemma disjoint_dom_map_add_restrict_distrib:
  \<open>dom a \<inter> dom b = {} \<Longrightarrow> (a ++ b) |` A = a |` A ++ b |` A\<close>
  by (simp add: fun_eq_iff restrict_map_def map_add_def)

lemma antidom_restrict_eq[simp]:
  \<open>a |` (- dom a) = Map.empty\<close>
  by (force simp add: restrict_map_def subset_iff domIff)

lemma dom_subset_restrict_eq:
  \<open>dom a \<subseteq> A \<Longrightarrow>  a |` A = a\<close>
  by (force simp add: restrict_map_def subset_iff domIff)

lemmas dom_disjoint_restrict_eq =
  dom_subset_restrict_eq[OF iffD1[OF disjoint_eq_subset_Compl]]

subsection \<open>Sets\<close>

lemma disjoint_equiv_iff_eq:
  \<open>(\<forall>C. A \<inter> C = {} \<longleftrightarrow> B \<inter> C = {}) \<longleftrightarrow> A = B\<close>
  by blast

lemma surj_disjoint_equiv_iff_eq:
  \<open>surj f \<Longrightarrow> (\<forall>x. A \<inter> f x = {} \<longleftrightarrow> B \<inter> f x = {}) \<longleftrightarrow> A = B\<close>
  by (metis disjoint_equiv_iff_eq surjD)

subsection \<open> Relations \<close>

lemma transp_subrel_compp_smaller:
  \<open>transp S \<Longrightarrow> R \<le> S \<Longrightarrow> S OO R \<le> S\<close>
  \<open>transp S \<Longrightarrow> R \<le> S \<Longrightarrow> R OO S \<le> S\<close>
  by (meson order.refl order.trans relcompp_mono transp_relcompp_less_eq)+

lemma rel_le_rtranscp_relcompp_absorb:
  \<open>R \<le> S \<Longrightarrow> S\<^sup>*\<^sup>* OO R\<^sup>*\<^sup>* = S\<^sup>*\<^sup>*\<close>
  \<open>R \<le> S \<Longrightarrow> R\<^sup>*\<^sup>* OO S\<^sup>*\<^sup>* = S\<^sup>*\<^sup>*\<close>
   apply -
   apply (rule antisym)
    apply (metis rtranclp_mono transp_rtranclp transp_subrel_compp_smaller(1))
   apply force
  apply (rule antisym)
   apply (simp add: rtranclp_mono transp_subrel_compp_smaller(2))
  apply force
  done

lemma not_Some_prod_eq[iff]: \<open>(\<forall>a b. x \<noteq> Some (a,b)) \<longleftrightarrow> x = None\<close>
  by (metis not_eq_None prod.collapse)

lemma not_Some_prodprod_eq[iff]: \<open>(\<forall>a b c. x \<noteq> Some ((a,b),c)) \<longleftrightarrow> x = None\<close>
  by (metis not_eq_None prod.collapse)

lemmas rev_finite_subset_Collect =
  rev_finite_subset[of \<open>Collect P\<close> \<open>Collect Q\<close> for P Q, OF _ iffD2[OF Collect_mono_iff]]

(* We can prove the existence of a map satisfying a relation by showing
    the relation is nice and that there exists a value for every input.
*)
lemma finite_map_choice_iff:
  shows \<open>(\<exists>f. finite (dom f) \<and> (\<forall>x. P x (f x))) \<longleftrightarrow>
          (finite {x. (\<exists>y. P x (Some y)) \<and> \<not> P x None} \<and> (\<forall>x. \<exists>y. P x y))\<close>
  apply -
  apply (rule iffI)
  subgoal (* 1 \<Longrightarrow> 2 *)
    apply (clarsimp simp add: dom_def)
    apply (subgoal_tac \<open>(\<forall>x. f x = None \<longrightarrow> P x None) \<and> (\<forall>x y. f x = Some y \<longrightarrow> P x (Some y))\<close>)
     prefer 2
     apply metis
    apply (rule conjI)
     apply (rule rev_finite_subset, assumption)
     apply blast
    apply force
    done
  subgoal (* 2 \<Longrightarrow> 1 *)
    apply (clarsimp simp add: dom_def)
    apply (clarsimp simp add: choice_iff)
    apply (rule_tac x=\<open>\<lambda>x. if \<exists>y. P x (Some y) \<and> \<not> P x None then f x else None\<close> in exI)
    apply (rule conjI)
     apply clarsimp
     apply (simp add: rev_finite_subset_Collect)
    apply (simp, metis option.exhaust_sel)
    done
  done

subsection \<open> Arithmetic \<close>

lemma ex_times_k_iff:
  fixes a :: \<open>'a :: division_ring\<close>
  assumes \<open>k \<noteq> 0\<close>
  shows \<open>(\<exists>x. a = x * k \<and> P x) \<longleftrightarrow> P (a / k)\<close>
  using assms
  by (metis eq_divide_eq)

lemma max_eq_k_iff:
  fixes a b :: \<open>'a :: linorder\<close>
  shows \<open>(max a b = k) = (a = k \<and> b \<le> k \<or> a \<le> k \<and> b = k)\<close>
  by (simp add: eq_iff le_max_iff_disj)

lemma min_eq_k_iff:
  fixes a b :: \<open>'a :: linorder\<close>
  shows \<open>(min a b = k) = (a = k \<and> k \<le> b \<or> k \<le> a \<and> b = k)\<close>
  by (simp add: eq_iff min_le_iff_disj)

lemma field_All_mult_inverse_iff:
  fixes x k :: \<open>'a :: field\<close>
  shows \<open>k \<noteq> 0 \<Longrightarrow> (\<forall>y. x = y * k \<longrightarrow> P y) \<longleftrightarrow> P (x / k)\<close>
  by fastforce

lemma zero_less_plus_positive:
  fixes a b :: \<open>'a :: {order,monoid_add}\<close>
  shows \<open>0 < a + b \<Longrightarrow> 0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> 0 < a \<or> 0 < b\<close>
  by force

lemma ordered_ab_group_add_ge0_le_iff_add:
  fixes a b :: \<open>'a :: ordered_ab_group_add\<close>
  shows \<open>(a \<le> b) = (\<exists>c\<ge>0. b = a + c)\<close>
  by (metis add.commute diff_add_cancel le_add_same_cancel1)

lemma linordered_semidom_ge0_le_iff_add:
  fixes a b :: \<open>'a :: {linordered_semidom}\<close>
  shows \<open>(a \<le> b) = (\<exists>c\<ge>0. b = a + c)\<close>
  by (metis le_add_diff_inverse le_add_same_cancel1)


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

sublocale monoid seq skip
  by standard (simp add: seq_assoc)+

end

lemma ordered_comm_monoid_add_add_min_assoc:
  fixes x y z k :: \<open>'a :: ordered_comm_monoid_add\<close>
  assumes \<open>x \<ge> 0\<close> \<open>z \<ge> 0\<close>
  shows \<open>min k (min k (x + y) + z) = min k (x + min k (y + z))\<close>
  using assms
  by (clarsimp simp add: min_def add.commute add.left_commute add_increasing add_increasing2 eq_iff,
      metis add.assoc add_increasing2)

section \<open>Top Extension\<close>

datatype 'a top_ext =
    Top | TEVal 'a

lemma not_TEVal_eq[simp]: \<open>(\<forall>x. a \<noteq> TEVal x) \<longleftrightarrow> a = Top\<close>
  by (meson top_ext.distinct top_ext.exhaust)

lemma not_Top_all_TEVal_iff: \<open>a \<noteq> Top \<Longrightarrow> (\<forall>x. a = TEVal x \<longrightarrow> Q x) \<longleftrightarrow> (\<exists>x. a = TEVal x \<and> Q x)\<close>
  using not_TEVal_eq by blast

instantiation top_ext :: (order) order_top
begin

definition \<open>top_top_ext \<equiv> Top\<close>
definition \<open>less_eq_top_ext a b \<equiv> b = Top \<or> (\<exists>b'. b = TEVal b' \<and> (\<exists>a'. a = TEVal a' \<and> a' \<le> b'))\<close>
definition \<open>less_top_ext a b \<equiv> b = Top \<and> a \<noteq> Top \<or> (\<exists>b'. b = TEVal b' \<and> (\<exists>a'. a = TEVal a' \<and> a' < b'))\<close>

instance
  by standard
    (force simp add: less_eq_top_ext_def less_top_ext_def top_top_ext_def)+
                      
lemmas Top_greatest[simp] =
  HOL.subst[OF meta_eq_to_obj_eq[OF top_top_ext_def], where P=\<open>(\<le>) a\<close> for a, OF top_greatest]

end

instantiation top_ext :: (plus) plus
begin
definition \<open>plus_top_ext a b \<equiv>
              case a of
                TEVal a' \<Rightarrow> 
                  (case b of
                    TEVal b' \<Rightarrow> TEVal (a' + b')
                  | Top \<Rightarrow> Top)
                | Top \<Rightarrow> Top\<close>
instance by standard
end

instance top_ext :: (semigroup_add) semigroup_add
  by standard
    (simp add: plus_top_ext_def add.assoc split: top_ext.splits)+

instantiation top_ext :: (zero) zero
begin
definition \<open>zero_top_ext \<equiv> TEVal 0\<close>
instance by standard
end

instance top_ext :: (monoid_add) monoid_add
  by standard
    (simp add: plus_top_ext_def zero_top_ext_def split: top_ext.splits)+

instance top_ext :: (ab_semigroup_add) ab_semigroup_add
  by standard
    (force simp add: plus_top_ext_def add_ac split: top_ext.splits)+

instance top_ext :: (comm_monoid_add) comm_monoid_add
  by standard
    (force simp add: plus_top_ext_def zero_top_ext_def split: top_ext.splits)+

instance top_ext :: (ordered_ab_semigroup_add) ordered_ab_semigroup_add
  by standard
    (force simp add: plus_top_ext_def zero_top_ext_def less_eq_top_ext_def add_ac
      intro: add_left_mono split: top_ext.splits)+

instance top_ext :: (linorder) linorder
  by (standard, simp add: less_eq_top_ext_def, metis nle_le not_TEVal_eq)

instance top_ext :: (ordered_comm_monoid_add) ordered_comm_monoid_add
  by standard

section \<open>Zero-Bot Extension\<close>

datatype 'a bot_ext = Bot | BEVal 'a

lemma not_BEVal_eq[simp]: \<open>(\<forall>x. a \<noteq> BEVal x) \<longleftrightarrow> a = Bot\<close>
  by (meson bot_ext.distinct bot_ext.exhaust)

instantiation bot_ext :: (ord) ord
begin
definition \<open>less_eq_bot_ext a b \<equiv> (a = Bot \<or> (\<exists>a'. a = BEVal a' \<and> (\<exists>b'. b = BEVal b' \<and> a' \<le> b')))\<close>
definition \<open>less_bot_ext a b \<equiv> (a = Bot \<and> b \<noteq> Bot \<or> (\<exists>a'. a = BEVal a' \<and> (\<exists>b'. b = BEVal b' \<and> a' < b')))\<close>
instance by standard
end

instance bot_ext :: (preorder) preorder
  by standard
    (force simp add: less_eq_bot_ext_def less_bot_ext_def less_le_not_le dest: order.trans)+

instantiation bot_ext :: (order) order_bot
begin
definition \<open>bot_bot_ext \<equiv> Bot\<close>
instance
  by standard
    (force simp add: less_eq_bot_ext_def bot_bot_ext_def)+
end

instance bot_ext :: (linorder) linorder
  by standard
    (simp add: less_eq_bot_ext_def, meson nle_le not_BEVal_eq)

instantiation bot_ext :: (plus) plus
begin
definition
  \<open>plus_bot_ext a b \<equiv>
    (case a of Bot \<Rightarrow> b | BEVal a' \<Rightarrow> (case b of Bot \<Rightarrow> a | BEVal b' \<Rightarrow> BEVal (a' + b')))\<close>
instance by standard
end

instantiation bot_ext :: (type) zero
begin
definition \<open>zero_bot_ext \<equiv> Bot\<close>
instance by standard
end

instance bot_ext :: (semigroup_add) semigroup_add
  by standard
    (force simp add: plus_bot_ext_def add.assoc split: bot_ext.splits)

instance bot_ext :: (ab_semigroup_add) ab_semigroup_add
  by standard
    (force simp add: plus_bot_ext_def add.commute split: bot_ext.splits)

instance bot_ext :: (monoid_add) monoid_add
  by standard
    (force simp add: plus_bot_ext_def zero_bot_ext_def split: bot_ext.splits)+

instance bot_ext :: (comm_monoid_add) comm_monoid_add
  by standard
    (force simp add: plus_bot_ext_def zero_bot_ext_def split: bot_ext.splits)

instantiation bot_ext :: (canonically_ordered_monoid_add) canonically_ordered_monoid_add
begin
instance
  apply standard
  apply (simp add: plus_bot_ext_def zero_bot_ext_def less_eq_bot_ext_def le_iff_add split: bot_ext.splits)+
  apply (case_tac a, force, case_tac b, force)
  apply (simp, metis bot_ext.inject group_cancel.rule0 not_BEVal_eq)
  done
end


end