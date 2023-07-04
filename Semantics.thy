theory Semantics
  imports DeallocHeap
begin

notation(input)
  times (infixl \<open>\<parallel>\<close> 70)

text \<open> A process can be represented as a trace of predicate pairs. \<close>

text \<open> Note: only finite traces at the moment. \<close>
type_synonym 'a pred = \<open>'a \<Rightarrow> bool\<close>

datatype (\<alpha>set: 'a) trace =
  TNil
  | TCons (trhd: 'a) (trtl: "'a trace") (infixr "\<cdot>" 70)
  for
    map: trace_map
    pred: trace_all    
    rel: trace_all2

lemma not_TNil_eq: \<open>a \<noteq> TNil \<longleftrightarrow> (\<exists>ax a'. a = ax \<cdot> a')\<close>
  using trace.exhaust_sel by blast

subsection \<open> Trace Start and End \<close>

fun trace_start :: \<open>'a trace \<Rightarrow> 'a\<close> where
  \<open>trace_start TNil = undefined\<close>
| \<open>trace_start (x \<cdot> _) = x\<close>

fun trace_end :: \<open>'a trace \<Rightarrow> 'a\<close> where
  \<open>trace_end TNil = undefined\<close>
| \<open>trace_end (x \<cdot> TNil) = x\<close>
| \<open>trace_end (_ \<cdot> a) = trace_end a\<close>

subsection \<open> Traces prefix ordered \<close>

instantiation trace :: (type) monoid_add
begin

subsection \<open> trace plus \<close>

definition \<open>zero_trace \<equiv> TNil\<close>

(* concat *)
fun plus_trace :: \<open>'a trace \<Rightarrow> 'a trace \<Rightarrow> 'a trace\<close> where
  \<open>plus_trace TNil b = b\<close>
| \<open>plus_trace (x \<cdot> a) b = x \<cdot> plus_trace a b\<close>

lemma plus_trace_unit_right[simp]:
  \<open>a + TNil = a\<close>
  by (induct a) simp+

lemma trace_start_plus[simp]:
  \<open>trace_start (a + b) = (if a = TNil then trace_start b else trace_start a)\<close>
  by (induct a arbitrary: b)
    (force elim: plus_trace.elims)+

lemma trace_end_plus[simp]:
  \<open>trace_end (a + b) = (if b = TNil then trace_end a else trace_end b)\<close>
  apply (induct a arbitrary: b)
   apply clarsimp
  apply (case_tac \<open>a + b\<close>)
   apply (force elim: plus_trace.elims)
  apply (simp, metis plus_trace_unit_right trace_end.simps(3))
  done

lemma trace_concat_eq_nil_iff[simp]:
  \<open>(a + b) = TNil \<longleftrightarrow> a = TNil \<and> b = TNil\<close>
  \<open>TNil = (a + b) \<longleftrightarrow> a = TNil \<and> b = TNil\<close>
  by (metis trace.discI plus_trace.elims)+

instance
proof standard
  fix a b c :: \<open>'a trace\<close>
  show \<open>a + b + c = a + (b + c)\<close>
    by (induct a arbitrary: b c) force+
  show \<open>0 + a = a\<close>
    by (simp add: zero_trace_def)
  show \<open>a + 0 = a\<close>
    by (simp add: zero_trace_def)
qed

end

instantiation trace :: (type) order
begin

fun less_eq_trace :: \<open>'a trace \<Rightarrow> 'a trace \<Rightarrow> bool\<close> where
  \<open>less_eq_trace (x \<cdot> a) (y \<cdot> b) = ((x = y) \<and> less_eq_trace a b)\<close>
| \<open>less_eq_trace TNil _ = True\<close>
| \<open>less_eq_trace _ _ = False\<close>

lemma le_TNil_iff[simp]:
  \<open>a \<le> TNil \<longleftrightarrow> a = TNil\<close>
  using less_eq_trace.elims(1) by auto

lemma le_TCons_iff:
  \<open>a \<le> y \<cdot> b \<longleftrightarrow> a = TNil \<or> (\<exists>a'. a = y \<cdot> a' \<and> a' \<le> b)\<close>
  using less_eq_trace.elims(2) by auto

lemma TCons_le_iff[simp]:
  \<open>x \<cdot> a \<le> b \<longleftrightarrow> (\<exists>b'. b = x \<cdot> b' \<and> a \<le> b')\<close>
  using less_eq_trace.elims(2) by fastforce


definition less_trace :: \<open>'a trace \<Rightarrow> 'a trace \<Rightarrow> bool\<close> where
  \<open>less_trace a b \<equiv> a \<le> b \<and> \<not> (b \<le> a)\<close>

instance
proof standard
  fix a b c :: \<open>'a trace\<close>
  show \<open>(a < b) = (a \<le> b \<and> \<not> b \<le> a)\<close>
    by (simp add: less_trace_def)
  show \<open>a \<le> a\<close>
    by (induct a) force+
  show \<open>a \<le> b \<Longrightarrow> b \<le> c \<Longrightarrow> a \<le> c\<close>
    apply (induct a b arbitrary: c rule: less_eq_trace.induct)
      apply (metis less_eq_trace.simps(1,3) not_TNil_eq)
     apply simp
    apply simp
    done
  show \<open>a \<le> b \<Longrightarrow> b \<le> a \<Longrightarrow> a = b\<close>
    by (induct a b rule: less_eq_trace.induct) force+
qed

end

lemma trace_le_iff_add:
  fixes a b :: \<open>'a trace\<close>
  shows \<open>a \<le> b \<longleftrightarrow> (\<exists>c. b = a + c)\<close>
  apply (induct b arbitrary: a)
   apply simp
  apply (case_tac a; force)
  done

lemma trace_le_plus_iff:
  fixes a b c :: \<open>'a trace\<close>
  shows \<open>a \<le> c + b \<longleftrightarrow> a \<le> c \<or> (\<exists>a'. a = c + a' \<and> a' \<le> b)\<close>
  by (induct c arbitrary: a b rule: trace.induct) (force simp add: le_TCons_iff)+

instantiation trace :: (type) semilattice_inf
begin

fun inf_trace :: \<open>'a trace \<Rightarrow> 'a trace \<Rightarrow> 'a trace\<close> where
  \<open>inf_trace (x \<cdot> a) (y \<cdot> b) = (if x = y then x \<cdot> (inf_trace a b) else TNil)\<close>
| \<open>inf_trace _ _ = TNil\<close>

lemma inf_trace_cons_left:
  \<open>(x \<cdot> a) \<sqinter> b = (case b of TNil \<Rightarrow> TNil | y \<cdot> b' \<Rightarrow> if x = y then x \<cdot> (a \<sqinter> b') else TNil)\<close>
  by (induct b arbitrary: a) force+

lemma inf_trace_cons_right:
  \<open>a \<sqinter> (y \<cdot> b) = (case a of TNil \<Rightarrow> TNil | x \<cdot> a' \<Rightarrow> if x = y then x \<cdot> (a' \<sqinter> b) else TNil)\<close>
  by (induct a arbitrary: b) force+

instance
proof standard
  fix a b c :: \<open>'a trace\<close>
  show \<open>a \<sqinter> b \<le> a\<close>
    by (induct b arbitrary: a)
      (simp add: inf_trace_cons_right split: trace.splits)+
  show \<open>a \<sqinter> b \<le> b\<close>
    by (induct b arbitrary: a)
      (simp add: inf_trace_cons_right split: trace.splits)+
  show \<open>a \<le> b \<Longrightarrow> a \<le> c \<Longrightarrow> a \<le> b \<sqinter> c\<close>
    by (induct a arbitrary: b c) force+
qed

end

subsection \<open> Custom trace induction rules \<close>

lemma traces2_step_induct[case_names TNil2 TConsL TConsR]:
  \<open>P TNil TNil \<Longrightarrow>
    (\<And>a b x. P a b \<Longrightarrow> P (x \<cdot> a) b) \<Longrightarrow>
    (\<And>a b y. P a b \<Longrightarrow> P a (y \<cdot> b)) \<Longrightarrow>
    P a b\<close>
proof (induct a arbitrary: b)
  case (TNil b)
  then show ?case
    by (induct b) blast+
next
  case TCons
  then show ?case
    by blast
qed

thm trace.induct less_induct

lemma trace_concat_induct[case_names TNil trace_concat]:
  fixes a :: \<open>'a trace\<close>
  shows \<open>P TNil \<Longrightarrow> (\<And>a b. a \<noteq> TNil \<Longrightarrow> P b \<Longrightarrow> P (a + b)) \<Longrightarrow> P a\<close>
  by (induct a) force+

lemma trace_concat_backwards_induct:
  fixes a :: \<open>'a trace\<close>
  shows \<open>P TNil \<Longrightarrow> (\<And>a b. b \<noteq> TNil \<Longrightarrow> P a \<Longrightarrow> P (a + b)) \<Longrightarrow> P a\<close>
proof (induct a rule: trace_concat_induct)
  case TNil
  then show ?case by force
next
  case (trace_concat a b)
  then show ?case
    apply (induct a arbitrary: b)
     apply force
    apply (metis plus_trace.simps(1))
    done
qed


subsection \<open> Parallel Trace Merge \<close>

inductive merge_traces_rel :: \<open>'a trace \<Rightarrow> 'a trace \<Rightarrow> 'a trace \<Rightarrow> bool\<close> where
  mergetr_nil: \<open>merge_traces_rel TNil TNil TNil\<close>
| mergetr_cons_left: \<open>merge_traces_rel a b t \<Longrightarrow> merge_traces_rel (x \<cdot> a) b (x \<cdot> t)\<close>
| mergetr_cons_right: \<open>merge_traces_rel a b t \<Longrightarrow> merge_traces_rel a (y \<cdot> b) (y \<cdot> t)\<close>

inductive_cases mergetr_out_nilE[elim]: \<open>merge_traces_rel a b TNil\<close>

inductive_cases mergetr_left_consE[elim]: \<open>merge_traces_rel (x \<cdot> a) b c\<close>
inductive_cases mergetr_right_consE[elim]: \<open>merge_traces_rel a (x \<cdot> b) c\<close>
inductive_cases mergetr_out_consE[elim]: \<open>merge_traces_rel a b (x \<cdot> c)\<close>

lemma merge_traces_rel_left_TNilD:
  \<open>merge_traces_rel a b c \<Longrightarrow> a = TNil \<Longrightarrow> b = c\<close>
  by (induct rule: merge_traces_rel.induct) simp+

lemma merge_traces_rel_right_TNilD:
  \<open>merge_traces_rel a b c \<Longrightarrow> b = TNil \<Longrightarrow> a = c\<close>
  by (induct rule: merge_traces_rel.induct) simp+

lemma mergetr_left_nilE[elim]:
  \<open>merge_traces_rel TNil b c \<Longrightarrow> (b = c \<Longrightarrow> P) \<Longrightarrow> P\<close>
  by (simp add: merge_traces_rel_left_TNilD)

lemma mergetr_right_nilE[elim]:
  \<open>merge_traces_rel a TNil c \<Longrightarrow> (a = c \<Longrightarrow> P) \<Longrightarrow> P\<close>
  by (simp add: merge_traces_rel_right_TNilD)


lemma mergetr_nil_left[intro!]:
  \<open>merge_traces_rel TNil b b\<close>
  by (induct b) (simp add: mergetr_nil mergetr_cons_right)+

lemma mergetr_nil_right[intro!]:
  \<open>merge_traces_rel a TNil a\<close>
  by (induct a) (simp add: mergetr_nil mergetr_cons_left)+


lemma merge_traces_rel_nil_simps[simp]:
  \<open>merge_traces_rel TNil b c \<longleftrightarrow> b = c\<close>
  \<open>merge_traces_rel a TNil c \<longleftrightarrow> a = c\<close>
  \<open>merge_traces_rel a b TNil \<longleftrightarrow> a = TNil \<and> b = TNil\<close>
  using merge_traces_rel_left_TNilD merge_traces_rel_right_TNilD
  by blast+

lemma merge_traces_rel_cons_LR_iff:
  \<open>merge_traces_rel (x \<cdot> a') (y \<cdot> b') c \<longleftrightarrow>
    (\<exists>c'. merge_traces_rel a' (y \<cdot> b') c' \<and> c = x \<cdot> c') \<or>
    (\<exists>c'. merge_traces_rel (x \<cdot> a') b' c' \<and> c = y \<cdot> c')\<close>
  apply (induct c)
   apply force
  apply (simp, metis mergetr_cons_left mergetr_cons_right mergetr_out_consE trace.inject)
  done

lemma merge_traces_rel_cons_out_iff:
  \<open>merge_traces_rel a b (z \<cdot> c') \<longleftrightarrow>
    (\<exists>a'. merge_traces_rel a' b c' \<and> a = z \<cdot> a') \<or>
    (\<exists>b'. merge_traces_rel a b' c' \<and> b = z \<cdot> b')\<close>
  by (metis mergetr_cons_left mergetr_cons_right mergetr_out_consE)

lemma merge_traces_assoc1:
  assumes
    \<open>merge_traces_rel a b ab\<close>
    \<open>merge_traces_rel ab c abc\<close>
    \<open>a \<in> A\<close> \<open>b \<in> B\<close> \<open>c \<in> C\<close>
  shows
    \<open>\<exists>a\<in>A. \<exists>bc. (\<exists>b\<in>B. \<exists>c\<in>C. merge_traces_rel b c bc) \<and> merge_traces_rel a bc abc\<close>
  using assms
proof (induct abc arbitrary: a b ab c A B C)
  case (TCons x abc)
  then show ?case
    apply (clarsimp simp add: merge_traces_rel_cons_out_iff)
    apply (erule disjE)
     apply (clarsimp simp add: merge_traces_rel_cons_out_iff)
     apply (erule disjE)
      (* Case: \<open>a\<close> takes a step *)
      apply clarsimp
      apply (rename_tac ab' a')
      apply (drule meta_spec, drule meta_spec, drule meta_spec, drule meta_spec)
      apply (drule_tac x=\<open>{a. x \<cdot> a \<in> A}\<close> in meta_spec)
      apply (drule_tac x=B in meta_spec)
      apply (drule_tac x=C in meta_spec)
      apply blast
      (* Case: \<open>b\<close> takes a step *)
     apply clarsimp
     apply (rename_tac ab' b')
     apply (drule meta_spec[of _ a], drule meta_spec, drule meta_spec, drule meta_spec)
     apply (drule meta_spec[of _ A])
     apply (drule meta_spec[of _ \<open>{a. x \<cdot> a \<in> B}\<close>])
     apply (drule meta_spec[of _ C])
     apply (drule meta_mp, assumption)
     apply (drule meta_mp, assumption)
     apply (metis mem_Collect_eq mergetr_cons_left)
      (* Case: \<open>c\<close> takes a step *)
    apply clarsimp
    apply (rename_tac c')
    apply (drule meta_spec[of _ a], drule meta_spec, drule meta_spec, drule meta_spec)
    apply (drule_tac x=A in meta_spec)
    apply (drule_tac x=B in meta_spec)
    apply (drule_tac x=\<open>{c. x \<cdot> c \<in> C}\<close> in meta_spec)
    apply (drule meta_mp, assumption)
    apply (drule meta_mp, assumption)
    apply (metis mem_Collect_eq mergetr_cons_right)
    done
qed simp


lemma merge_traces_assoc2:
  assumes
    \<open>merge_traces_rel b c bc\<close>
    \<open>merge_traces_rel a bc abc\<close>
    \<open>a \<in> A\<close> \<open>b \<in> B\<close> \<open>c \<in> C\<close>
  shows
    \<open>\<exists>ab. (\<exists>a\<in>A. \<exists>b\<in>B. merge_traces_rel a b ab) \<and> (\<exists>c\<in>C. merge_traces_rel ab c abc)\<close>
  using assms
proof (induct abc arbitrary: a b c bc A B C)
  case (TCons x abc)
  then show ?case
    apply (clarsimp simp add: merge_traces_rel_cons_out_iff)
    apply (erule disjE)
     apply clarsimp
      (* Case: \<open>a\<close> takes a step *)
     apply (drule meta_spec[of _ b], drule meta_spec, drule meta_spec, drule meta_spec)
     apply (drule meta_spec[of _ \<open>{t. x \<cdot> t \<in> A}\<close>])
     apply (drule meta_spec[of _ B])
     apply (drule meta_spec[of _ C])
     apply (drule meta_mp, assumption)
     apply (drule meta_mp, assumption)
     apply (simp, metis mergetr_cons_left)
    apply (clarsimp simp add: merge_traces_rel_cons_out_iff)
    apply (erule disjE)
      (* Case: \<open>b\<close> takes a step *)
     apply clarsimp
     apply (rename_tac ab' b')
     apply (drule meta_spec, drule meta_spec[of _ c], drule meta_spec, drule meta_spec)
     apply (drule meta_spec[of _ A])
     apply (drule meta_spec[of _ \<open>{t. x \<cdot> t \<in> B}\<close>])
     apply (drule meta_spec[of _ C])
     apply (drule meta_mp, assumption)
     apply (drule meta_mp, assumption)
     apply (simp, metis mergetr_cons_right)
      (* Case: \<open>c\<close> takes a step *)
    apply clarsimp
    apply (rename_tac c')
    apply (drule meta_spec[of _ b], drule meta_spec, drule meta_spec, drule meta_spec)
    apply (drule meta_spec[of _ A])
    apply (drule meta_spec[of _ B])
    apply (drule meta_spec[of _ \<open>{t. x \<cdot> t \<in> C}\<close>])
    apply blast
    done
qed simp

lemma merge_traces_rel_assoc:
  \<open>{abc. \<exists>ab. (\<exists>a\<in>A. \<exists>b\<in>B. merge_traces_rel a b ab) \<and> (\<exists>c\<in>C. merge_traces_rel ab c abc)} =
    {abc. \<exists>a\<in>A. \<exists>bc. (\<exists>b\<in>B. \<exists>c\<in>C. merge_traces_rel b c bc) \<and> merge_traces_rel a bc abc}\<close>
  apply (clarsimp simp add: set_eq_iff)
  apply (rule iffI)
   apply (clarsimp, blast intro: merge_traces_assoc1)
  apply (clarsimp, blast intro: merge_traces_assoc2)
  done

definition merge_traces :: \<open>'a trace \<Rightarrow> 'a trace \<Rightarrow> 'a trace set\<close> where
  \<open>merge_traces a b \<equiv> Collect (merge_traces_rel a b)\<close>

lemma merge_traces_simp[simp]:
  \<open>merge_traces TNil b = {b}\<close>
  \<open>merge_traces a TNil = {a}\<close>
  \<open>merge_traces (x \<cdot> a) (y \<cdot> b) =
    ((TCons x ` merge_traces a (y \<cdot> b)) \<union> (TCons y ` merge_traces (x \<cdot> a) b))\<close>
    apply (force simp add: merge_traces_def)
   apply (force simp add: merge_traces_def)
  apply (force simp add: merge_traces_def set_eq_iff merge_traces_rel_cons_LR_iff image_def)
  done

lemma merge_traces_induct[case_names TNilL TNilR TCons2]:
  \<open>(\<And>b. P TNil b) \<Longrightarrow>
    (\<And>a. P a TNil) \<Longrightarrow>
    (\<And>a b x y.
      P a (y \<cdot> b) \<Longrightarrow>
      P (x \<cdot> a) b \<Longrightarrow>
      P (x \<cdot> a) (y \<cdot> b)) \<Longrightarrow>
    P a b\<close>
proof (induct a arbitrary: b)
  case TNil
  then show ?case
    by blast
next
  case (TCons x a b)
  then show ?case
    by (induct b) blast+
qed

lemma TNil_merge_traces_TNil_parts:
  \<open>TNil \<in> merge_traces a b \<Longrightarrow> a = TNil \<or> b = TNil\<close>
  by (simp add: merge_traces_def)

lemma merge_traces_rel_comm:
  \<open>merge_traces_rel a b c = merge_traces_rel b a c\<close>
  by (induct c arbitrary: a b)
    (force simp add: merge_traces_rel_cons_out_iff)+

lemma merge_traces_comm:
  \<open>merge_traces a b = merge_traces b a\<close>
  by (simp add: merge_traces_def set_eq_iff merge_traces_rel_comm)

lemma merge_traces_not_empty:
  \<open>merge_traces a b \<noteq> {}\<close>
  by (induct a b rule: merge_traces_induct)
     (force simp add: merge_traces_def merge_traces_rel_cons_LR_iff)+

definition
  \<open>merge_trace_sets A B \<equiv> \<Union>a\<in>A. \<Union>b\<in>B. merge_traces a b\<close>

lemma merge_trace_sets_assoc:
  \<open>merge_trace_sets (merge_trace_sets A B) C = merge_trace_sets A (merge_trace_sets B C)\<close>
  by (simp add: merge_trace_sets_def merge_traces_def Union_eq merge_traces_rel_assoc)

lemma merge_trace_sets_comm:
  \<open>merge_trace_sets A B = merge_trace_sets B A\<close>
  by (fastforce simp: merge_trace_sets_def Union_eq merge_traces_comm)

section \<open>Processes\<close>

subsection \<open> prefix closure \<close>

definition \<open>prefixcl A \<equiv> {t. \<exists>t'\<in>A. t \<le> t'}\<close>

lemma prefixcl_empty[simp]:
  \<open>prefixcl {} = {}\<close>
  by (simp add: prefixcl_def)

lemma prefixcl_mono:
  \<open>A \<le> B \<Longrightarrow> prefixcl A \<le> prefixcl B\<close>
  by (force simp add: prefixcl_def)

lemma prefixcl_increasing:
  fixes A :: \<open>('a :: preorder) set\<close>
  shows \<open>A \<le> prefixcl A\<close>
  by (force simp add: prefixcl_def)

lemma prefix_closed_prefixcl_eq[simp]:
  fixes A :: \<open>('a :: preorder) set\<close>
  shows \<open>prefixcl A \<subseteq> A \<Longrightarrow> prefixcl A = A\<close>
  by (force simp add: prefixcl_def subset_eq set_eq_iff)

lemma prefixcl_un[simp]:
  \<open>prefixcl (A \<union> B) = prefixcl A \<union> prefixcl B\<close>
  by (force simp add: prefixcl_def)

lemma prefixcl_Union[simp]:
  \<open>prefixcl (\<Union>\<A>) = \<Union>(prefixcl ` \<A>)\<close>
  by (force simp add: prefixcl_def)

lemma prefixcl_idem[simp]:
  fixes A :: \<open>('a :: preorder) set\<close>
  shows \<open>prefixcl (prefixcl A) = prefixcl A\<close>
  by (auto intro: order.trans simp: prefixcl_def)

abbreviation (input) \<open>prefix_closed A \<equiv> prefixcl A \<subseteq> A\<close>

lemma prefixcl_trace_plusD:
  fixes A :: \<open>'a trace set\<close>
  shows \<open>prefix_closed A \<Longrightarrow> a1 + a2 \<in> A \<Longrightarrow> a1 \<in> A\<close>
  using prefixcl_def trace_le_iff_add by fastforce

lemma prefixcl_merge_traces[simp]:
  assumes
    \<open>prefixcl A \<subseteq> A\<close>
    \<open>prefixcl B \<subseteq> B\<close>
  shows
    \<open>prefixcl (merge_trace_sets A B) \<subseteq> merge_trace_sets A B\<close>
proof -
  {
    fix ab' a b ab
    assume assms2:
      \<open>merge_traces_rel a b ab\<close>
      \<open>a \<in> A\<close>
      \<open>b \<in> B\<close>
      \<open>ab' \<le> ab\<close>
    then have \<open>\<exists>a'\<in>A. \<exists>b'\<in>B. merge_traces_rel a' b' ab'\<close>
      apply (induct ab arbitrary:  rule: trace_concat_backwards_induct)
       apply force
      apply (case_tac "aa + ba"; clarsimp simp: le_TCons_iff)
      apply (erule disjE)
       apply (metis assms(1,2) merge_traces_rel.simps plus_trace.simps(1) prefixcl_trace_plusD)
      sorry
  } note helper = this
  then show ?thesis
    using assms helper
    by (clarsimp simp add: prefixcl_def merge_trace_sets_def merge_traces_def)
qed

lemma prefix_closed_strong:
  fixes A :: \<open>('a :: preorder) set\<close>
  shows \<open>prefix_closed A \<longleftrightarrow> prefixcl A = A\<close>
  by (force simp add: prefixcl_def set_eq_iff subset_iff)

subsection \<open> Typedef \<close>

type_synonym 'a ptrace = \<open>('a pred \<times> 'a pred) trace\<close>

typedef 'a process = \<open>Collect prefix_closed :: 'a trace set set\<close>
  morphisms proctr Process
  by auto

declare Process_inverse[simplified, simp] proctr_inverse[simp]

setup_lifting type_definition_process

lemma process_eq_iff:
  \<open>a = b \<longleftrightarrow> proctr a = proctr b\<close>
  by (metis proctr_inverse)

lemma eq_Process_iff_proctr_eq:
  \<open>prefix_closed A \<Longrightarrow> a = Process A \<longleftrightarrow> proctr a = A\<close>
  by (metis Process_inverse mem_Collect_eq proctr_inverse)

lemma Process_eq_iff_eq_proctr:
  \<open>prefix_closed A \<Longrightarrow> Process A = a \<longleftrightarrow> A = proctr a\<close>
  by (metis Process_inverse mem_Collect_eq proctr_inverse)

subsection \<open> Processes are a semiring \<close>

instantiation process :: (type) comm_semiring_1
begin

lift_definition plus_process :: \<open>'a process \<Rightarrow> 'a process \<Rightarrow> 'a process\<close> is
  \<open>\<lambda>A B. A \<union> B\<close>
  by (force simp add: prefixcl_def subset_iff)

lift_definition zero_process :: \<open>'a process\<close> is \<open>{}\<close>
  by simp

lift_definition times_process :: \<open>'a process \<Rightarrow> 'a process \<Rightarrow> 'a process\<close> is
  \<open>\<lambda>A B. merge_trace_sets A B\<close>
  by (rule prefixcl_merge_traces)


lemma prefixcl_TNil_set[simp]:
  \<open>prefixcl {TNil} = {TNil}\<close>
  by (simp add: prefixcl_def)

lift_definition one_process :: \<open>'a process\<close> is
  \<open>{TNil}\<close>
  by simp

declare process_eq_iff[simp]

instance
proof

  fix a b c :: \<open>'a process\<close>
  show \<open>a + b + c = a + (b + c)\<close>
    by (simp  add:sup_assoc plus_process.rep_eq)
  show \<open>0 + a = a\<close>
    by (simp add: zero_process_def plus_process_def)
  show \<open>a + b = b + a\<close>
    by (simp add: plus_process_def sup_commute)
  show \<open>a \<parallel> b \<parallel> c = a \<parallel> (b \<parallel> c)\<close>
    by (simp add: merge_trace_sets_assoc times_process.rep_eq)
  show \<open>1 \<parallel> a = a\<close>
    by (simp add: times_process_def one_process_def merge_trace_sets_def)
  show \<open>a \<parallel> b = b \<parallel> a\<close>
    by (simp add: times_process_def merge_trace_sets_comm) 
  show \<open>0 \<parallel> a = 0\<close>
    by (simp add:  times_process_def zero_process_def merge_trace_sets_def)
  show \<open>a \<parallel> 0 = 0\<close>
    by (simp add: zero_process_def times_process.rep_eq 
                  merge_trace_sets_comm merge_trace_sets_def)
  show \<open>(a + b) \<parallel> c = a \<parallel> c + b \<parallel> c\<close>  
    by (metis (mono_tags, lifting) SUP_union proctr_inverse 
        plus_process.rep_eq times_process.rep_eq merge_trace_sets_def)
  show \<open>(0::'a process) \<noteq> 1\<close>
    by (simp add: zero_process_def one_process_def)
qed

declare process_eq_iff[simp del]

end

instantiation process :: (type) monoid_seq
begin

definition seq_process :: \<open>'a process \<Rightarrow> 'a process \<Rightarrow> 'a process\<close> where
  \<open>seq_process A B \<equiv> Process {a + b|a b. a \<in> proctr A \<and> b \<in> proctr B}\<close>

definition skip_process :: \<open>'a process\<close> where
  \<open>skip_process \<equiv> Process {TNil}\<close>

lemma process_skip_eq_one:
  \<open>(\<I>::'a process) = 1\<close>
  by (simp add: one_process_def skip_process_def)

instance
  apply standard
    apply (simp add: seq_process_def set_eq_iff)
    apply (rule arg_cong[where f=Process])
    apply (subst Process_inverse)
     apply (clarsimp simp add: prefixcl_def trace_le_plus_iff)
     apply (erule disjE)
      apply (metis trace_le_iff_add CollectD add_0 plus_trace_unit_right prefixcl_trace_plusD proctr)
     apply (metis (lifting) CollectD prefixcl_trace_plusD proctr trace_le_iff_add)
    apply (subst Process_inverse)
     apply (clarsimp simp add: prefixcl_def trace_le_plus_iff)
     apply (erule disjE)
      apply (metis trace_le_iff_add CollectD add_0 plus_trace_unit_right prefixcl_trace_plusD proctr)
     apply (metis (lifting) CollectD prefixcl_trace_plusD proctr trace_le_iff_add)
    apply (force simp add: set_eq_iff ex_simps[symmetric] add.assoc simp del: ex_simps)
   apply (simp add: seq_process_def skip_process_def)
  apply (simp add: seq_process_def skip_process_def)
  done

end


(*
  t1t1t1t1t1t1t1t1 t2t2t2t2t2t2t2t2
  s1s1s1s1s1 s2s2s2s2s2s2s2s2s2s2s2
*)

lemma trace_TCons_concatD:
  \<open>x \<cdot> t' = ta + tb \<Longrightarrow>
      (ta = TNil \<and> tb = x \<cdot> t') \<or>
     (\<exists>ta'. ta = x \<cdot> ta' \<and> t' = ta' + tb)\<close>
  by (metis plus_trace.elims trace.sel(2) trace_start.simps(2))

lemma trace_TCons_concatI:
  \<open>(ta = TNil \<and> tb = x \<cdot> t') \<or>
   (\<exists>ta'. ta = x \<cdot> ta' \<and> t' = ta' + tb) \<Longrightarrow>
  x \<cdot> t' = ta + tb\<close>
  by fastforce

lemma trace_TCons_concat_eq:
  \<open>(x \<cdot> t' = ta + tb) \<longleftrightarrow>
      (ta = TNil \<and> tb = x \<cdot> t') \<or>
     (\<exists>ta'. ta = x \<cdot> ta' \<and> t' = ta' + tb)\<close>
  using  trace_TCons_concatD 
  by fastforce

lemma trace_concat_eq:
  fixes s1 s2 t1 t2 :: \<open>'a trace\<close>
  shows \<open>s1 + s2 = t1 + t2 \<longleftrightarrow> 
          ((s1 \<le> t1 \<and> 
              (\<exists>s1'. t1 = s1 + s1' \<and> s2 = s1' + t2)) \<or> 
           (t1 \<le> s1 \<and> 
              (\<exists>t1'. s1 = t1 + t1' \<and> t2 = t1'+ s2)))\<close>
  by (induct s1 arbitrary: t1 t2)
     (fastforce simp: trace_TCons_concat_eq)+


lemma seq_eq[simp]:
  \<open>proctr (a \<triangleright> b) = {ta + tb |ta tb. ta \<in> proctr a \<and> tb \<in> proctr b}\<close>
  apply (simp add: seq_process_def)
  apply (subst Process_inverse)
   apply (clarsimp simp add: prefixcl_def trace_le_iff_add trace_concat_eq)
   apply (erule disjE)
    apply clarsimp

   apply (rename_tac t1a t1b t2a t2b)

   apply (subgoal_tac \<open>t1a \<le> t1b \<or> t1b \<le> t1a\<close>)
    apply (erule disjE)
     apply (clarsimp simp add: trace_le_iff_add)
     apply (rename_tac tc)
     apply (rule_tac x=\<open>u1\<close> in exI)
     apply (rule_tac x=\<open>u2\<close> in exI)
  
  

  sorry


text \<open>TODO: should probably be a new class\<close>
lemma seq_zero_zero[simp]:
  fixes a :: \<open>'a process\<close>
  shows
    \<open>a \<triangleright> 0 = 0\<close>
    \<open>0 \<triangleright> a = 0\<close>
  by (simp add: seq_process_def zero_process_def)+

lemma seq_plus_eq:
  fixes a :: \<open>'a process\<close>
  shows
    \<open>a \<triangleright> (b + c) = (a \<triangleright> b) + (a \<triangleright> c)\<close>
    \<open>(a + b) \<triangleright> c = (a \<triangleright> c) + (b \<triangleright> c)\<close>
  sorry
(*
  by (force simp add: seq_process_def plus_process_def)+
*)

instance process :: (type) semiring_no_zero_divisors
  sorry
(*
  by standard
    (simp add: times_process_def zero_process_def eq_Process_iff_proctr_eq merge_traces_not_empty)
*)

instance process :: (type) semiring_1_no_zero_divisors
  by standard

instantiation process :: (type) bounded_semilattice_inf_top
begin

definition top_process :: \<open>'a process\<close> where
  \<open>top_process \<equiv> Process {}\<close>

lemma process_top_eq_zero: \<open>(\<top>::'a process) = 0\<close>
  by (simp add: top_process_def zero_process_def)

definition inf_process :: \<open>'a process \<Rightarrow> 'a process \<Rightarrow> 'a process\<close> where
  \<open>inf_process a b \<equiv> Process (proctr a \<union> proctr b)\<close>

lemma process_inf_eq_plus: \<open>(a::'a process) \<sqinter> b = a + b\<close>
  by (simp add: inf_process_def plus_process_def)

definition less_eq_process :: \<open>'a process \<Rightarrow> 'a process \<Rightarrow> bool\<close> where
  \<open>less_eq_process a b \<equiv> prefixcl (proctr a) \<supseteq> prefixcl (proctr b)\<close>

definition less_process :: \<open>'a process \<Rightarrow> 'a process \<Rightarrow> bool\<close> where
  \<open>less_process a b \<equiv> prefixcl (proctr a) \<supset> prefixcl (proctr b)\<close>

instance
  apply (standard; 
          simp add: less_eq_process_def less_process_def 
                    zero_process_def process_eq_iff process_top_eq_zero)
      apply (simp_all add: process_inf_eq_plus plus_process.rep_eq)
   apply (fastforce simp: top_process_def process_eq_iff)   
  apply (metis CollectD prefix_closed_strong proctr)
  done

end

instance process :: (type) ordered_semiring_0
  apply standard
    apply (metis plus_process.rep_eq inf_process_def inf_le1
           inf_le2 le_inf_iff order_trans proctr_inverse)
   apply (metis add_0 inf_le1 mult.commute mult_zero_right order_antisym process_inf_eq_plus)
  apply (metis add_0 inf_le1 mult_zero_right order_antisym process_inf_eq_plus)
  done

section \<open> Specific Program Semantics \<close>

datatype ('p) val =
  VPtr 'p

datatype ('x,'p) action =
  AAlloc 'x \<open>'p val\<close>
  | AFree 'p
  | AReadPtr 'x 'p
  | AWritePtr 'p \<open>'p val\<close>
  | ASkip
  | AAbort
  | ALocal \<open>(unit, 'x, 'p val) pheap \<Rightarrow> (unit, 'x, 'p val) pheap\<close>

type_synonym ('x,'p) state = \<open>(unit, 'x, 'p val) pheap \<times> ('p, 'p val) dheap\<close>

inductive sstep_sem :: \<open>('x,'p) action \<Rightarrow> ('x, 'p) state \<Rightarrow> ('x, 'p) state \<Rightarrow> bool\<close>
  (\<open>_ \<sim> _ \<leadsto> _\<close> [51,0,51] 50 )
  where

  \<open>ASkip \<sim> s\<leadsto> s\<close>

| \<open>h \<bullet>d p = None \<Longrightarrow> 
  s = (l, h) \<Longrightarrow> 
    AAlloc x v \<sim> 
        s \<leadsto> 
        (l(x \<mapsto>p ((), VPtr p)), h(p \<mapsto>d (full_perm, v)))\<close>

| \<open>h \<bullet>d p = Some (full_perm, v) \<Longrightarrow> 
    s = (l, h) \<Longrightarrow> 
    AFree p \<sim>
        s \<leadsto>
        (l, h |`d (-{p}))\<close>

| \<open>h \<bullet>d p = Some (perm, v) \<Longrightarrow> 
    AReadPtr x p \<sim> 
        (l, h) \<leadsto> 
        (l(x \<mapsto>p ((), v)), h)\<close>

| \<open>\<lbrakk> h \<bullet>d p = Some (perm, v); 
     wperm perm = 1\<rbrakk> \<Longrightarrow> 
    AWritePtr p v \<sim> 
        (l, h) \<leadsto> 
        (l, h(p \<mapsto>d (perm, v)))\<close>

| \<open>ALocal f \<sim> 
        (l, h)\<leadsto> 
        (f l, h)\<close>

inductive_cases sstep_sem_AFreeE[elim]: \<open>AFree p \<sim> s \<leadsto> s'\<close>

lemma sstep_sem_AFree_iff:
  \<open>AFree p \<sim> (l,h) \<leadsto> (l',h') \<longleftrightarrow> 
    (l' = l \<and> h' = h |`d (- {p}) \<and> (\<exists>v. h \<bullet>d p = Some (full_perm, v)))\<close>
  by (rule iffI; force intro: sstep_sem.intros)

lemma sstep_sem_no_step_abort:
  \<open>\<not> AAbort \<sim> s\<leadsto> s'\<close>
proof -
  { fix a
  have  \<open>a \<sim>s\<leadsto> s' \<Longrightarrow> a = AAbort \<Longrightarrow> False\<close>
    by (induct rule: sstep_sem.induct) simp+ }
  then show ?thesis
    by force
qed

fun sstep_sem_reftrcl :: 
  \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close> (\<open>_ \<sim>_\<leadsto>\<^sup>* _\<close> [60,0,60]) 
where
  \<open>sstep_sem_reftrcl s TNil s' = (s = s')\<close>
| \<open>sstep_sem_reftrcl s (x \<cdot> a) s' = (\<exists>s1. x \<sim> s \<leadsto> s1 \<and> s1 \<sim> a \<leadsto>\<^sup>* s')\<close>

section \<open> Unit pheap \<close>

lemma unit_pheap_hperm_plus_eq:
  fixes a b :: \<open>(unit, 'x, 'v) pheap\<close>
  shows \<open>a \<bullet> x \<oplus>\<^sub>p b \<bullet> x =
          (case b \<bullet> x of
              None \<Rightarrow> a \<bullet> x
            | Some (_, vb) \<Rightarrow>
                (case a \<bullet> x of
                  None \<Rightarrow> app_pheap b x
                | Some (_, va) \<Rightarrow> Some ((), va)))\<close>
  by (simp add: plus_hperm_def split: option.splits)

section \<open> Hoare Triples \<close>

fun lift_interp_trace :: \<open>('a \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 'a trace \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool\<close> 
  (\<open>_\<^sup>* _ _ _\<close> [999,999,999,999]) where
  \<open>lift_interp_trace r TNil s s' = (s = s')\<close>
| \<open>lift_interp_trace r (x \<cdot> a) s s' = (\<exists>s1. r x s s1 \<and> r\<^sup>* a s1 s')\<close>

lemma lift_interp_trace_TNil:
  "lift_interp_trace r TNil s s" 
  by simp

definition lift_interp_process ::
  \<open>('a \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 'a process \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool\<close> where
  \<open>lift_interp_process ssem p \<equiv> \<lambda>s s'. (\<forall>t\<in>proctr p. lift_interp_trace ssem t s s')\<close>


definition generic_htriple ::
  \<open>('a \<Rightarrow> ('s::preorder) \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 's pred  \<Rightarrow> 'a process \<Rightarrow> 's pred \<Rightarrow> bool\<close>
  (\<open>_ \<turnstile> \<lbrace> _ \<rbrace> _ \<lbrace> _ \<rbrace>\<close> [60,0,60,0] 60) where
  \<open>generic_htriple ssem pre p post \<equiv>
     \<forall>s s'. lift_interp_process ssem p s s' \<longrightarrow> (\<exists>x. x \<le> s \<and> pre x) \<longrightarrow> (\<exists>x. x \<le> s' \<and> post x)\<close>


definition htriple_basic ::
  \<open>('a \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('s::preorder) pred  \<Rightarrow> 'a  \<Rightarrow> 's pred \<Rightarrow> bool\<close>
where
  \<open>htriple_basic ssem pre a post \<equiv>  
     \<forall>s s'. 
       ssem a s s' \<longrightarrow> (\<exists>x. x \<le> s \<and> pre x) \<longrightarrow> (\<exists>x. x \<le> s' \<and> post x)\<close>


fun lift_htriple_traces ::
  \<open>('a \<Rightarrow> 's pred \<Rightarrow> 's pred \<Rightarrow> bool) \<Rightarrow> 'a trace \<Rightarrow> 's pred \<Rightarrow> 's pred \<Rightarrow> bool\<close> 
  where
  \<open>lift_htriple_traces r TNil p q = (p = q)\<close>
| \<open>lift_htriple_traces r (a \<cdot> t) p q = (\<exists>p'. r a p p' \<and> lift_htriple_traces r t p' q)\<close>


definition lift_htriple ::
  \<open>('a \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('s::preorder) pred  \<Rightarrow> 'a process  \<Rightarrow> 's pred \<Rightarrow> bool\<close>
where
  \<open>lift_htriple ssem pre p post \<equiv>
    \<forall>t\<in>proctr p. lift_htriple_traces (\<lambda>x y. htriple_basic ssem y x) t pre post \<close>

lemma generic_htriple_eq_lift_htriple:
  "generic_htriple  ssem pre p post = lift_htriple ssem pre p post"
  unfolding generic_htriple_def lift_htriple_def htriple_basic_def lift_interp_process_def
  sorry


(*
lemma
  assumes
    \<open>\<lbrace> pre \<rbrace> a \<lbrace> post \<rbrace>\<^sub>B\<close>
  shows
    \<open>\<lbrace> pre \<rbrace> {a} \<lbrace> post \<rbrace>\<close>
  sorry

lemma
  assumes
    \<open>\<lbrace> pre \<rbrace> a . p \<lbrace> m \<rbrace>\<close>
    \<open>\<lbrace> m \<rbrace> a \<lbrace> post \<rbrace>\<^sub>B\<close>
  shows
    \<open>\<lbrace> pre \<rbrace> p  \<lbrace> post \<rbrace>\<close>
  sorry
*)
(* what does it mean for htriple_basic to be sound? *)

(* what does it mean for lift_htriple to be sound given htriple_basic is sound? *)

(* what does it mean for generic_htriple to be sound? *)

subsection \<open> Specific Semantics \<close>




definition htriple ::
  \<open>('x,'p) state pred  \<Rightarrow> ('x,'p) action process \<Rightarrow> ('x,'p) state pred \<Rightarrow> bool\<close>
  (\<open>\<lbrace> _ \<rbrace> _ \<lbrace> _ \<rbrace>\<close> [0,60,0] 60) where
  \<open>htriple pre p post \<equiv> sstep_sem \<turnstile> \<lbrace> pre \<rbrace> p \<lbrace> post \<rbrace>\<close>
(*
abbreviation interp
  where "interp \<equiv> lift_interp sstep_sem"
*)

(*
definition htriple_act :: 
  \<open> ('x, 'p) state pred \<Rightarrow>
    ('x, 'p) action  \<Rightarrow>
    ('x, 'p) state pred \<Rightarrow>
      bool\<close>
  (\<open>\<lbrace> _ \<rbrace> _ \<lbrace> _ \<rbrace>\<close> [0,0,0]) 
where
  \<open> htriple_act p a q \<equiv> True\<close>
*)


(*

definition htriple'
  :: \<open>('s::ord) pred \<Rightarrow>
      ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
      's pred \<Rightarrow>
      bool\<close> where
  \<open>htriple' p c q \<equiv> \<forall>s s'. c s s' \<longrightarrow> (\<exists>x. x \<le> s \<and> p x) \<longrightarrow> (\<exists>x. x \<le> s' \<and> q x)\<close>



definition htriple'
  :: \<open>('s::ord) pred \<Rightarrow>
      ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
      's pred \<Rightarrow>
      bool\<close> where
  \<open>htriple' p c q \<equiv> \<forall>s s'. c s s' \<longrightarrow> (\<exists>x. x \<le> s \<and> p x) \<longrightarrow> (\<exists>x. x \<le> s' \<and> q x)\<close>


definition interp_act ::
  \<open>('x,'p) action process \<Rightarrow> (('x, 'p) state \<Rightarrow> ('x, 'p) state \<Rightarrow> bool)\<close> where
  \<open>interp_act p \<equiv> \<lambda>s s'. (\<forall>a\<in>proctr p.  s \<sim> a \<leadsto>\<^sup>* s')\<close>

definition interp  \<open>('x,'p) action process \<Rightarrow> 
 (('x, 'p) state \<Rightarrow> ('x,'p) action \<Rightarrow> ('x, 'p) state \<Rightarrow> bool) \<Rightarrow> 
('x, 'p) state \<Rightarrow> ('x, 'p) state \<Rightarrow> bool\<close> ::
sstep_sem


definition interp_act ::
  \<open>('x,'p) action process \<Rightarrow> 
 (('x, 'p) state \<Rightarrow> ('x,'p) action \<Rightarrow> ('x, 'p) state \<Rightarrow> bool) \<Rightarrow> 
('x, 'p) state \<Rightarrow> ('x, 'p) state \<Rightarrow> bool\<close> where
  \<open>interp_act p r \<equiv> \<lambda>s s'. (\<forall>a\<in>proctr p.  r\<^sup>* a s s')\<close>


(*
definition interp ::
  \<open>'a process \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool\<close> where
  \<open>interp_act p \<equiv> \<lambda>s s'. (\<forall>a\<in>proctr p.  s \<sim> a \<leadsto>\<^sup>* s')\<close>
*)
definition htriple'
  :: \<open>('s::ord) pred \<Rightarrow>
      ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
      's pred \<Rightarrow>
      bool\<close> where
  \<open>htriple' p c q \<equiv> \<forall>s s'. c s s' \<longrightarrow> (\<exists>x. x \<le> s \<and> p x) \<longrightarrow> (\<exists>x. x \<le> s' \<and> q x)\<close>


definition \<open>dealloc_cap p \<equiv> \<lambda>(l,h). \<exists>perm v. h \<bullet>d p = Some (perm, v) \<and> is_full_perm perm\<close>
definition \<open>write_cap p \<equiv> \<lambda>(l,h). \<exists>perm v. h \<bullet>d p = Some (perm, v) \<and> is_write_perm perm\<close>

(*
lemma hoare_triple_ptr_write:
  fixes P :: \<open>((unit, 'x, 'p val) pheap \<times> ('p, 'p val) dheap) pred\<close>
  shows \<open>\<lbrace> dealloc_cap p \<rbrace> (\<lambda>s s'. s \<sim>AFree p\<leadsto> s') \<lbrace> emp \<rbrace>\<close>
  apply (clarsimp simp add: htriple_def sstep_sem_AFree_iff sepconj_def dheap_eq_iff emp_def
      dealloc_cap_def is_full_perm_def)
  apply (metis Rep_dheap_zero app_zero_pheap sep_alg_class.zero_le)
  done
*)

definition interp_act ::
  \<open>('x,'p) action process \<Rightarrow> (('x, 'p) state \<Rightarrow> ('x, 'p) state \<Rightarrow> bool)\<close> where
  \<open>interp_act p \<equiv> \<lambda>s s'. (\<forall>a\<in>proctr p.  s \<sim> a \<leadsto>\<^sup>* s')\<close>
(*
definition interp :: \<open>'a pred process \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool)\<close> where
  \<open>interp p \<equiv> \<lambda>s s'.
      (TNil \<in> proctr p \<longrightarrow> s = s') \<and>
      (\<forall>t\<in>proctr p. t \<noteq> TNil \<longrightarrow> trace_start t s \<longrightarrow> trace_end t s')\<close>
*)


definition htriple:: 
  \<open> ('x, 'p) state pred \<Rightarrow>
    ('x, 'p) action process \<Rightarrow>
    ('x, 'p) state pred \<Rightarrow>
      bool\<close>
  (\<open>\<lbrace> _ \<rbrace> _ \<lbrace> _ \<rbrace>\<close> [0,0,0]) 
where
  \<open> htriple p c q \<equiv> htriple' p (interp_act c) q\<close>

*)

end