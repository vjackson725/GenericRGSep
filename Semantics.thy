theory Semantics
  imports DeallocHeap
begin

notation(input)
  times (infixl \<open>\<parallel>\<close> 65)

text \<open> A process can be represented as a trace of predicate pairs. \<close>

text \<open> Note: only finite traces at the moment. \<close>
type_synonym 'a pred = \<open>'a \<Rightarrow> bool\<close>

datatype (\<alpha>set: 'a) trace =
  TNil
| TCons (trhd: 'a) (trtl: "'a trace") (infixr "\<cdot>" 70)

lemma not_TNil_eq: \<open>a \<noteq> TNil \<longleftrightarrow> (\<exists>ax a'. a = ax \<cdot> a')\<close>
  using trace.exhaust_sel by blast

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

lemma merge_traces_rel_cons_iff:
  \<open>merge_traces_rel (x \<cdot> a') b c \<longleftrightarrow>
    (\<exists>c'. merge_traces_rel a' b c' \<and> c = x \<cdot> c') \<or>
      (\<exists>y b' c'. merge_traces_rel (x \<cdot> a') b' c' \<and> b = y \<cdot> b' \<and> c = y \<cdot> c')\<close>
  \<open>merge_traces_rel a (y \<cdot> b') c \<longleftrightarrow>
    (\<exists>c'. merge_traces_rel a b' c' \<and> c = y \<cdot> c') \<or>
      (\<exists>x a' c'. merge_traces_rel a' (y \<cdot> b') c' \<and> a = x \<cdot> a' \<and> c = x \<cdot> c')\<close>
   apply (metis mergetr_cons_left mergetr_cons_right mergetr_left_consE)
  apply (metis mergetr_cons_left mergetr_cons_right mergetr_right_consE)
  done

lemma merge_traces_rel_cons_simps[simp]:
  \<open>merge_traces_rel a b (z \<cdot> c') \<longleftrightarrow>
    (\<exists>a'. merge_traces_rel a' b c' \<and> a = z \<cdot> a') \<or>
    (\<exists>b'. merge_traces_rel a b' c' \<and> b = z \<cdot> b')\<close>
  by (meson mergetr_cons_left mergetr_cons_right mergetr_out_consE)

lemma merge_traces_assoc1:
  assumes
    \<open>merge_traces_rel a b ab\<close>
    \<open>merge_traces_rel ab c abc\<close>
    \<open>a \<in> A\<close> \<open>b \<in> B\<close> \<open>c \<in> C\<close>
  shows
    \<open>\<exists>a b c bc. a \<in> A \<and> b \<in> B \<and> c \<in> C \<and> merge_traces_rel b c bc \<and> merge_traces_rel a bc abc\<close>
  using assms
proof (induct abc arbitrary: a b ab c A B C)
  case TNil
  then show ?case
    by simp
next
  case (TCons x abc)
  then show ?case
    apply clarsimp
    apply (erule disjE)
     apply clarsimp
     apply (erule disjE)
      apply clarsimp
      apply (rename_tac ab' a')
      apply (drule meta_spec, drule meta_spec, drule meta_spec, drule meta_spec)
      apply (drule_tac x=\<open>{a. x \<cdot> a \<in> A}\<close> in meta_spec)
      apply (drule_tac x=B in meta_spec)
      apply (drule_tac x=C in meta_spec)
      apply blast
     apply clarsimp
     apply (rename_tac ab' b')
     apply (drule meta_spec, drule meta_spec, drule meta_spec, drule meta_spec)
     apply (drule_tac x=A in meta_spec)
     apply (drule_tac x=\<open>{a. x \<cdot> a \<in> B}\<close> in meta_spec)
     apply (drule_tac x=C in meta_spec)
     apply force
    apply clarsimp
    apply (rename_tac c')
    apply (drule meta_spec, drule meta_spec, drule meta_spec, drule meta_spec)
    apply (drule_tac x=A in meta_spec)
    apply (drule_tac x=B in meta_spec)
    apply (drule_tac x=\<open>{c. x \<cdot> c \<in> C}\<close> in meta_spec)
    apply force
    done
qed


lemma merge_traces_assoc2:
  assumes
    \<open>merge_traces_rel b c bc\<close>
    \<open>merge_traces_rel a bc abc\<close>
    \<open>a \<in> A\<close> \<open>b \<in> B\<close> \<open>c \<in> C\<close>
  shows
    \<open>\<exists>a b c bc. a \<in> A \<and> b \<in> B \<and> c \<in> C \<and> merge_traces_rel b c bc \<and> merge_traces_rel a bc abc\<close>
  using assms
proof (induct abc arbitrary: a b c bc A B C)
  case TNil
  then show ?case
    by simp
next
  case (TCons x abc)
  then show ?case
    apply clarsimp
    apply (erule disjE)
     apply clarsimp
     apply (erule disjE)
      apply clarsimp
      apply (rename_tac ab' a')
      apply (drule meta_spec, drule meta_spec, drule meta_spec, drule meta_spec)
      apply (drule_tac x=\<open>{a. x \<cdot> a \<in> A}\<close> in meta_spec)
      apply (drule_tac x=B in meta_spec)
      apply (drule_tac x=C in meta_spec)
      apply blast
     apply clarsimp
     apply (rename_tac ab' b')
     apply (drule meta_spec, drule meta_spec, drule meta_spec, drule meta_spec)
     apply (drule_tac x=A in meta_spec)
     apply (drule_tac x=\<open>{a. x \<cdot> a \<in> B}\<close> in meta_spec)
     apply (drule_tac x=C in meta_spec)
     apply force
    apply clarsimp
    apply (rename_tac c')
    apply (drule meta_spec, drule meta_spec, drule meta_spec, drule meta_spec)
    apply (drule_tac x=A in meta_spec)
    apply (drule_tac x=B in meta_spec)
    apply (drule_tac x=\<open>{c. x \<cdot> c \<in> C}\<close> in meta_spec)
    apply force
    done
qed

lemma merge_traces_assoc:
  \<open>{abc|a b c ab abc::'a trace. a \<in> A \<and> b \<in> B \<and> c \<in> C \<and> merge_traces_rel a b ab \<and> merge_traces_rel ab c abc} =
    {abc|a b c bc abc. a \<in> A \<and> b \<in> B \<and> c \<in> C \<and> merge_traces_rel b c bc \<and> merge_traces_rel a bc abc}\<close>
  sorry

(*
fun merge_traces :: \<open>'a trace \<Rightarrow> 'a trace \<Rightarrow> 'a trace set\<close> where
  \<open>merge_traces TNil b = {b}\<close>
| \<open>merge_traces a TNil = {a}\<close>
| \<open>merge_traces (x \<cdot> a) (y \<cdot> b) = (\<Union>t\<in>merge_traces a b. {x \<cdot> y \<cdot> t, y \<cdot> x \<cdot> t})\<close>

lemmas merge_traces_induct = merge_traces.induct[case_names LeftTNil RightTNil TCons]

lemma merge_traces_extra_simps[simp]:
  \<open>merge_traces a TNil = {a}\<close>
  by (metis merge_traces.simps(1,2) not_TNil_eq)

lemma TNil_merge_traces_TNil_parts:
  \<open>TNil \<in> merge_traces a b \<Longrightarrow> a = TNil \<or> b = TNil\<close>
  by (induct a b rule: merge_traces.induct) force+

lemma merge_traces_assoc:
  \<open>{abc|a b c ab abc::'a trace. a \<in> A \<and> b \<in> B \<and> c \<in> C \<and> ab \<in> merge_traces a b \<and> abc \<in> merge_traces ab c} =
    {abc|a b c bc abc. a \<in> A \<and> b \<in> B \<and> c \<in> C \<and> bc \<in> merge_traces b c \<and> abc \<in> merge_traces a bc}\<close>
  sorry
*)

section \<open>Processes\<close>

type_synonym 'a ptrace = \<open>('a pred \<times> 'a pred) trace\<close>

datatype 'a process = Process (proctr: \<open>'a ptrace set\<close>)

instantiation process :: (type) monoid_mult
begin

definition times_process :: \<open>'a process \<Rightarrow> 'a process \<Rightarrow> 'a process\<close> where
  \<open>times_process A B \<equiv> Process (\<Union>{merge_traces a b|a b. a \<in> proctr A \<and> b \<in> proctr B })\<close>

definition one_process :: \<open>'a process\<close> where
  \<open>one_process \<equiv> Process {TNil}\<close>

instance
proof
  fix a b c :: \<open>'a process\<close>
  show \<open>a \<parallel> b \<parallel> c = a \<parallel> (b \<parallel> c)\<close>
    apply (simp add: times_process_def one_process_def Setcompr_eq_image Union_eq)
    apply (rule HOL.trans[OF _ merge_traces_assoc[where A=\<open>proctr a\<close> and B=\<open>proctr b\<close> and C=\<open>proctr c\<close>], THEN HOL.trans])
     apply blast
    apply blast
    done
  show \<open>1 \<parallel> a = a\<close>
    by (simp add: times_process_def one_process_def Setcompr_eq_image)
  show \<open>a \<parallel> 1 = a\<close>
    by (simp add: times_process_def one_process_def Setcompr_eq_image)
qed

end


end