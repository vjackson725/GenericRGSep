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

subsection \<open> Trace Concat \<close>

fun trace_concat :: \<open>'a trace \<Rightarrow> 'a trace \<Rightarrow> 'a trace\<close> (infixr \<open>@t\<close> 65) where
  \<open>trace_concat TNil b = b\<close>
| \<open>trace_concat (x \<cdot> a) b = x \<cdot> trace_concat a b\<close>

lemma trace_concat_unit_right[simp]:
  \<open>a @t TNil = a\<close>
  by (induct a) simp+

lemma trace_concat_assoc:
  \<open>a @t b @t c = (a @t b) @t c\<close>
  by (induct a arbitrary: b c) simp+

lemma trace_start_concat[simp]:
  \<open>trace_start (a @t b) = (if a = TNil then trace_start b else trace_start a)\<close>
  by (induct a arbitrary: b)
    (force elim: trace_concat.elims)+

lemma trace_end_concat[simp]:
  \<open>trace_end (a @t b) = (if b = TNil then trace_end a else trace_end b)\<close>
  apply (induct a arbitrary: b)
   apply clarsimp
  apply (case_tac \<open>a @t b\<close>)
   apply (force elim: trace_concat.elims)
  apply (simp, metis trace_concat_unit_right trace_end.simps(3))
  done

lemma trace_concat_eq_nil_iff[simp]:
  \<open>(a @t b) = TNil \<longleftrightarrow> a = TNil \<and> b = TNil\<close>
  \<open>TNil = (a @t b) \<longleftrightarrow> a = TNil \<and> b = TNil\<close>
  by (metis trace.discI trace_concat.elims)+

subsection \<open> Parallel Trace Merge\<close>

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
    \<open>\<exists>a b c bc. a \<in> A \<and> b \<in> B \<and> c \<in> C \<and> merge_traces_rel b c bc \<and> merge_traces_rel a bc abc\<close>
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
    \<open>\<exists>a b c ab. a \<in> A \<and> b \<in> B \<and> c \<in> C \<and> merge_traces_rel a b ab \<and> merge_traces_rel ab c abc\<close>
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
  \<open>{abc. \<exists>a. a \<in> A \<and> (\<exists>b. b \<in> B \<and> (\<exists>c. c \<in> C \<and> (\<exists>ab.
      merge_traces_rel a b ab \<and> merge_traces_rel ab c abc)))}
    = {abc. \<exists>a. a \<in> A \<and> (\<exists>b. b \<in> B \<and> (\<exists>c. c \<in> C \<and> (\<exists>bc.
        merge_traces_rel b c bc \<and> merge_traces_rel a bc abc)))}\<close>
  using merge_traces_assoc1 merge_traces_assoc2
  by fast

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

lemma merge_traces_assoc:
  \<open>{abc|a b c ab abc::'a trace.
      a \<in> A \<and> b \<in> B \<and> c \<in> C \<and> ab \<in> merge_traces a b \<and> abc \<in> merge_traces ab c}
    = {abc|a b c bc abc.
        a \<in> A \<and> b \<in> B \<and> c \<in> C \<and> bc \<in> merge_traces b c \<and> abc \<in> merge_traces a bc}\<close>
  by (simp add: merge_traces_def merge_traces_rel_assoc)

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

section \<open>Processes\<close>

type_synonym 'a ptrace = \<open>('a pred \<times> 'a pred) trace\<close>

datatype 'a process = Process (proctr: \<open>'a trace set\<close>)

lemma process_eq_iff:
  \<open>a = b \<longleftrightarrow> proctr a = proctr b\<close>
  using process.expand by auto

lemma eq_Process_iff_proctr_eq:
  \<open>a = Process A \<longleftrightarrow> proctr a = A\<close>
  by auto

lemma Process_eq_iff_eq_proctr:
  \<open>Process A = a \<longleftrightarrow> A = proctr a\<close>
  by auto

subsection \<open> Processes are a semiring \<close>

instantiation process :: (type) comm_semiring_1
begin

definition plus_process :: \<open>'a process \<Rightarrow> 'a process \<Rightarrow> 'a process\<close> where
  \<open>plus_process A B \<equiv> Process (proctr A \<union> proctr B)\<close>

definition zero_process :: \<open>'a process\<close> where
  \<open>zero_process \<equiv> Process {}\<close>

definition times_process :: \<open>'a process \<Rightarrow> 'a process \<Rightarrow> 'a process\<close> where
  \<open>times_process A B \<equiv> Process (\<Union>(a,b) \<in> (proctr A \<times> proctr B). merge_traces a b)\<close>

definition one_process :: \<open>'a process\<close> where
  \<open>one_process \<equiv> Process {TNil}\<close>

instance
proof
  fix a b c :: \<open>'a process\<close>
  show \<open>a + b + c = a + (b + c)\<close>
    by (force simp add: plus_process_def)
  show \<open>0 + a = a\<close>
    by (simp add: plus_process_def zero_process_def)
  show \<open>a + b = b + a\<close>
    by (simp add: plus_process_def sup_commute)
  show \<open>a \<parallel> b \<parallel> c = a \<parallel> (b \<parallel> c)\<close>
    apply (simp add: times_process_def Setcompr_eq_image Union_eq)
    apply (rule HOL.trans[OF _ merge_traces_assoc, THEN HOL.trans])
     apply blast
    apply blast
    done
  show \<open>1 \<parallel> a = a\<close>
    by (simp add: times_process_def one_process_def Setcompr_eq_image)
  show \<open>a \<parallel> b = b \<parallel> a\<close>
    using merge_traces_comm
    by (fastforce simp add: times_process_def set_eq_iff)
  show \<open>0 \<parallel> a = 0\<close>
    by (simp add: zero_process_def times_process_def)
  show \<open>a \<parallel> 0 = 0\<close>
    by (simp add: zero_process_def times_process_def)
  show \<open>(a + b) \<parallel> c = a \<parallel> c + b \<parallel> c\<close>
    by (simp add: plus_process_def times_process_def Sigma_Un_distrib1)
  show \<open>(0::'a process) \<noteq> 1\<close>
    by (simp add: zero_process_def one_process_def)
qed

end

instantiation process :: (type) monoid_seq
begin

definition seq_process :: \<open>'a process \<Rightarrow> 'a process \<Rightarrow> 'a process\<close> where
  \<open>seq_process A B \<equiv> Process {a @t b|a b. a \<in> proctr A \<and> b \<in> proctr B}\<close>

definition skip_process :: \<open>'a process\<close> where
  \<open>skip_process \<equiv> Process {TNil}\<close>

lemma process_skip_eq_one:
  \<open>(\<I>::'a process) = 1\<close>
  by (simp add: one_process_def skip_process_def)

instance
  apply standard
    apply (simp add: seq_process_def set_eq_iff, metis trace_concat_assoc)
   apply (simp add: seq_process_def skip_process_def)
  apply (simp add: seq_process_def skip_process_def)
  done

end

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
  by (force simp add: seq_process_def plus_process_def)+

instance process :: (type) semiring_no_zero_divisors
  by standard
    (simp add: times_process_def zero_process_def eq_Process_iff_proctr_eq merge_traces_not_empty)

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
  \<open>less_eq_process a b \<equiv> proctr a \<supseteq> proctr b\<close>

definition less_process :: \<open>'a process \<Rightarrow> 'a process \<Rightarrow> bool\<close> where
  \<open>less_process a b \<equiv> proctr a \<supset> proctr b\<close>

instance
  by standard
    (force simp add: less_process_def less_eq_process_def inf_process_def top_process_def
      process_eq_iff)+

end

instance process :: (type) ordered_semiring_0
  apply standard
    apply (force simp add: less_eq_process_def plus_process_def)
   apply (simp add: less_eq_process_def zero_process_def times_process_def)
  apply (simp add: less_eq_process_def zero_process_def times_process_def)
  done

section \<open> Hoare Triples \<close>

definition htriple' :: \<open>'a pred \<Rightarrow> ('a pred \<times> 'a pred) process \<Rightarrow> 'a pred \<Rightarrow> bool\<close>
  (\<open>\<lbrace> _ \<rbrace> _ \<lbrace> _ \<rbrace>\<close> [0,0,0]) where
  \<open>htriple' p a q \<equiv>
    \<forall>t\<in>proctr a. if t = TNil then p \<le> q else snd (trace_end t) \<le> q\<close>

lemma hoare_triple_ndet:
  \<open>\<lbrace> p1 \<rbrace> a \<lbrace> q1 \<rbrace> \<Longrightarrow> \<lbrace> p2 \<rbrace> b \<lbrace> q2 \<rbrace> \<Longrightarrow> \<lbrace> p1 \<sqinter> p2 \<rbrace> a + b \<lbrace> q1 \<squnion> q2 \<rbrace>\<close>
  by (force simp add: htriple'_def plus_process_def)

lemma hoare_triple_seq:
  \<open>\<lbrace> p \<rbrace> a \<lbrace> q \<rbrace> \<Longrightarrow> \<lbrace> q \<rbrace> b \<lbrace> r \<rbrace> \<Longrightarrow> \<lbrace> p \<rbrace> a \<triangleright> b \<lbrace> r \<rbrace>\<close>
  by (force simp add: htriple'_def seq_process_def Ball_def all_conj_distrib
      split: if_splits)

end