theory StableLang
  imports Stabilisation "HOL-Library.BNF_Corec"
begin

notation(input)
  plus (infixl \<open>\<parallel>\<close> 65)

text \<open>
  A process can be represented as a trace of predicate pairs.
\<close>

type_synonym 'a pred = \<open>'a \<Rightarrow> bool\<close>

codatatype (\<alpha>set: 'a) trace =
  TNil
| TCons (trhd: 'a) (trtl: "'a trace") (infixr "\<cdot>" 70)

primcorec trace_map :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> 'a trace \<Rightarrow> 'b trace\<close> where
  \<open>trace_map f a = (if a = TNil then TNil else f (trhd a) \<cdot> trace_map f (trtl a))\<close>

lemma trace_map_simps[simp]:
  \<open>trace_map f TNil = TNil\<close>
  \<open>trace_map f (x \<cdot> xs) = f x \<cdot> trace_map f xs\<close>
  by (simp add: trace_map.ctr)+
  

lemma not_TNil_eq: \<open>a \<noteq> TNil \<longleftrightarrow> (\<exists>ax a'. a = ax \<cdot> a')\<close>
  using trace.exhaust_sel by blast


type_synonym 'a ptrace = \<open>('a pred \<times> 'a pred) trace\<close>

codatatype merge_tr =
  MKEndL |
  MKEndR |
  MKLeft merge_tr |
  MKRight merge_tr |
  MKSyncLR merge_tr |
  MKSyncRL merge_tr

print_theorems

corec flip_merge_tr :: \<open>merge_tr \<Rightarrow> merge_tr\<close> where
  \<open>flip_merge_tr a =
    (case a of
      MKEndL \<Rightarrow> MKEndR
    | MKEndR \<Rightarrow> MKEndL
    | MKLeft a' \<Rightarrow> MKRight (flip_merge_tr a')
    | MKRight a' \<Rightarrow> MKLeft (flip_merge_tr a')
    | MKSyncLR a' \<Rightarrow> MKSyncRL (flip_merge_tr a')
    | MKSyncRL a' \<Rightarrow> MKSyncLR (flip_merge_tr a'))\<close>

print_theorems

lemma flip_merge_tr_simps[simp]:
  \<open>flip_merge_tr MKEndR = MKEndL\<close>
  \<open>flip_merge_tr MKEndL = MKEndR\<close>
  \<open>flip_merge_tr (MKRight a) = MKLeft (flip_merge_tr a)\<close>
  \<open>flip_merge_tr (MKLeft a) = MKRight (flip_merge_tr a)\<close>
  \<open>flip_merge_tr (MKSyncLR a) = MKSyncRL (flip_merge_tr a)\<close>
  \<open>flip_merge_tr (MKSyncRL a) = MKSyncLR (flip_merge_tr a)\<close>
  by (simp add: flip_merge_tr.code)+

lemma flip_merge_tr_eq_simps[iff]:
  \<open>flip_merge_tr k = MKEndL \<longleftrightarrow> k = MKEndR\<close>
  \<open>flip_merge_tr k = MKEndR \<longleftrightarrow> k = MKEndL\<close>
  \<open>flip_merge_tr k = MKRight a \<longleftrightarrow> (\<exists>k'. k = MKLeft k' \<and> flip_merge_tr k' = a)\<close>
  \<open>flip_merge_tr k = MKLeft a \<longleftrightarrow> (\<exists>k'. k = MKRight k' \<and> flip_merge_tr k' = a)\<close>
  \<open>flip_merge_tr k = MKSyncLR a \<longleftrightarrow> (\<exists>k'. k = MKSyncRL k' \<and> flip_merge_tr k' = a)\<close>
  \<open>flip_merge_tr k = MKSyncRL a \<longleftrightarrow> (\<exists>k'. k = MKSyncLR k' \<and> flip_merge_tr k' = a)\<close>
  by (cases k; simp; fail)+

lemma flip_merge_is_merge_tr_iff[iff]:
  \<open>is_MKRight (flip_merge_tr k) \<longleftrightarrow> is_MKLeft k\<close>
  \<open>is_MKLeft (flip_merge_tr k) \<longleftrightarrow> is_MKRight k\<close>
  \<open>is_MKSyncLR (flip_merge_tr k) \<longleftrightarrow> is_MKSyncRL k\<close>
  \<open>is_MKSyncRL (flip_merge_tr k) \<longleftrightarrow> is_MKSyncLR k\<close>
  by (cases k; simp; fail)+

lemma flip_merge_un_merge_tr_eq[simp]:
  \<open>is_MKLeft k \<Longrightarrow> un_MKRight (flip_merge_tr k) = flip_merge_tr (un_MKLeft k)\<close>
  \<open>is_MKRight k \<Longrightarrow> un_MKLeft (flip_merge_tr k) = flip_merge_tr (un_MKRight k)\<close>
  \<open>is_MKSyncLR k \<Longrightarrow> un_MKSyncRL (flip_merge_tr k) = flip_merge_tr (un_MKSyncLR k)\<close>
  \<open>is_MKSyncRL k \<Longrightarrow> un_MKSyncLR (flip_merge_tr k) = flip_merge_tr (un_MKSyncRL k)\<close>
  by (cases k; simp; fail)+

lemma flip_merge_key_idem[simp]:
  \<open>flip_merge_tr (flip_merge_tr k) = k\<close>
  by (rule merge_tr.coinduct[where
        R=\<open>\<lambda>x y. \<exists>x'. x = flip_merge_tr (flip_merge_tr x') \<and> x' = y\<close>
        ]) force+


coinductive ptrace_merge_with :: \<open>'a ptrace \<Rightarrow> 'a ptrace \<Rightarrow> 'a ptrace \<Rightarrow> merge_tr \<Rightarrow> bool\<close>
  where
  \<open>ptrace_merge_with TNil b b MKEndL\<close>
| \<open>ptrace_merge_with a TNil a MKEndR\<close>
| \<open>ptrace_merge_with a' b c k' \<Longrightarrow>
    ptrace_merge_with (ax \<cdot> a') b (ax \<cdot> c) (MKLeft k')\<close>
| \<open>ptrace_merge_with a b' c k' \<Longrightarrow>
    ptrace_merge_with a (bx \<cdot> b') (bx \<cdot> c) (MKRight k')\<close>
| \<open>ptrace_merge_with a' b' c' k' \<Longrightarrow>
    snd ax = fst bx \<Longrightarrow>
    cx = (fst ax, snd bx) \<Longrightarrow>
    ptrace_merge_with (ax \<cdot> a') (bx \<cdot> b') (cx \<cdot> c') (MKSyncLR k')\<close>
| \<open>ptrace_merge_with a' b' c' k' \<Longrightarrow>
    fst ax = snd bx \<Longrightarrow>
    cx = (fst bx, snd ax) \<Longrightarrow>
    ptrace_merge_with (ax \<cdot> a') (bx \<cdot> b') (cx \<cdot> c') (MKSyncRL k')\<close>

abbreviation ptrace_merge :: \<open>'a ptrace \<Rightarrow> 'a ptrace \<Rightarrow> 'a ptrace \<Rightarrow> bool\<close> where
  \<open>ptrace_merge a b c \<equiv> Ex (ptrace_merge_with a b c)\<close>

lemma ptrace_merge_NilL[simp]:
  \<open>ptrace_merge TNil b c \<longleftrightarrow> c = b\<close>
proof (rule iffI)
  show \<open>ptrace_merge TNil b c \<Longrightarrow> c = b\<close>
    apply (coinduct rule: trace.coinduct, assumption)
    apply (subst (asm) ptrace_merge_with.simps)
    apply (force intro: ptrace_merge_with.intros)
    done
next
  show \<open>c = b \<Longrightarrow> ptrace_merge TNil b c\<close>
    using ptrace_merge_with.intros by blast
qed

lemma ptrace_merge_NilR[simp]:
  \<open>ptrace_merge a TNil c \<longleftrightarrow> c = a\<close>
proof (rule iffI)
  show \<open>ptrace_merge a TNil c \<Longrightarrow> c = a\<close>
    apply (coinduct rule: trace.coinduct, assumption)
    apply (subst (asm) ptrace_merge_with.simps)
    apply (force intro: ptrace_merge_with.intros)
    done
next
  show \<open>c = a \<Longrightarrow> ptrace_merge a TNil c\<close>
    using ptrace_merge_with.intros by blast
qed


  

lemma trace_map_trace_map[simp]: \<open>trace_map f (trace_map g a) = trace_map (f \<circ> g) a\<close>
  apply (rule trace.coinduct[where
        R=\<open>\<lambda>x y. (\<exists>x' y'. x = trace_map f (trace_map g x') \<and> y = trace_map (f \<circ> g) y' \<and> x' = y')\<close>
        ])
   apply force+
  done


lemma ptrace_merge_with_comm':
  \<open>ptrace_merge_with a b c (flip_merge_tr k) \<Longrightarrow> ptrace_merge_with b a c k\<close>
  apply (rule ptrace_merge_with.coinduct[where
        X=\<open>\<lambda>b a c k. ptrace_merge_with a b c (flip_merge_tr k)\<close>
        ])
   apply blast
  apply (thin_tac \<open>ptrace_merge_with a _ _ _\<close>)
  apply (rename_tac b a c k)
  apply (subst (asm) ptrace_merge_with.simps)
  apply (case_tac k; force)
  done

lemma ptrace_merge_with_comm:
  \<open>ptrace_merge_with a b c k \<Longrightarrow> ptrace_merge_with b a c (flip_merge_tr k)\<close>
  using ptrace_merge_with_comm' by force

lemma ptrace_merge_comm:
  \<open>ptrace_merge a b c \<Longrightarrow> ptrace_merge b a c\<close>
  by (meson ptrace_merge_with_comm)

lemma pmergep_assoc1:
  assumes
    \<open>ptrace_merge_with a b m k1\<close>
    \<open>ptrace_merge_with m c d k2\<close>
  shows
    \<open>\<exists>m2 k1' k2'. ptrace_merge_with c b m2 k1' \<and> ptrace_merge_with m2 a d k2'\<close>
  using assms
  sorry


section \<open>Processes\<close>

datatype 'a process = Process (proctr: \<open>'a ptrace set\<close>)

instantiation process :: (type) monoid_add
begin

definition plus_process :: \<open>'a process \<Rightarrow> 'a process \<Rightarrow> 'a process\<close> where
  \<open>plus_process A B \<equiv> Process {c|c a b. a \<in> proctr A \<and> b \<in> proctr B \<and> pmergep a b c }\<close>

definition zero_process :: \<open>'a process\<close> where
  \<open>zero_process \<equiv> Process {Nil}\<close>

instance
proof
  fix a b c :: \<open>'a process\<close>
  show \<open>a + b + c = a + (b + c)\<close>
    sorry
  show \<open>0 + a = a\<close>
    by (simp add: plus_process_def zero_process_def)
  show \<open>a + 0 = a\<close>
    by (simp add: plus_process_def zero_process_def)
qed

end





end