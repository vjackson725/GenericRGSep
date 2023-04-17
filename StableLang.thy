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

print_theorems

abbreviation ptrace_merge :: \<open>'a ptrace \<Rightarrow> 'a ptrace \<Rightarrow> 'a ptrace \<Rightarrow> bool\<close> where
  \<open>ptrace_merge a b c \<equiv> Ex (ptrace_merge_with a b c)\<close>


lemma ptrace_merge_with_merge_tr_iff[iff]:
  \<open>ptrace_merge_with a b c MKEndL \<longleftrightarrow> a = TNil \<and> c = b\<close>
  \<open>ptrace_merge_with a b c MKEndR \<longleftrightarrow> b = TNil \<and> c = a\<close>
  \<open>ptrace_merge_with a b c (MKLeft k') \<longleftrightarrow>
    (\<exists>x a' c'. a = (x \<cdot> a') \<and> c = (x \<cdot> c') \<and> ptrace_merge_with a' b c' k')\<close>
  \<open>ptrace_merge_with a b c (MKRight k') \<longleftrightarrow>
    (\<exists>x b' c'. b = (x \<cdot> b') \<and> c = (x \<cdot> c') \<and> ptrace_merge_with a b' c' k')\<close>
  \<open>ptrace_merge_with a b c (MKSyncLR k') \<longleftrightarrow>
    (\<exists>p q r a' b' c'. a = ((p,q) \<cdot> a') \<and> b = (q,r) \<cdot> b' \<and> c = ((p,r) \<cdot> c') \<and> ptrace_merge_with a' b' c' k')\<close>
  \<open>ptrace_merge_with a b c (MKSyncRL k') \<longleftrightarrow>
    (\<exists>p q r a' b' c'. a = ((q,r) \<cdot> a') \<and> b = (p,q) \<cdot> b' \<and> c = ((p,r) \<cdot> c') \<and> ptrace_merge_with a' b' c' k')\<close>
  by (subst ptrace_merge_with.simps, force)+


lemma ptrace_merge_with_TNil_same:
  \<open>ptrace_merge_with TNil b c k \<Longrightarrow> b = c\<close>
  \<open>ptrace_merge_with a TNil c k \<Longrightarrow> a = c\<close>
  \<open>ptrace_merge_with a b TNil k \<Longrightarrow> a = TNil \<and> b = TNil\<close>
  apply (rule trace.coinduct[of \<open>\<lambda>x y. \<exists>k. ptrace_merge_with TNil x y k\<close>], force,
      clarsimp, case_tac ka; force)
  apply (rule trace.coinduct[of \<open>\<lambda>x y. \<exists>k. ptrace_merge_with x TNil y k\<close>], force,
      clarsimp, case_tac ka; force)
  apply (force elim: ptrace_merge_with.cases)
  done


lemma ptrace_merge_with_left_step:
  \<open>ptrace_merge_with TNil b c k \<longleftrightarrow>
    k = MKEndL \<and> c = b \<or>
    k = MKEndR \<and> b = TNil \<and> c = TNil \<or>
    (\<exists>x b' c' k'. b = x \<cdot> b' \<and> c = x \<cdot> c' \<and> k = MKRight k' \<and> ptrace_merge_with TNil b' c' k')\<close>
  \<open>ptrace_merge_with (ax \<cdot> a') b c k \<longleftrightarrow>
    (k = MKEndR \<and> b = TNil \<and> c = ax \<cdot> a' \<or>
     (\<exists>k' c'. k = MKLeft k' \<and> c = ax \<cdot> c' \<and> ptrace_merge_with a' b c' k') \<or>
     (\<exists>b' c' k' x.
        k = MKRight k' \<and> b = x \<cdot> b' \<and> c = x \<cdot> c' \<and> ptrace_merge_with (ax \<cdot> a') b' c' k') \<or>
     (\<exists>b' c' k' q.
        k = MKSyncLR k' \<and> b = (snd ax, q) \<cdot> b' \<and> c = (fst ax, q) \<cdot> c' \<and>
        ptrace_merge_with a' b' c' k') \<or>
     (\<exists>b' c' k' q.
        k = MKSyncRL k' \<and> b = (q, fst ax) \<cdot> b' \<and> c = (q, snd ax) \<cdot> c' \<and>
        ptrace_merge_with a' b' c' k'))\<close>
  by (subst ptrace_merge_with.simps; cases k; force)+

lemma ptrace_merge_with_right_step:
  \<open>ptrace_merge_with a TNil c k \<longleftrightarrow>
    k = MKEndR \<and> c = a \<or>
    k = MKEndL \<and> a = TNil \<and> c = TNil \<or>
    (\<exists>x a' c' k'. a = x \<cdot> a' \<and> c = x \<cdot> c' \<and> k = MKLeft k' \<and> ptrace_merge_with a' TNil c' k')\<close>
  \<open>ptrace_merge_with a (bx \<cdot> b') c k \<longleftrightarrow>
    (k = MKEndL \<and> a = TNil \<and> c = bx \<cdot> b' \<or>
     (\<exists>k' c'. k = MKRight k' \<and> c = bx \<cdot> c' \<and> ptrace_merge_with a b' c' k') \<or>
     (\<exists>a' c' k' x.
        k = MKLeft k' \<and> a = x \<cdot> a' \<and> c = x \<cdot> c' \<and> ptrace_merge_with a' (bx \<cdot> b') c' k') \<or>
     (\<exists>a' c' k' q.
        k = MKSyncRL k' \<and> a = (snd bx, q) \<cdot> a' \<and> c = (fst bx, q) \<cdot> c' \<and>
        ptrace_merge_with a' b' c' k') \<or>
     (\<exists>a' c' k' q.
        k = MKSyncLR k' \<and> a = (q, fst bx) \<cdot> a' \<and> c = (q, snd bx) \<cdot> c' \<and>
        ptrace_merge_with a' b' c' k'))\<close>
  by (subst ptrace_merge_with.simps; cases k; force)+



lemma ptrace_merge_left_step:
  \<open>ptrace_merge (ax \<cdot> a') b c \<longleftrightarrow>
    (b = TNil \<and> c = ax \<cdot> a' \<or>
     (\<exists>c'. c = ax \<cdot> c' \<and> ptrace_merge a' b c') \<or>
     (\<exists>b' c' x. b = x \<cdot> b' \<and> c = x \<cdot> c' \<and> ptrace_merge (ax \<cdot> a') b' c') \<or>
     (\<exists>b' c' q. b = (snd ax, q) \<cdot> b' \<and> c = (fst ax, q) \<cdot> c' \<and> ptrace_merge a' b' c') \<or>
     (\<exists>b' c' q. b = (q, fst ax) \<cdot> b' \<and> c = (q, snd ax) \<cdot> c' \<and> ptrace_merge a' b' c'))\<close>
  apply (rule iffI)
   apply (blast dest: iffD1[OF ptrace_merge_with_left_step(2)])
  apply force
  done

lemma ptrace_merge_right_step:
  \<open>ptrace_merge a (bx \<cdot> b') c \<longleftrightarrow>
    (a = TNil \<and> c = bx \<cdot> b' \<or>
     (\<exists>c'. c = bx \<cdot> c' \<and> ptrace_merge a b' c') \<or>
     (\<exists>a' c' x. a = x \<cdot> a' \<and> c = x \<cdot> c' \<and> ptrace_merge a' (bx \<cdot> b') c') \<or>
     (\<exists>a' c' q. a = (snd bx, q) \<cdot> a' \<and> c = (fst bx, q) \<cdot> c' \<and> ptrace_merge a' b' c') \<or>
     (\<exists>a' c' q. a = (q, fst bx) \<cdot> a' \<and> c = (q, snd bx) \<cdot> c' \<and> ptrace_merge a' b' c'))\<close>
  apply (rule iffI)
   apply (blast dest: iffD1[OF ptrace_merge_with_right_step(2)])
  apply force
  done


lemma ptrace_merge_Nil[simp]:
  \<open>ptrace_merge TNil b c \<longleftrightarrow> c = b\<close>
  \<open>ptrace_merge a TNil c \<longleftrightarrow> c = a\<close>
  using ptrace_merge_with_TNil_same
  by blast+

lemma trace_map_trace_map[simp]: \<open>trace_map f (trace_map g a) = trace_map (f \<circ> g) a\<close>
  by (rule trace.coinduct[of
        \<open>\<lambda>x y. (\<exists>x' y'. x = trace_map f (trace_map g x') \<and> y = trace_map (f \<circ> g) y' \<and> x' = y')\<close>])
    force+


lemma ptrace_merge_with_comm':
  \<open>ptrace_merge_with a b c (flip_merge_tr k) \<Longrightarrow> ptrace_merge_with b a c k\<close>
  apply (rule ptrace_merge_with.coinduct[of \<open>\<lambda>b a c k. ptrace_merge_with a b c (flip_merge_tr k)\<close>])
   apply force
  apply (rename_tac b' a' c' k')
  apply (case_tac k'; force)
  done

lemma ptrace_merge_with_comm:
  \<open>ptrace_merge_with a b c k \<Longrightarrow> ptrace_merge_with b a c (flip_merge_tr k)\<close>
  using ptrace_merge_with_comm' by force

lemma ptrace_merge_comm:
  \<open>ptrace_merge a b c \<Longrightarrow> ptrace_merge b a c\<close>
  by (meson ptrace_merge_with_comm)

(*
thm ptrace_merge_with.intros
corec assoc_merge_tr_left :: \<open>merge_tr \<Rightarrow> merge_tr \<Rightarrow> merge_tr\<close> where
  \<open>assoc_merge_tr_left kab kabc =
        (case kabc of
          MKEndL \<Rightarrow> MKEndL \<comment> \<open>(TNil \<parallel> TNil) \<parallel> c \<leadsto> TNil \<parallel> (TNil \<parallel> c)\<close>
        | MKEndR \<Rightarrow> kab    \<comment> \<open>(a \<parallel> TNil) \<parallel> TNil \<leadsto> a \<parallel> (b \<parallel> TNil)\<close>
        | MKLeft kabc' \<Rightarrow>
            (case kab of
              MKEndL \<Rightarrow> MKEndL \<comment> \<open>(TNil \<parallel> (bx \<cdot> b')) \<parallel> c \<leadsto> TNil \<parallel> ((bx \<cdot> b') \<parallel> c)\<close>
            | MKEndR \<Rightarrow> MKLeft (assoc_merge_tr_left MKEndR kabc')
                \<comment> \<open>((ax \<cdot> a') \<parallel> TNil) \<parallel> c \<leadsto> (ax \<cdot> a') \<parallel> (TNil \<parallel> c)\<close>
            | MKLeft kab' \<Rightarrow> MKLeft (assoc_merge_tr_left kab' kabc')
                \<comment> \<open>((ax \<cdot> a') \<parallel> b) \<parallel> c \<leadsto> (ax \<cdot> a') \<parallel> (b \<parallel> c)\<close>
            | MKRight kab' \<Rightarrow> MKRight (assoc_merge_tr_left kab' kabc')
                \<comment> \<open>(a \<parallel> (bx \<cdot> b')) \<parallel> c \<leadsto> a \<parallel> ((bx \<cdot> b') \<parallel> c)\<close>
            | MKSyncLR kab' \<Rightarrow> MKSyncLR (assoc_merge_tr_left kab' kabc')
                \<comment> \<open>(((p,q) \<cdot> a') \<parallel> ((q,r) \<cdot> b')) \<parallel> c \<leadsto> ((p,q) \<cdot> a') \<parallel> (((q,r) \<cdot> b') \<parallel> c)\<close>
            | MKSyncRL kab' \<Rightarrow> MKSyncRL (assoc_merge_tr_left kab' kabc')
                \<comment> \<open>(((q,r) \<cdot> a') \<parallel> ((p,q) \<cdot> b')) \<parallel> c \<leadsto> ((q,r) \<cdot> a') \<parallel> (((p,q) \<cdot> b') \<parallel> c)\<close>)
        | MKRight kabc' \<Rightarrow>
            (case kab of
              MKEndL \<Rightarrow> MKEndL \<comment> \<open>(TNil \<parallel> b) \<parallel> (cx \<cdot> c') \<leadsto> TNil \<parallel> (b \<parallel> (cx \<cdot> c'))\<close>
            | MKEndR \<Rightarrow>  MKRight (assoc_merge_tr_left kab' kabc')
                \<comment> \<open>(a \<parallel> TNil) \<parallel> (cx \<cdot> c') \<leadsto> a \<parallel> (TNil \<parallel> (cx \<cdot> c'))\<close>
            | MKLeft kab' \<Rightarrow> MKLeft (assoc_merge_tr_left kab' kabc)
                \<comment> \<open>((ax \<cdot> a') \<parallel> b) \<parallel> (cx \<cdot> c') \<leadsto> (ax \<cdot> a') \<parallel> (b \<parallel> (cx \<cdot> c'))\<close>
            | MKRight kab' \<Rightarrow> MKRight (assoc_merge_tr_left kab' kabc')
                \<comment> \<open>(a \<parallel> (bx \<cdot> b')) \<parallel> (cx \<cdot> c') \<leadsto> a \<parallel> ((bx \<cdot> b') \<parallel> (cx \<cdot> c'))\<close>
            | MKSyncLR kab' \<Rightarrow> MKSyncLR (assoc_merge_tr_left kab' kabc')
                \<comment> \<open>(((p,q) \<cdot> a') \<parallel> ((q,r) \<cdot> b')) \<parallel> (cx \<cdot> c') \<leadsto> ((p,q) \<cdot> a') \<parallel> (((q,r) \<cdot> b') \<parallel> (cx \<cdot> c'))\<close>
            | MKSyncRL kab' \<Rightarrow> MKSyncRL (assoc_merge_tr_left kab' kabc')
                \<comment> \<open>(((q,r) \<cdot> a') \<parallel> ((p,q) \<cdot> b')) \<parallel> (cx \<cdot> c') \<leadsto> ((q,r) \<cdot> a') \<parallel> (((p,q) \<cdot> b') \<parallel> (cx \<cdot> c'))\<close>)
        | MKSyncLR kab' \<Rightarrow>
            (case kab of
              MKEndL \<Rightarrow> MKEndL \<comment> \<open>(a \<parallel> b) \<parallel> c \<leadsto> a \<parallel> (b \<parallel> c)\<close>
            | MKEndR \<Rightarrow> MKLeft (assoc_merge_tr_left MKEndR kabc')
                \<comment> \<open>(a \<parallel> b) \<parallel> c \<leadsto> a \<parallel> (b \<parallel> c)\<close>
            | MKLeft kab' \<Rightarrow> MKLeft (assoc_merge_tr_left kab' kabc')
                \<comment> \<open>(a \<parallel> b) \<parallel> c \<leadsto> a \<parallel> (b \<parallel> c)\<close>
            | MKRight kab' \<Rightarrow> MKRight (assoc_merge_tr_left kab' kabc')
                \<comment> \<open>(a \<parallel> b) \<parallel> c \<leadsto> a \<parallel> (b \<parallel> c)\<close>
            | MKSyncLR kab' \<Rightarrow> MKSyncLR (assoc_merge_tr_left kab' kabc')
                \<comment> \<open>(a \<parallel> b) \<parallel> c \<leadsto> a \<parallel> (b \<parallel> c)\<close>
            | MKSyncRL kab' \<Rightarrow> MKSyncRL (assoc_merge_tr_left kab' kabc')
                \<comment> \<open>(a \<parallel> b) \<parallel> c \<leadsto> a \<parallel> (b \<parallel> c)\<close>)
        | MKSyncRL kab' \<Rightarrow>
            (case kab of
              MKEndL \<Rightarrow> MKEndL \<comment> \<open>(a \<parallel> b) \<parallel> c \<leadsto> a \<parallel> (b \<parallel> c)\<close>
            | MKEndR \<Rightarrow> MKLeft (assoc_merge_tr_left MKEndR kabc')
                \<comment> \<open>(a \<parallel> b) \<parallel> c \<leadsto> a \<parallel> (b \<parallel> c)\<close>
            | MKLeft kab' \<Rightarrow> MKLeft (assoc_merge_tr_left kab' kabc')
                \<comment> \<open>(a \<parallel> b) \<parallel> c \<leadsto> a \<parallel> (b \<parallel> c)\<close>
            | MKRight kab' \<Rightarrow> MKRight (assoc_merge_tr_left kab' kabc')
                \<comment> \<open>(a \<parallel> b) \<parallel> c \<leadsto> a \<parallel> (b \<parallel> c)\<close>
            | MKSyncLR kab' \<Rightarrow> MKSyncLR (assoc_merge_tr_left kab' kabc')
                \<comment> \<open>(a \<parallel> b) \<parallel> c \<leadsto> a \<parallel> (b \<parallel> c)\<close>
            | MKSyncRL kab' \<Rightarrow> MKSyncRL (assoc_merge_tr_left kab' kabc')
                \<comment> \<open>(a \<parallel> b) \<parallel> c \<leadsto> a \<parallel> (b \<parallel> c)\<close>))\<close>

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
*)

lemma context_conj_ex_helperI:
  \<open>P x y \<Longrightarrow> (P x y \<Longrightarrow> Q x z) \<Longrightarrow> \<exists>x. Ex (P x) \<and> Ex (Q x)\<close>
  by blast

lemma pmergep_assoc1:
  assumes
    \<open>ptrace_merge_with a b m k1\<close>
    \<open>ptrace_merge_with m c d k2\<close>
  shows
    \<open>\<exists>m2. ptrace_merge c b m2 \<and> ptrace_merge m2 a d\<close>
  using assms
  apply -
  apply (rule context_conj_ex_helperI[
      where P=\<open>\<lambda>x k. ptrace_merge_with c b x k\<close> and Q=\<open>\<lambda>x k. ptrace_merge_with x a d k\<close>,
          OF ptrace_merge_with.coinduct ptrace_merge_with.coinduct,
        where ?X2=\<open>\<lambda>c b m2 y. ptrace_merge_with a b m k1 \<and> ptrace_merge_with m c d k2\<close>
          and ?X1=\<open>\<lambda>m2 a d z. ptrace_merge_with a b m k1 \<and> ptrace_merge_with m c d k2\<close>])
     apply blast
  
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