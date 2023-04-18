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
  MEndL |
  MEndR |
  MLeft merge_tr |
  MRight merge_tr |
  MSyncLR merge_tr |
  MSyncRL merge_tr



print_theorems

corec flip_merge_tr :: \<open>merge_tr \<Rightarrow> merge_tr\<close> where
  \<open>flip_merge_tr a =
    (case a of
      MEndL \<Rightarrow> MEndR
    | MEndR \<Rightarrow> MEndL
    | MLeft a' \<Rightarrow> MRight (flip_merge_tr a')
    | MRight a' \<Rightarrow> MLeft (flip_merge_tr a')
    | MSyncLR a' \<Rightarrow> MSyncRL (flip_merge_tr a')
    | MSyncRL a' \<Rightarrow> MSyncLR (flip_merge_tr a'))\<close>

print_theorems

lemma flip_merge_tr_simps[simp]:
  \<open>flip_merge_tr MEndR = MEndL\<close>
  \<open>flip_merge_tr MEndL = MEndR\<close>
  \<open>flip_merge_tr (MRight a) = MLeft (flip_merge_tr a)\<close>
  \<open>flip_merge_tr (MLeft a) = MRight (flip_merge_tr a)\<close>
  \<open>flip_merge_tr (MSyncLR a) = MSyncRL (flip_merge_tr a)\<close>
  \<open>flip_merge_tr (MSyncRL a) = MSyncLR (flip_merge_tr a)\<close>
  by (simp add: flip_merge_tr.code)+

lemma flip_merge_tr_eq_simps[iff]:
  \<open>flip_merge_tr k = MEndL \<longleftrightarrow> k = MEndR\<close>
  \<open>flip_merge_tr k = MEndR \<longleftrightarrow> k = MEndL\<close>
  \<open>flip_merge_tr k = MRight a \<longleftrightarrow> (\<exists>k'. k = MLeft k' \<and> flip_merge_tr k' = a)\<close>
  \<open>flip_merge_tr k = MLeft a \<longleftrightarrow> (\<exists>k'. k = MRight k' \<and> flip_merge_tr k' = a)\<close>
  \<open>flip_merge_tr k = MSyncLR a \<longleftrightarrow> (\<exists>k'. k = MSyncRL k' \<and> flip_merge_tr k' = a)\<close>
  \<open>flip_merge_tr k = MSyncRL a \<longleftrightarrow> (\<exists>k'. k = MSyncLR k' \<and> flip_merge_tr k' = a)\<close>
  by (cases k; simp; fail)+

lemma flip_merge_is_merge_tr_iff[iff]:
  \<open>is_MRight (flip_merge_tr k) \<longleftrightarrow> is_MLeft k\<close>
  \<open>is_MLeft (flip_merge_tr k) \<longleftrightarrow> is_MRight k\<close>
  \<open>is_MSyncLR (flip_merge_tr k) \<longleftrightarrow> is_MSyncRL k\<close>
  \<open>is_MSyncRL (flip_merge_tr k) \<longleftrightarrow> is_MSyncLR k\<close>
  by (cases k; simp; fail)+

lemma flip_merge_un_merge_tr_eq[simp]:
  \<open>is_MLeft k \<Longrightarrow> un_MRight (flip_merge_tr k) = flip_merge_tr (un_MLeft k)\<close>
  \<open>is_MRight k \<Longrightarrow> un_MLeft (flip_merge_tr k) = flip_merge_tr (un_MRight k)\<close>
  \<open>is_MSyncLR k \<Longrightarrow> un_MSyncRL (flip_merge_tr k) = flip_merge_tr (un_MSyncLR k)\<close>
  \<open>is_MSyncRL k \<Longrightarrow> un_MSyncLR (flip_merge_tr k) = flip_merge_tr (un_MSyncRL k)\<close>
  by (cases k; simp; fail)+

lemma flip_merge_key_idem[simp]:
  \<open>flip_merge_tr (flip_merge_tr k) = k\<close>
  by (rule merge_tr.coinduct[where
        R=\<open>\<lambda>x y. \<exists>x'. x = flip_merge_tr (flip_merge_tr x') \<and> x' = y\<close>
        ]) force+


coinductive ptrace_merge_with :: \<open>'a ptrace \<Rightarrow> 'a ptrace \<Rightarrow> 'a ptrace \<Rightarrow> merge_tr \<Rightarrow> bool\<close>
  where
  \<open>ptrace_merge_with TNil b b MEndL\<close>
| \<open>ptrace_merge_with a TNil a MEndR\<close>
| \<open>ptrace_merge_with a' b c k' \<Longrightarrow>
    ptrace_merge_with (ax \<cdot> a') b (ax \<cdot> c) (MLeft k')\<close>
| \<open>ptrace_merge_with a b' c k' \<Longrightarrow>
    ptrace_merge_with a (bx \<cdot> b') (bx \<cdot> c) (MRight k')\<close>
| \<open>ptrace_merge_with a' b' c' k' \<Longrightarrow>
    snd ax = fst bx \<Longrightarrow>
    cx = (fst ax, snd bx) \<Longrightarrow>
    ptrace_merge_with (ax \<cdot> a') (bx \<cdot> b') (cx \<cdot> c') (MSyncLR k')\<close>
| \<open>ptrace_merge_with a' b' c' k' \<Longrightarrow>
    fst ax = snd bx \<Longrightarrow>
    cx = (fst bx, snd ax) \<Longrightarrow>
    ptrace_merge_with (ax \<cdot> a') (bx \<cdot> b') (cx \<cdot> c') (MSyncRL k')\<close>

print_theorems

abbreviation ptrace_merge :: \<open>'a ptrace \<Rightarrow> 'a ptrace \<Rightarrow> 'a ptrace \<Rightarrow> bool\<close> where
  \<open>ptrace_merge a b c \<equiv> Ex (ptrace_merge_with a b c)\<close>


lemma ptrace_merge_with_merge_tr_iff[iff]:
  \<open>ptrace_merge_with a b c MEndL \<longleftrightarrow> a = TNil \<and> c = b\<close>
  \<open>ptrace_merge_with a b c MEndR \<longleftrightarrow> b = TNil \<and> c = a\<close>
  \<open>ptrace_merge_with a b c (MLeft k') \<longleftrightarrow>
    (\<exists>x a' c'. a = (x \<cdot> a') \<and> c = (x \<cdot> c') \<and> ptrace_merge_with a' b c' k')\<close>
  \<open>ptrace_merge_with a b c (MRight k') \<longleftrightarrow>
    (\<exists>x b' c'. b = (x \<cdot> b') \<and> c = (x \<cdot> c') \<and> ptrace_merge_with a b' c' k')\<close>
  \<open>ptrace_merge_with a b c (MSyncLR k') \<longleftrightarrow>
    (\<exists>p q r a' b' c'. a = ((p,q) \<cdot> a') \<and> b = (q,r) \<cdot> b' \<and> c = ((p,r) \<cdot> c') \<and> ptrace_merge_with a' b' c' k')\<close>
  \<open>ptrace_merge_with a b c (MSyncRL k') \<longleftrightarrow>
    (\<exists>p q r a' b' c'. a = ((q,r) \<cdot> a') \<and> b = (p,q) \<cdot> b' \<and> c = ((p,r) \<cdot> c') \<and> ptrace_merge_with a' b' c' k')\<close>
  by (subst ptrace_merge_with.simps, force)+


lemma ptrace_merge_with_TNil_same:
  \<open>ptrace_merge_with TNil b c k \<Longrightarrow> b = c\<close>
  \<open>ptrace_merge_with a TNil c k \<Longrightarrow> a = c\<close>
  apply (rule trace.coinduct[of \<open>\<lambda>x y. \<exists>k. ptrace_merge_with TNil x y k\<close>], force,
      clarsimp, case_tac ka; force)
  apply (rule trace.coinduct[of \<open>\<lambda>x y. \<exists>k. ptrace_merge_with x TNil y k\<close>], force,
      clarsimp, case_tac ka; force)
  done

lemma ptrace_merge_with_TNil_out[simp]:
  \<open>ptrace_merge_with a b TNil k \<longleftrightarrow> a = TNil \<and> b = TNil \<and> (k = MEndL \<or> k = MEndR)\<close>
  by (force elim: ptrace_merge_with.cases)


lemma ptrace_merge_with_left_step:
  \<open>ptrace_merge_with TNil b c k \<longleftrightarrow>
    k = MEndL \<and> c = b \<or>
    k = MEndR \<and> b = TNil \<and> c = TNil \<or>
    (\<exists>x b' c' k'. b = x \<cdot> b' \<and> c = x \<cdot> c' \<and> k = MRight k' \<and> ptrace_merge_with TNil b' c' k')\<close>
  \<open>ptrace_merge_with (ax \<cdot> a') b c k \<longleftrightarrow>
    (k = MEndR \<and> b = TNil \<and> c = ax \<cdot> a' \<or>
     (\<exists>k' c'. k = MLeft k' \<and> c = ax \<cdot> c' \<and> ptrace_merge_with a' b c' k') \<or>
     (\<exists>b' c' k' x.
        k = MRight k' \<and> b = x \<cdot> b' \<and> c = x \<cdot> c' \<and> ptrace_merge_with (ax \<cdot> a') b' c' k') \<or>
     (\<exists>b' c' k' q.
        k = MSyncLR k' \<and> b = (snd ax, q) \<cdot> b' \<and> c = (fst ax, q) \<cdot> c' \<and>
        ptrace_merge_with a' b' c' k') \<or>
     (\<exists>b' c' k' q.
        k = MSyncRL k' \<and> b = (q, fst ax) \<cdot> b' \<and> c = (q, snd ax) \<cdot> c' \<and>
        ptrace_merge_with a' b' c' k'))\<close>
  by (subst ptrace_merge_with.simps; cases k; force)+

lemma ptrace_merge_with_right_step:
  \<open>ptrace_merge_with a TNil c k \<longleftrightarrow>
    k = MEndR \<and> c = a \<or>
    k = MEndL \<and> a = TNil \<and> c = TNil \<or>
    (\<exists>x a' c' k'. a = x \<cdot> a' \<and> c = x \<cdot> c' \<and> k = MLeft k' \<and> ptrace_merge_with a' TNil c' k')\<close>
  \<open>ptrace_merge_with a (bx \<cdot> b') c k \<longleftrightarrow>
    (k = MEndL \<and> a = TNil \<and> c = bx \<cdot> b' \<or>
     (\<exists>k' c'. k = MRight k' \<and> c = bx \<cdot> c' \<and> ptrace_merge_with a b' c' k') \<or>
     (\<exists>a' c' k' x.
        k = MLeft k' \<and> a = x \<cdot> a' \<and> c = x \<cdot> c' \<and> ptrace_merge_with a' (bx \<cdot> b') c' k') \<or>
     (\<exists>a' c' k' q.
        k = MSyncRL k' \<and> a = (snd bx, q) \<cdot> a' \<and> c = (fst bx, q) \<cdot> c' \<and>
        ptrace_merge_with a' b' c' k') \<or>
     (\<exists>a' c' k' q.
        k = MSyncLR k' \<and> a = (q, fst bx) \<cdot> a' \<and> c = (q, snd bx) \<cdot> c' \<and>
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


thm ptrace_merge_with.intros
corec assoc_merge_tr_left :: \<open>merge_tr \<Rightarrow> merge_tr \<Rightarrow> merge_tr\<close> where
  \<open>assoc_merge_tr_left kab kabc =
        (case kabc of
          MEndL \<Rightarrow> MEndL \<comment> \<open>(TNil \<parallel> TNil) \<parallel> c \<leadsto> TNil \<parallel> (TNil \<parallel> c)\<close>
        | MEndR \<Rightarrow> kab    \<comment> \<open>(a \<parallel> TNil) \<parallel> TNil \<leadsto> a \<parallel> (b \<parallel> TNil)\<close>
        | MLeft kabc' \<Rightarrow>
            (case kab of
              MEndL \<Rightarrow> MEndL \<comment> \<open>(TNil \<parallel> (bx \<cdot> b')) \<parallel> c \<leadsto> TNil \<parallel> ((bx \<cdot> b') \<parallel> c)\<close>
            | MEndR \<Rightarrow> MLeft (assoc_merge_tr_left MEndR kabc')
                \<comment> \<open>((ax \<cdot> a') \<parallel> TNil) \<parallel> c \<leadsto> (ax \<cdot> a') \<parallel> (TNil \<parallel> c)\<close>
            | MLeft kab' \<Rightarrow> MLeft (assoc_merge_tr_left kab' kabc')
                \<comment> \<open>((ax \<cdot> a') \<parallel> b) \<parallel> c \<leadsto> (ax \<cdot> a') \<parallel> (b \<parallel> c)\<close>
            | MRight kab' \<Rightarrow> MRight (assoc_merge_tr_left kab' kabc')
                \<comment> \<open>(a \<parallel> (bx \<cdot> b')) \<parallel> c \<leadsto> a \<parallel> ((bx \<cdot> b') \<parallel> c)\<close>
            | MSyncLR kab' \<Rightarrow> MSyncLR (assoc_merge_tr_left kab' kabc')
                \<comment> \<open>(((p,q) \<cdot> a') \<parallel> ((q,r) \<cdot> b')) \<parallel> c \<leadsto> ((p,q) \<cdot> a') \<parallel> (((q,r) \<cdot> b') \<parallel> c)\<close>
            | MSyncRL kab' \<Rightarrow> MSyncRL (assoc_merge_tr_left kab' kabc')
                \<comment> \<open>(((q,r) \<cdot> a') \<parallel> ((p,q) \<cdot> b')) \<parallel> c \<leadsto> ((q,r) \<cdot> a') \<parallel> (((p,q) \<cdot> b') \<parallel> c)\<close>)
        | MRight kabc' \<Rightarrow> MRight (assoc_merge_tr_left kab kabc')
            \<comment> \<open> (a \<parallel> b) \<parallel> [cx \<cdot> c'] \<leadsto> a \<parallel> [b \<parallel> (cx \<cdot> c')]\<close>
        | MSyncLR kabc' \<Rightarrow>
            \<comment> \<open> a1 \<parallel> b1 = (pa,qa) \<cdot> ab' \<and> c = (qa,ra) \<cdot> c'\<close>
            (case kab of
              MEndL \<Rightarrow> MEndL
                \<comment> \<open> TNil \<parallel> (bx \<cdot> b' \<parallel> cx \<cdot> c')\<close>
            | MEndR \<Rightarrow> MSyncLR (assoc_merge_tr_left MEndR kabc')
                \<comment> \<open> (ax \<cdot> a') \<parallel> (TNil \<parallel> cx \<cdot> c')\<close>
            | MLeft kab' \<Rightarrow> MSyncLR (assoc_merge_tr_left kab' kabc')
                \<comment> \<open> (ax \<cdot> a') \<parallel> (b \<parallel> cx \<cdot> c')\<close>
            | MRight kab' \<Rightarrow> MRight (assoc_merge_tr_left kab' kabc')
                \<comment> \<open> a \<parallel> ((bx \<cdot> b') \<parallel> (cx \<cdot> c'))\<close>
            | MSyncLR kab' \<Rightarrow> MSyncLR (assoc_merge_tr_left kab' kabc')
                \<comment> \<open> ((p,q) \<cdot> a') \<parallel> (((q,r) \<cdot> b') \<parallel> ((r,s) \<cdot> c'))\<close>
            | MSyncRL kab' \<Rightarrow>
                MSyncRL (MSyncRL (assoc_merge_tr_left kab' kabc'))
                \<comment> \<open> n.b. this requires multiple merge-keys \<close>
                \<comment> \<open> ((q,r) \<cdot> a') \<parallel> (((p,q) \<cdot> b') \<parallel> ((r,s) \<cdot> c'))\<close>)
        | MSyncRL kabc' \<Rightarrow>
            \<comment> \<open> a1 \<parallel> b1 = (qx,rx) \<cdot> ab' \<and> c = (px,qx) \<cdot> c' \<close>
            (case kab of
              MEndL \<Rightarrow> MEndL
                \<comment> \<open> TNil \<parallel> ((q,r) \<cdot> b' \<parallel> (p,q) \<cdot> c') \<close>
            | MEndR \<Rightarrow> MSyncRL (assoc_merge_tr_left MEndR kabc')
                \<comment> \<open> ((q,r) \<cdot> a') \<parallel> ((p,q) \<parallel> cx \<cdot> c') \<close>
            | MLeft kab' \<Rightarrow> MSyncRL (assoc_merge_tr_left kab' kabc')
                \<comment> \<open> ((q,r) \<cdot> a') \<parallel> (b \<parallel> (p,q) \<cdot> c') \<close>
            | MRight kab' \<Rightarrow> MRight (assoc_merge_tr_left kab' kabc')
                \<comment> \<open> a \<parallel> (((q,r) \<cdot> b') \<parallel> ((p,q) \<cdot> c')) \<close>
            | MSyncLR kab' \<Rightarrow> MSyncLR (assoc_merge_tr_left kab' kabc')
                \<comment> \<open> ((p,q) \<cdot> a') \<parallel> ( ((q,r) \<cdot> b') \<parallel> ((r,s) \<cdot> c') ) \<close>
            | MSyncRL kab' \<Rightarrow>
                MSyncRL (assoc_merge_tr_left kab' kabc')
                \<comment> \<open> ((q,r) \<cdot> a') \<parallel> ( ((p,q) \<cdot> b') \<parallel> ((k,p) \<cdot> c') ) \<close>))\<close>

lemma assoc_merge_tr_left_eqL:
  \<open>assoc_merge_tr_left MEndL kabc =
    (case kabc of
      MEndL \<Rightarrow> MEndL
    | MEndR \<Rightarrow> MEndL
    | MLeft _ \<Rightarrow> MEndL
    | MRight kabc' \<Rightarrow>  MRight (assoc_merge_tr_left MEndL kabc')
    | MSyncLR _ \<Rightarrow> MEndL
    | MSyncRL _ \<Rightarrow> MEndL)\<close>
  \<open>assoc_merge_tr_left MEndR kabc =
    (case kabc of
      MEndL \<Rightarrow> MEndL
    | MEndR \<Rightarrow> MEndR
    | MLeft kabc' \<Rightarrow> MLeft (assoc_merge_tr_left MEndR kabc')
    | MRight kabc' \<Rightarrow> MRight (assoc_merge_tr_left MEndR kabc')
    | MSyncLR kabc' \<Rightarrow> MSyncLR (assoc_merge_tr_left MEndR kabc')
    | MSyncRL kabc' \<Rightarrow> MSyncRL (assoc_merge_tr_left MEndR kabc'))\<close>
  \<open>assoc_merge_tr_left (MLeft kab') kabc =
    (case kabc of
      MEndL \<Rightarrow> MEndL
    | MEndR \<Rightarrow> MLeft kab'
    | MLeft kabc' \<Rightarrow> MLeft (assoc_merge_tr_left kab' kabc')
    | MRight kabc' \<Rightarrow> MRight (assoc_merge_tr_left (MLeft kab') kabc')
    | MSyncLR kabc' \<Rightarrow> MSyncLR (assoc_merge_tr_left kab' kabc')
    | MSyncRL kabc' \<Rightarrow> MSyncRL (assoc_merge_tr_left kab' kabc'))\<close>
  \<open>assoc_merge_tr_left (MRight kab') kabc =
    (case kabc of
      MEndL \<Rightarrow> MEndL
    | MEndR \<Rightarrow> MRight kab'
    | MLeft kabc' \<Rightarrow>  MRight (assoc_merge_tr_left kab' kabc')
    | MRight kabc' \<Rightarrow> MRight (assoc_merge_tr_left (MRight kab') kabc')
    | MSyncLR kabc' \<Rightarrow> MRight (assoc_merge_tr_left kab' kabc')
    | MSyncRL kabc' \<Rightarrow> MRight (assoc_merge_tr_left kab' kabc'))\<close>
  \<open>assoc_merge_tr_left (MSyncLR kab') kabc =
    (case kabc of
      MEndL \<Rightarrow> MEndL
    | MEndR \<Rightarrow> MSyncLR kab'
    | MLeft kabc' \<Rightarrow> MSyncLR (assoc_merge_tr_left kab' kabc')
    | MRight kabc' \<Rightarrow> MRight (assoc_merge_tr_left (MSyncLR kab') kabc')
    | MSyncLR kabc' \<Rightarrow> MSyncLR (assoc_merge_tr_left kab' kabc')
    | MSyncRL kabc' \<Rightarrow> MSyncLR (assoc_merge_tr_left kab' kabc'))\<close>
  \<open>assoc_merge_tr_left (MSyncRL kab') kabc =
    (case kabc of
      MEndL \<Rightarrow> MEndL
    | MEndR \<Rightarrow> MSyncRL kab'
    | MLeft kabc' \<Rightarrow>  MSyncRL (assoc_merge_tr_left kab' kabc')
    | MRight kabc' \<Rightarrow> MRight (assoc_merge_tr_left (MSyncRL kab') kabc')
    | MSyncLR kabc' \<Rightarrow> MSyncRL (MSyncRL (assoc_merge_tr_left kab' kabc'))
    | MSyncRL kabc' \<Rightarrow> MSyncRL (assoc_merge_tr_left kab' kabc'))\<close>
  by ((simp add: assoc_merge_tr_left.code, simp split: merge_tr.splits); fail)+

lemma assoc_merge_tr_left_eqR:
  \<open>assoc_merge_tr_left kab MEndL = MEndL\<close>
  \<open>assoc_merge_tr_left kab MEndR = kab\<close>
  \<open>assoc_merge_tr_left kab (MLeft kabc') =
    (case kab of
      MEndL \<Rightarrow> MEndL
    | MEndR \<Rightarrow>  MLeft (assoc_merge_tr_left MEndR kabc')
    | MLeft kab' \<Rightarrow> MLeft (assoc_merge_tr_left kab' kabc')
    | MRight kab' \<Rightarrow> MRight (assoc_merge_tr_left kab' kabc')
    | MSyncLR kab' \<Rightarrow> MSyncLR (assoc_merge_tr_left kab' kabc')
    | MSyncRL kab' \<Rightarrow> MSyncRL (assoc_merge_tr_left kab' kabc'))\<close>
  \<open>assoc_merge_tr_left kab (MRight kabc') = MRight (assoc_merge_tr_left kab kabc')\<close>
  \<open>assoc_merge_tr_left kab (MSyncLR kabc') =
    (case kab of
      MEndL \<Rightarrow> MEndL
    | MEndR \<Rightarrow> MSyncLR (assoc_merge_tr_left MEndR kabc')
    | MLeft kab' \<Rightarrow> MSyncLR (assoc_merge_tr_left kab' kabc')
    | MRight kab' \<Rightarrow> MRight (assoc_merge_tr_left kab' kabc')
    | MSyncLR kab' \<Rightarrow> MSyncLR (assoc_merge_tr_left kab' kabc')
    | MSyncRL kab' \<Rightarrow> MSyncRL (MSyncRL (assoc_merge_tr_left kab' kabc')))\<close>
  \<open>assoc_merge_tr_left kab (MSyncRL kabc') =
    (case kab of
      MEndL \<Rightarrow> MEndL
    | MEndR \<Rightarrow> MSyncRL (assoc_merge_tr_left MEndR kabc')
    | MLeft kab' \<Rightarrow>  MSyncRL (assoc_merge_tr_left kab' kabc')
    | MRight kab' \<Rightarrow> MRight (assoc_merge_tr_left kab' kabc')
    | MSyncLR kab' \<Rightarrow> MSyncLR (assoc_merge_tr_left kab' kabc')
    | MSyncRL kab' \<Rightarrow> MSyncRL (assoc_merge_tr_left kab' kabc'))\<close>
  by (simp add: assoc_merge_tr_left.code; cases kab; simp; fail)+



corec assoc_merge_tr_right :: \<open>merge_tr \<Rightarrow> merge_tr \<Rightarrow> merge_tr\<close> where
  \<open>assoc_merge_tr_right kab kabc =
        (case kabc of
          MEndL \<Rightarrow> MEndL \<comment> \<open> _ \<parallel> (TNil \<parallel> c)\<close>
        | MEndR \<Rightarrow> MEndR \<comment> \<open> _ \<parallel> (b \<parallel> TNil)\<close>
        | MLeft kabc' \<Rightarrow>
            (case kab of
              MEndL \<Rightarrow> MLeft (assoc_merge_tr_right MEndL kabc')
                \<comment> \<open> _ \<parallel> (bx \<cdot> b' \<parallel> c) \<close>
            | MEndR \<Rightarrow> MEndL
                \<comment> \<open> _ \<parallel> (TNil \<parallel> c)\<close>
            | MLeft kab' \<Rightarrow> undefined \<comment> \<open> (assoc_merge_tr_right kab' kabc') \<close>
                \<comment> \<open> _ \<parallel> (b \<parallel> c) \<close>
            | MRight kab' \<Rightarrow> MLeft (assoc_merge_tr_right kab' kabc')
                \<comment> \<open> _ \<parallel> ((bx \<cdot> b') \<parallel> c) \<close>
            | MSyncLR kab' \<Rightarrow> MLeft (assoc_merge_tr_right kab' kabc')
                \<comment> \<open> _ \<parallel> ((q,r) \<cdot> b' \<parallel> c) \<close>
            | MSyncRL kab' \<Rightarrow> MLeft (assoc_merge_tr_right kab' kabc')
                \<comment> \<open> _ \<parallel> ((p,q) \<cdot> b' \<parallel> c \<close>)
        | MRight kabc' \<Rightarrow> MRight (assoc_merge_tr_right kab kabc')
            \<comment> \<open> _ \<parallel> (b \<parallel> (cx \<cdot> c')) \<close>
        | MSyncLR kabc' \<Rightarrow>
            \<comment> \<open> a1 \<parallel> b1 = (pa,qa) \<cdot> ab' \<and> c = (qa,ra) \<cdot> c'\<close>
            (case kab of
              MEndL \<Rightarrow> MSyncLR (assoc_merge_tr_right MEndL kabc')
                \<comment> \<open> _ \<parallel> ((p,q) \<cdot> b' \<parallel> (q,r) \<cdot> c')\<close>
            | MEndR \<Rightarrow> MRight (assoc_merge_tr_right MEndR kabc')
                \<comment> \<open> _ \<parallel> (TNil \<parallel> cx \<cdot> c')\<close>
            | MLeft kab' \<Rightarrow> MRight (assoc_merge_tr_right kab' kabc')
                \<comment> \<open> _ \<parallel> (b \<parallel> cx \<cdot> c')\<close>
            | MRight kab' \<Rightarrow> MSyncLR (assoc_merge_tr_right kab' kabc')
                \<comment> \<open> _ \<parallel> (((p,q) \<cdot> b') \<parallel> ((q,r) \<cdot> c'))\<close>
            | MSyncLR kab' \<Rightarrow> MSyncLR (assoc_merge_tr_right kab' kabc')
                \<comment> \<open> (_ \<parallel> (((q,r) \<cdot> b') \<parallel> ((r,s) \<cdot> c'))\<close>
            | MSyncRL kab' \<Rightarrow>
                MRight (MLeft (assoc_merge_tr_right kab' kabc'))
                \<comment> \<open> n.b. this requires multiple merge-keys \<close>
                \<comment> \<open> ((q,r) \<cdot> a') \<parallel> (((p,q) \<cdot> b') \<parallel> ((r,s) \<cdot> c'))\<close>)
        | MSyncRL kabc' \<Rightarrow>
            \<comment> \<open> a1 \<parallel> b1 = (qx,rx) \<cdot> ab' \<and> c = (px,qx) \<cdot> c' \<close>
            (case kab of
              MEndL \<Rightarrow> MSyncRL (assoc_merge_tr_right kab kabc')
                \<comment> \<open> _ \<parallel> ((q,r) \<cdot> b' \<parallel> (p,q) \<cdot> c') \<close>
            | MEndR \<Rightarrow> MRight (assoc_merge_tr_right MEndR kabc')
                \<comment> \<open> _ \<parallel> (TNil \<parallel> (p,q) \<cdot> c') \<close>
            | MLeft kab' \<Rightarrow> MRight (assoc_merge_tr_right kab' kabc')
                \<comment> \<open> _ \<parallel> (b \<parallel> ((p,q) \<cdot> c')) \<close>
            | MRight kab' \<Rightarrow> MSyncRL (assoc_merge_tr_right kab' kabc')
                \<comment> \<open> _ \<parallel> (((q,r) \<cdot> b') \<parallel> ((p,q) \<cdot> c')) \<close>
            | MSyncLR kab' \<Rightarrow> MSyncLR (assoc_merge_tr_right kab' kabc')
                \<comment> \<open> _ \<parallel> ( ((q,r) \<cdot> b') \<parallel> ((r,s) \<cdot> c') ) \<close>
            | MSyncRL kab' \<Rightarrow>
                MSyncRL (assoc_merge_tr_right kab' kabc')
                \<comment> \<open> _ \<parallel> ( ((p,q) \<cdot> b') \<parallel> ((k,p) \<cdot> c') ) \<close>))\<close>


(*
lemma flip_merge_tr_eq_simps[iff]:
  \<open>flip_merge_tr k = MEndL \<longleftrightarrow> k = MEndR\<close>
  \<open>flip_merge_tr k = MEndR \<longleftrightarrow> k = MEndL\<close>
  \<open>flip_merge_tr k = MRight a \<longleftrightarrow> (\<exists>k'. k = MLeft k' \<and> flip_merge_tr k' = a)\<close>
  \<open>flip_merge_tr k = MLeft a \<longleftrightarrow> (\<exists>k'. k = MRight k' \<and> flip_merge_tr k' = a)\<close>
  \<open>flip_merge_tr k = MSyncLR a \<longleftrightarrow> (\<exists>k'. k = MSyncRL k' \<and> flip_merge_tr k' = a)\<close>
  \<open>flip_merge_tr k = MSyncRL a \<longleftrightarrow> (\<exists>k'. k = MSyncLR k' \<and> flip_merge_tr k' = a)\<close>
  by (cases k; simp; fail)+

lemma flip_merge_is_merge_tr_iff[iff]:
  \<open>is_MRight (flip_merge_tr k) \<longleftrightarrow> is_MLeft k\<close>
  \<open>is_MLeft (flip_merge_tr k) \<longleftrightarrow> is_MRight k\<close>
  \<open>is_MSyncLR (flip_merge_tr k) \<longleftrightarrow> is_MSyncRL k\<close>
  \<open>is_MSyncRL (flip_merge_tr k) \<longleftrightarrow> is_MSyncLR k\<close>
  by (cases k; simp; fail)+

lemma flip_merge_un_merge_tr_eq[simp]:
  \<open>is_MLeft k \<Longrightarrow> un_MRight (flip_merge_tr k) = flip_merge_tr (un_MLeft k)\<close>
  \<open>is_MRight k \<Longrightarrow> un_MLeft (flip_merge_tr k) = flip_merge_tr (un_MRight k)\<close>
  \<open>is_MSyncLR k \<Longrightarrow> un_MSyncRL (flip_merge_tr k) = flip_merge_tr (un_MSyncLR k)\<close>
  \<open>is_MSyncRL k \<Longrightarrow> un_MSyncLR (flip_merge_tr k) = flip_merge_tr (un_MSyncRL k)\<close>
  by (cases k; simp; fail)+
*)

lemma context_conj_ex_helperI:
  \<open>P x y \<Longrightarrow> (P x y \<Longrightarrow> Q x z) \<Longrightarrow> \<exists>x. Ex (P x) \<and> Ex (Q x)\<close>
  by blast


lemma pmergep_assoc1:
  assumes
    \<open>ptrace_merge_with a b m k1\<close>
    \<open>ptrace_merge_with m c d k2\<close>
    \<open>ptrace_merge_with c b m2a (assoc_merge_tr_left k1 k2)\<close>
    \<open>ptrace_merge_with m2b a d (assoc_merge_tr_right k1 k2)\<close>
  shows
    \<open>m2a = m2b\<close>
  using assms
  apply -
  apply (rule trace.coinduct[of \<open>\<lambda>x y.
    \<exists>a b m k1 c d k2.
      ptrace_merge_with a b m k1 \<and>
      ptrace_merge_with m c d k2 \<and>
      ptrace_merge_with c b x (assoc_merge_tr_left k1 k2) \<and>
      ptrace_merge_with y a d (assoc_merge_tr_right k1 k2)\<close>])
   apply blast
  apply (thin_tac \<open>_ m\<close>, thin_tac \<open>_ m\<close>, thin_tac \<open>_ k1\<close>, thin_tac \<open>_ k2\<close>)
  apply clarsimp
  apply (rename_tac m2a' m2b' a' b' m' k1' c' d' k2')
  apply (case_tac m2a')
   apply simp
   apply (erule disjE)
    apply (subst (asm) assoc_merge_tr_left.code, simp split: merge_tr.splits)
   apply (subst (asm) assoc_merge_tr_left.code, subst (asm) assoc_merge_tr_right.code,
      simp split: merge_tr.splits)
  apply (case_tac m2b')
   apply clarsimp
   apply (subst (asm) ptrace_merge_with.simps[of TNil])
   apply clarsimp
   apply (erule disjE)
    apply clarsimp
    apply (subst (asm) assoc_merge_tr_right.code, simp split: merge_tr.splits)
      apply (subst (asm) assoc_merge_tr_left_eqR, force)
     apply (subst (asm) assoc_merge_tr_left.code)
     apply clarsimp
     apply (frule ptrace_merge_with_TNil_same)
     apply clarsimp

  sorry

lemma pmergep_assoc1:
  assumes
    \<open>ptrace_merge_with a b m k1\<close>
    \<open>ptrace_merge_with m c d k2\<close>
  shows
    \<open>\<exists>m2. ptrace_merge_with c b m2 (assoc_merge_tr_left k1 k2) \<and> ptrace_merge_with m2 a d (assoc_merge_tr_right k1 k2)\<close>
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