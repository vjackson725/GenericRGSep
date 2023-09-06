theory RGSep
  imports Stabilisation
begin

datatype 'h comm =
  Skip
  | Seq \<open>'h comm\<close> \<open>'h comm\<close> (infixr \<open>;;\<close> 75)
  | Par \<open>'h comm\<close> \<open>'h comm\<close> (infixr \<open>\<parallel>\<close> 65)
  | Ndet \<open>'h comm\<close> \<open>'h comm\<close> (infixr \<open>\<^bold>+\<close> 65)
(*
  | ExtNdet \<open>'h comm\<close> \<open>'h comm\<close> (infixr \<open>\<^bold>\<box>\<close> 65)
*)
  | Iter \<open>'h comm\<close> (\<open>_\<^sup>\<star>\<close> [80] 80)
  | Basic \<open>'h \<Rightarrow> 'h \<Rightarrow> bool\<close>

datatype 'h act =
    Tau
  | Env 'h 'h

lemma act_neq_iff[simp]:
  \<open>a \<noteq> Tau \<longleftrightarrow> (\<exists>x y. a = Env x y)\<close>
  \<open>Tau \<noteq> a \<longleftrightarrow> (\<exists>x y. a = Env x y)\<close>
  by (metis act.distinct(1) act.exhaust)+

inductive basics_guarantee :: \<open>('h \<Rightarrow> 'h \<Rightarrow> bool) \<Rightarrow> 'h comm \<Rightarrow> bool\<close> where
  skip[iff]: \<open>basics_guarantee g Skip\<close>
| seq[intro!]: \<open>basics_guarantee g c1 \<Longrightarrow> basics_guarantee g c2 \<Longrightarrow> basics_guarantee g (c1 ;; c2)\<close>
| par[intro!]: \<open>basics_guarantee g c1 \<Longrightarrow> basics_guarantee g c2 \<Longrightarrow> basics_guarantee g (c1 \<parallel> c2)\<close>
| ndet[intro!]: \<open>basics_guarantee g c1 \<Longrightarrow> basics_guarantee g c2 \<Longrightarrow> basics_guarantee g (c1 \<^bold>+ c2)\<close>
| iter[intro!]: \<open>basics_guarantee g c \<Longrightarrow> basics_guarantee g (c\<^sup>\<star>)\<close>
| basic[intro!]: \<open>g \<le> g' \<Longrightarrow> basics_guarantee g (Basic g')\<close>

inductive_cases basics_guarantee_skipE[elim!]: \<open>basics_guarantee g Skip\<close>
inductive_cases basics_guarantee_seqE[elim!]: \<open>basics_guarantee g (c1 ;; c2)\<close>
inductive_cases basics_guarantee_ndetE[elim!]: \<open>basics_guarantee g (c1 \<^bold>+ c2)\<close>
inductive_cases basics_guarantee_parE[elim!]: \<open>basics_guarantee g (c1 \<parallel>  c2)\<close>
inductive_cases basics_guarantee_iterE[elim!]: \<open>basics_guarantee g (c\<^sup>\<star>)\<close>
inductive_cases basics_guarantee_basicE[elim!]: \<open>basics_guarantee g (Basic g')\<close>


inductive opsem :: \<open>('h \<Rightarrow> 'h \<Rightarrow> bool) \<Rightarrow> 'h act \<Rightarrow> 'h \<times> 'h comm \<Rightarrow> 'h \<times> 'h comm \<Rightarrow> bool\<close> where
  seq_left[intro!]: \<open>opsem r a (h,c1) (h',c1') \<Longrightarrow> opsem r a (h, c1 ;; c2) (h', c1' ;; c2)\<close>
| seq_right[intro!]: \<open>opsem r Tau (h, Skip ;; c2) (h, c2)\<close>
| ndet_left[intro!]: \<open>opsem r Tau (h, s \<^bold>+ t) (h, s)\<close>
| ndet_right[intro!]: \<open>opsem r Tau (h, s \<^bold>+ t) (h, t)\<close>
(*
| extndet_resolve_left[intro]:
  \<open>opsem r a (h, c1) (h', c1') \<Longrightarrow> a \<noteq> Tau \<Longrightarrow> opsem r a (h, c1 \<^bold>\<box> c2) (h', c1')\<close>
| extndet_resolve_right[intro]:
  \<open>opsem r a (h, c2) (h', c2') \<Longrightarrow> a \<noteq> Tau \<Longrightarrow> opsem r a (h, c1 \<^bold>\<box> c2) (h', c2')\<close>
| extndet_step_left[intro]:
  \<open>opsem r Tau (h, c1) (h', c1') \<Longrightarrow> opsem r Tau (h, c1 \<^bold>\<box> c2) (h', c1' \<^bold>\<box> c2)\<close>
| extndet_step_right[intro]:
  \<open>opsem r Tau (h, c2) (h', c2') \<Longrightarrow> opsem r Tau (h, c1 \<^bold>\<box> c2) (h', c1 \<^bold>\<box> c2')\<close>
*)
| par_step_left[intro]: \<open>opsem r a (h, s) (h', s') \<Longrightarrow> opsem r a (h, s \<parallel> t) (h', s' \<parallel> t)\<close>
| par_step_right[intro]: \<open>opsem r a (h, t) (h', t') \<Longrightarrow> opsem r a (h, s \<parallel> t) (h', s \<parallel> t')\<close>
| par_left[intro!]: \<open>opsem r Tau (h, Skip \<parallel> t) (h, t)\<close>
| par_right[intro!]: \<open>opsem r Tau (h, s \<parallel> Skip) (h, s)\<close>
| iter[intro]: \<open>opsem r Tau (h, c\<^sup>\<star>) (h, c ;; c\<^sup>\<star>)\<close> (* ideally a different semantics here *)
| basic[intro!]: \<open>g h h' \<Longrightarrow> opsem r Tau (h, Basic g) (h', Skip)\<close>
| env[intro!]: \<open>r h h' \<Longrightarrow> opsem r (Env h h') (h, t) (h', t)\<close>

inductive_cases opsem_seqE[elim!]: \<open>opsem r a (h, c1 ;; c2) (h', c')\<close>
inductive_cases opsem_ndetE[elim!]: \<open>opsem r a (h, c1 \<^bold>+ c2) (h', c')\<close>
inductive_cases opsem_parE[elim!]: \<open>opsem r a (h, c1 \<parallel>  c2) (h', c')\<close>
inductive_cases opsem_iterE[elim!]: \<open>opsem r a (h, c\<^sup>\<star>) (h', c')\<close>
inductive_cases opsem_basicE[elim!]: \<open>opsem r a (h, Basic g) (h', c')\<close>
inductive_cases opsem_skipE[elim!]: \<open>opsem r a (h, Skip) (h', c')\<close>
inductive_cases opsem_envE[elim]: \<open>opsem r (Env x y) s s'\<close>

lemma opsem_tau_iff:
  \<open>opsem r Tau (h, c1 ;; c2) s' \<longleftrightarrow>
    c1 = Skip \<and> s' = (h, c2) \<or> (\<exists>h' c1'. opsem r Tau (h,c1) (h',c1') \<and> s' = (h', c1' ;; c2))\<close>
  \<open>opsem r Tau (h, c1 \<parallel> c2) s' \<longleftrightarrow>
    c1 = Skip \<and> s' = (h, c2) \<or>
    c2 = Skip \<and> s' = (h, c1) \<or>
    (\<exists>h' c1'. opsem r Tau (h,c1) (h',c1') \<and> s' = (h', c1' \<parallel> c2) \<or>
    (\<exists>h' c2'. opsem r Tau (h,c2) (h',c2') \<and> s' = (h', c1 \<parallel> c2')))\<close>
  \<open>opsem r Tau (h, c1 \<^bold>+ c2) s' \<longleftrightarrow> s' = (h, c2) \<or> s' = (h, c1)\<close>
  \<open>opsem r Tau (h, c\<^sup>\<star>) s' \<longleftrightarrow> s' = (h, c ;; c\<^sup>\<star>)\<close>
  \<open>opsem r Tau (h, Basic g) s' \<longleftrightarrow> (\<exists>h'. g h h' \<and> s' = (h', Skip))\<close>
  by (cases s', force)+

lemma opsem_envD:
  \<open>opsem r a s s' \<Longrightarrow> a = Env x y \<Longrightarrow> fst s = x \<and> fst s' = y \<and> snd s' = snd s \<and> r x y\<close>
  by (induct arbitrary: x y rule: opsem.induct) simp+

lemma opsem_env_iff:
  \<open>opsem r (Env x y) s s' \<longleftrightarrow> fst s = x \<and> fst s' = y \<and> snd s' = snd s \<and> r x y\<close>
  by (metis env opsem_envD prod.collapse)


definition \<open>passert p \<equiv> \<lambda>a b. p a\<close>
definition \<open>passume p \<equiv> \<lambda>a b. p b\<close> 

abbreviation \<open>Assert p \<equiv> Basic (passert p)\<close>
abbreviation \<open>Assume p \<equiv> Basic (passume p)\<close>

abbreviation(input) pretty_opsem :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _\<close> (\<open>_ \<midarrow>(_, _)\<rightarrow> _\<close> [60,0,60] 60) where
  \<open>hs \<midarrow>r, a\<rightarrow> ht \<equiv> opsem r a hs ht\<close>

inductive opsem_rtrancl :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _\<close> where
  base[intro!]: \<open>opsem_rtrancl r [] s s\<close>
| step[intro!]: \<open>s \<midarrow>r, a\<rightarrow> s' \<Longrightarrow> opsem_rtrancl r as s' s'' \<Longrightarrow> opsem_rtrancl r (a # as) s s''\<close>

inductive_cases opsem_rtrancl_NilE[elim!]: \<open>opsem_rtrancl r [] s s'\<close>
inductive_cases opsem_rtrancl_ConsE[elim!]: \<open>opsem_rtrancl r (a # as) s s'\<close>

lemma opsem_rtrancl_iff[simp]:
  \<open>opsem_rtrancl r [] s s' \<longleftrightarrow> s' = s\<close>
  \<open>opsem_rtrancl r (a # as) s s'' \<longleftrightarrow> (\<exists>s'. (s \<midarrow>r, a\<rightarrow> s') \<and> opsem_rtrancl r as s' s'')\<close>
  by force+

lemma opsem_rtrancl_step_rev:
  \<open>opsem_rtrancl r as s s' \<Longrightarrow> s' \<midarrow>r, a\<rightarrow> s'' \<Longrightarrow> opsem_rtrancl r (as @ [a]) s s''\<close>
  apply (induct rule: opsem_rtrancl.induct)
   apply (metis append_self_conv2 opsem_rtrancl.simps)
  apply force
  done

lemma opsem_rtrancl_step_revE:
  \<open>opsem_rtrancl r (as @ [a]) s s'' \<Longrightarrow> (\<And>s'. opsem_rtrancl r as s s' \<Longrightarrow> opsem r a s' s'' \<Longrightarrow> P) \<Longrightarrow> P\<close>
  by (induct as arbitrary: r a s s'') force+

lemma opsem_rtrancl_rev_cons_iff[simp]:
  \<open>opsem_rtrancl r (as @ [a]) s s'' \<longleftrightarrow> (\<exists>s'. opsem_rtrancl r as s s' \<and> (s' \<midarrow>r, a\<rightarrow> s''))\<close>
  by (meson opsem_rtrancl_step_rev opsem_rtrancl_step_revE)

(* TODO: infinite behaviour *)
(* TODO: actions *)
abbreviation(input) pretty_opsem_transcl :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _\<close> (\<open>_ \<midarrow>(_, _)\<rightarrow>\<^sup>\<star> _\<close> [60,0,0,60] 60) where
  \<open>hs \<midarrow>r, as\<rightarrow>\<^sup>\<star> ht \<equiv> opsem_rtrancl r as hs ht\<close>

lemma opsem_rtrancl_rev_induct:
  \<open>opsem_rtrancl r as s s' \<Longrightarrow>
    (\<And>r s. P r [] s s) \<Longrightarrow>
    (\<And>s r a s' as s''. opsem_rtrancl r as s s' \<Longrightarrow> opsem r a s' s'' \<Longrightarrow> P r as s' s'' \<Longrightarrow> P r (as @ [a]) s s'') \<Longrightarrow>
    P r as s s'\<close>
  apply (induct as arbitrary: s s' rule: rev_induct)
   apply force
  apply clarsimp
  oops


section \<open> Theorems \<close>

lemma skip_stuck:
  \<open>\<nexists>s'. (h, Skip)  \<midarrow>r, Tau\<rightarrow> s'\<close>
  by force

lemma blocked_basic_stuck:
  \<open>\<nexists>h'. g h h' \<Longrightarrow> \<nexists>s'. (h, Basic g)  \<midarrow>r, Tau\<rightarrow> s'\<close>
  by force

lemma nonskip_nonstuck:
  \<open>c \<noteq> Skip \<Longrightarrow> \<forall>x. \<exists>y. g x y \<Longrightarrow> basics_guarantee g c \<Longrightarrow> \<exists>s'. (h, c)  \<midarrow>r, Tau\<rightarrow> s'\<close>
  by (induct c arbitrary: h)
    (fastforce simp add: opsem_tau_iff)+

lemma opsem_samecD:
  \<open>opsem r a s s' \<Longrightarrow> snd s' = snd s \<Longrightarrow> r (fst s) (fst s') \<and> a = Env (fst s) (fst s')\<close>
  by (induct rule: opsem.induct) force+

lemma opsem_samec:
  \<open>opsem r a (h, c) (h', c) \<longleftrightarrow> r h h' \<and> a = Env h h'\<close>
  by (force dest: opsem_samecD)

inductive env_chain :: \<open>'h act list \<Rightarrow> 'h \<Rightarrow> 'h \<Rightarrow> bool\<close> where
  \<open>env_chain [] x x\<close>
| \<open>env_chain as x z \<Longrightarrow> env_chain (Env y x # as) y z\<close>

inductive_cases env_chain_NilE[elim!]: \<open>env_chain [] x z\<close>
inductive_cases env_chain_ConsE[elim!]: \<open>env_chain (a # as) x z\<close>

lemma env_chain_iff[simp]:
  \<open>env_chain [] x x \<longleftrightarrow> True\<close>
  \<open>env_chain (a # as) x z \<longleftrightarrow> (\<exists>y. a = Env x y \<and> env_chain as y z)\<close>
  by (force intro: env_chain.intros)+


lemma opsem_rtrancl_start_skip_all_env:
  assumes \<open>opsem_rtrancl r as (h, Skip) s'\<close>
  shows \<open>env_chain as h (fst s')\<close>
proof -
  { fix s
    have \<open>opsem_rtrancl r as s s' \<Longrightarrow> snd s = Skip \<Longrightarrow> env_chain as (fst s) (fst s')\<close>
      by (induct rule: opsem_rtrancl.induct) force+
  } then show ?thesis
    using assms
    by force
qed

lemma opsem_rtrancl_start_skip_in_rely:
  assumes
    \<open>opsem_rtrancl r as (h, Skip) s'\<close>
    \<open>reflp r\<close>
    \<open>transp r\<close>
  shows \<open>r h (fst s')\<close>
proof -
  { fix s
    have \<open>opsem_rtrancl r as s s' \<Longrightarrow> snd s = Skip \<Longrightarrow> r (fst s) (fst s')\<close>
      using assms
      apply (induct rule: opsem_rtrancl.induct)
       apply (force dest: reflpD)
      apply clarsimp
      apply (force dest: transpD)
      sorry
  } then show ?thesis
    using assms
    by force
qed


inductive rgsat
  :: \<open>('h::perm_alg) comm \<Rightarrow> ('h \<Rightarrow> 'h \<Rightarrow> bool) \<Rightarrow> ('h \<Rightarrow> 'h \<Rightarrow> bool) \<Rightarrow> ('h \<Rightarrow> bool) \<Rightarrow> ('h \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where
  rgsep_skip: \<open>rgsat Skip r g p (\<lceil> p \<rceil>\<^bsub>r\<^esub>)\<close>
| rgsep_iter: \<open>rgsat c r g p p \<Longrightarrow> rgsat (c\<^sup>\<star>) r g p p\<close>
| rgsep_ndetL:
  \<open>rgsat s1 r g1 p q1 \<Longrightarrow> rgsat s2 r g2 p q2 \<Longrightarrow> rgsat (s1 \<^bold>+ s2) r (g1 \<squnion> g2) p (q1 \<squnion> q2)\<close>
| rgsep_par:
  \<open>rgsat s1 (r \<squnion> g2) g1 p1 q1 \<Longrightarrow>
    rgsat s2 (r \<squnion> g1) g2 p2 q2 \<Longrightarrow>
    rgsat (s1 \<parallel> s2) r (g1 \<squnion> g2) (p1 \<sqinter> p2) (q1 \<sqinter> q2)\<close>
| rgsep_basic:
  \<open>passert p \<sqinter> c \<le> passume q \<Longrightarrow>
    passert p \<sqinter> c \<le> g \<Longrightarrow>
    rgsat (Basic c) r g (\<lfloor> p \<rfloor>\<^bsub>r\<^esub>) (\<lceil> q \<rceil>\<^bsub>r\<^esub>)\<close>
| rgsep_weaken:
  \<open>p \<le> p' \<Longrightarrow> q' \<le> q \<Longrightarrow> r \<le> r' \<Longrightarrow> g' \<le> g \<Longrightarrow>
    rgsat c r' g' p' q' \<Longrightarrow>
    rgsat c r g p q\<close>
| rgsep_frame:
  \<open>rgsat c r g p q \<Longrightarrow>
    rgsat c r g (p \<^emph> f) (q \<^emph> \<lceil> f \<rceil>\<^bsub>r \<squnion> g\<^esub>)\<close>

inductive_cases rgsep_skipE[elim]: \<open>rgsat Skip r g p q\<close>
inductive_cases rgsep_iterE[elim]: \<open>rgsat (c\<^sup>\<star>) r g p q\<close>
inductive_cases rgsep_parE[elim]: \<open>rgsat (s1 \<parallel> s2) r g p q\<close>
inductive_cases rgsep_basicE[elim]: \<open>rgsat (Basic c) r g p q\<close>

lemmas rgsep_weakenD = rgsep_weaken[rotated 4]

lemma backwards_frame:
  \<open>rgsat c r g p q \<Longrightarrow> rgsat c r g (p \<^emph> \<lfloor> f \<rfloor>\<^bsub>r \<squnion> g\<^esub>) (q \<^emph> f)\<close>
  oops

lemma backwards_skip:
  \<open>rgsat Skip r g (\<lfloor> p \<rfloor>\<^bsub>r\<^esub>) p\<close>
  apply (rule rgsep_weakenD[OF rgsep_skip _ _ order.refl order.refl])
  oops

lemma pre_soundness:
  \<open>rgsat c r g p q \<Longrightarrow> (h, c) \<midarrow>r, as\<rightarrow>\<^sup>\<star> (h', Skip) \<Longrightarrow> p h \<Longrightarrow> basics_guarantee g c \<Longrightarrow> q h'\<close>
  apply (induct rule: rgsat.inducts)
        apply clarsimp
        apply (frule opsem_rtrancl_start_skip_all_env)
        apply simp
  sledgehammer
  oops

end