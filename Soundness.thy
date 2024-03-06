theory Soundness
  imports RGLogic
begin

section \<open> Misc Lemmas \<close>

declare eq_OO[simp] OO_eq[simp]

lemma rtranclp_tuple_rel_semidistrib:
  \<open>(\<lambda>(a, c) (b, d). r1 a b \<and> r2 c d)\<^sup>*\<^sup>* ac bd
    \<Longrightarrow> r1\<^sup>*\<^sup>* (fst ac) (fst bd) \<and> r2\<^sup>*\<^sup>* (snd ac) (snd bd)\<close>
  by (induct rule: rtranclp_induct; force)

lemma rel_Times_rtranclp_semidistrib:
  \<open>(r1 \<times>\<^sub>R r2)\<^sup>*\<^sup>* \<le> r1\<^sup>*\<^sup>* \<times>\<^sub>R r2\<^sup>*\<^sup>*\<close>
  apply (clarsimp simp add: le_fun_def rel_Times_def)
  apply (force dest: rtranclp_tuple_rel_semidistrib)
  done

lemma rtranclp_tuple_lift_eq_left:
  \<open>r2\<^sup>*\<^sup>* c d \<Longrightarrow> (\<lambda>(a, c) (b, d). a = b \<and> r2 c d)\<^sup>*\<^sup>* (a,c) (a,d)\<close>
  by (induct rule: rtranclp_induct, fast, simp add: rtranclp.rtrancl_into_rtrancl)

lemma rtranclp_eq_eq[simp]:
  \<open>(=)\<^sup>*\<^sup>* = (=)\<close>
  by (simp add: rtransp_rel_is_rtransclp)

lemma rel_Times_left_eq_rtranclp_distrib[simp]:
  \<open>((=) \<times>\<^sub>R r2)\<^sup>*\<^sup>* = (=) \<times>\<^sub>R r2\<^sup>*\<^sup>*\<close>
  apply (rule order.antisym)
   apply (force dest: rtranclp_tuple_rel_semidistrib simp add: le_fun_def rel_Times_def)
  apply (force dest: rtranclp_tuple_lift_eq_left simp add: le_fun_def rel_Times_def)
  done

lemma rel_Times_comp[simp]:
  \<open>(a \<times>\<^sub>R b) OO (c \<times>\<^sub>R d) = (a OO c) \<times>\<^sub>R (b OO d)\<close>
  by (force simp add: fun_eq_iff OO_def)

section \<open> rely/guarantee helpers \<close>

abbreviation \<open>sswa r \<equiv> sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*)\<close>
abbreviation \<open>wssa r \<equiv> wlp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*)\<close>

lemma sp_rely_step:
  \<open>r y y' \<Longrightarrow>
    sp ((=) \<times>\<^sub>R rx) p (x, y) \<Longrightarrow>
    sp ((=) \<times>\<^sub>R (rx OO r)) p (x, y')\<close>
  by (force simp add: sp_def)

lemma sp_rely_step_rtranclp:
  \<open>r y y' \<Longrightarrow>
    sswa r p (x, y) \<Longrightarrow>
    sswa r p (x, y')\<close>
  by (simp add: sp_def, meson rtranclp.rtrancl_into_rtrancl)

lemma wlp_rely_step_rtranclp:
  \<open>r y y' \<Longrightarrow>
    wlp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) p (x, y) \<Longrightarrow>
    wlp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) p (x, y')\<close>
  by (simp add: wlp_def converse_rtranclp_into_rtranclp)

lemmas sp_rely_stronger = sp_refl_rel_le[where r=\<open>(=) \<times>\<^sub>R r\<^sup>*\<^sup>*\<close> for r, simplified]
lemmas sp_rely_absorb =
  sp_comp_rel[where ?r1.0=\<open>(=) \<times>\<^sub>R ra\<^sup>*\<^sup>*\<close> and ?r2.0=\<open>(=) \<times>\<^sub>R rb\<^sup>*\<^sup>*\<close> for ra rb, simplified]

lemma trivial_sp_rely_step[intro]:
  \<open>p x \<Longrightarrow> sswa r p x\<close>
  by (simp add: sp_refl_relI)

lemmas rely_rel_wlp_impl_sp =
  refl_rel_wlp_impl_sp[of \<open>(=) \<times>\<^sub>R r\<^sup>*\<^sup>*\<close> \<open>(=) \<times>\<^sub>R r\<^sup>*\<^sup>*\<close> for r, simplified]


lemma wlp_rely_sepconj_conj_semidistrib_mono:
  \<open>p' \<le> wlp ((=) \<times>\<^sub>R r) p \<Longrightarrow>
    q' \<le> wlp ((=) \<times>\<^sub>R r) q \<Longrightarrow>
    p' \<^emph>\<and> q' \<le> wlp ((=) \<times>\<^sub>R r) (p \<^emph>\<and> q)\<close>
  by (fastforce simp add: wlp_def sepconj_conj_def le_fun_def)

lemmas wlp_rely_sepconj_conj_semidistrib =
  wlp_rely_sepconj_conj_semidistrib_mono[OF order.refl order.refl]

lemma sp_rely_sepconj_conj_semidistrib_mono:
  \<open>sp ((=) \<times>\<^sub>R r) p \<le> p' \<Longrightarrow>
    sp ((=) \<times>\<^sub>R r) q \<le> q' \<Longrightarrow>
    sp ((=) \<times>\<^sub>R r) (p \<^emph>\<and> q) \<le> p' \<^emph>\<and> q'\<close>
  by (fastforce simp add: sp_def sepconj_conj_def le_fun_def)

lemmas sp_rely_sepconj_conj_semidistrib =
  sp_rely_sepconj_conj_semidistrib_mono[OF order.refl order.refl]

lemma wlp_rely_of_pred_Times_eq[simp]:
  \<open>wlp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) (p \<times>\<^sub>P q) = (p \<times>\<^sub>P wlp r\<^sup>*\<^sup>* q)\<close>
  by (force simp add: rel_Times_def pred_Times_def wlp_def split: prod.splits)

lemma sp_rely_of_pred_Times_eq[simp]:
  \<open>sswa r (p \<times>\<^sub>P q) = (p \<times>\<^sub>P sp r\<^sup>*\<^sup>* q)\<close>
  by (force simp add: rel_Times_def pred_Times_def sp_def split: prod.splits)


section \<open> Operational Semantics \<close>

subsection \<open> Actions \<close>

datatype act = Tau | Local

lemma act_not_eq_iff[simp]:
  \<open>a \<noteq> Tau \<longleftrightarrow> a = Local\<close>
  \<open>a \<noteq> Local \<longleftrightarrow> a = Tau\<close>
  by (meson act.distinct act.exhaust)+

subsection \<open> Operational semantics steps \<close>

fun head_atoms :: \<open>'a comm \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) set\<close> where
  \<open>head_atoms (c1 ;; c2) = (let a1 = head_atoms c1
                             in if a1 = \<bottom> then head_atoms c2 else a1)\<close>
| \<open>head_atoms (c1 \<^bold>+ c2) = (head_atoms c1 \<squnion> head_atoms c2)\<close>
| \<open>head_atoms (c1 \<box> c2) = (head_atoms c1 \<squnion> head_atoms c2)\<close>
| \<open>head_atoms (c1 \<parallel> c2) = (head_atoms c1 \<squnion> head_atoms c2)\<close>
| \<open>head_atoms (Atomic b) = {b}\<close>
| \<open>head_atoms (c\<^sup>\<star>) = head_atoms c\<close>
| \<open>head_atoms Skip = {}\<close>
| \<open>head_atoms (\<mu> c) = head_atoms c\<close>
| \<open>head_atoms (FixVar x) = \<bottom>\<close>

inductive opstep :: \<open>act \<Rightarrow> ('l \<times> 's) \<times> ('l \<times> 's) comm \<Rightarrow> (('l \<times> 's) \<times> ('l \<times> 's) comm) \<Rightarrow> bool\<close> where
  seq_left[intro!]: \<open>opstep a (h, c1) (h', c1') \<Longrightarrow> opstep a (h, c1 ;; c2) (h', c1' ;; c2)\<close>
| seq_right[intro!]: \<open>opstep Tau (h, Skip ;; c2) (h, c2)\<close>
| indet_left[intro]:  \<open>opstep a (h, c1) s' \<Longrightarrow> opstep a (h, c1 \<^bold>+ c2) s'\<close>
| indet_right[intro]: \<open>opstep a (h, c2) s' \<Longrightarrow> opstep a (h, c1 \<^bold>+ c2) s'\<close>
| endet_tau_left[intro]:  \<open>opstep Tau (h, c1) (h', c1') \<Longrightarrow> opstep Tau (h, c1 \<box> c2) (h', c1' \<box> c2)\<close>
| endet_tau_right[intro]: \<open>opstep Tau (h, c2) (h', c2') \<Longrightarrow> opstep Tau (h, c1 \<box> c2) (h', c1 \<box> c2')\<close>
| endet_skip_left[intro!]:  \<open>opstep Tau (h, Skip \<box> c2) (h, c2)\<close>
| endet_skip_right[intro!]: \<open>opstep Tau (h, c1 \<box> Skip) (h, c1)\<close>
| endet_local_left[intro]:  \<open>a \<noteq> Tau \<Longrightarrow> opstep a (h, c1) s' \<Longrightarrow> opstep a (h, c1 \<box> c2) s'\<close>
| endet_local_right[intro]: \<open>a \<noteq> Tau \<Longrightarrow> opstep a (h, c2) s' \<Longrightarrow> opstep a (h, c1 \<box> c2) s'\<close>
| par_left[intro]: \<open>opstep a (h, s) (h', s') \<Longrightarrow> opstep a (h, s \<parallel> t) (h', s' \<parallel> t)\<close>
| par_right[intro]: \<open>opstep a (h, t) (h', t') \<Longrightarrow> opstep a (h, s \<parallel> t) (h', s \<parallel> t')\<close>
| par_skip[intro!]: \<open>opstep Tau (h, Skip \<parallel> Skip) (h, Skip)\<close>
| iter_step[intro]: \<open>opstep a (h, c) (h', c') \<Longrightarrow> opstep a (h, c\<^sup>\<star>) (h, c' ;; c\<^sup>\<star>)\<close>
| iter_end[intro]: \<open>\<not> pre_state (\<Squnion>(head_atoms c)) h \<Longrightarrow> opstep a (h, c\<^sup>\<star>) (h, Skip)\<close>
| fixpt_skip[intro!]: \<open>c' = c[0 \<leftarrow> \<mu> c] \<Longrightarrow> opstep Tau (h, \<mu> c) (h, c')\<close>
| atomic[intro!]: \<open>a = Local \<Longrightarrow> snd s' = Skip \<Longrightarrow> b h (fst s') \<Longrightarrow> opstep a (h, Atomic b) s'\<close>

inductive_cases opstep_tauE[elim]: \<open>opstep Tau s s'\<close>
inductive_cases opstep_localE[elim]: \<open>opstep Local s s'\<close>

inductive_cases opstep_skipE[elim!]: \<open>opstep a (h, Skip) s'\<close>
inductive_cases opstep_seqE[elim]: \<open>opstep a (h, c1 ;; c2) s'\<close>
inductive_cases opstep_indetE[elim]: \<open>opstep a (h, c1 \<^bold>+ c2) s'\<close>
inductive_cases opstep_endetE[elim]: \<open>opstep a (h, c1 \<box> c2) s'\<close>
inductive_cases opstep_parE[elim]: \<open>opstep a (h, c1 \<parallel> c2) s'\<close>
inductive_cases opstep_fixptE[elim]: \<open>opstep a (h, \<mu> c) s'\<close>
inductive_cases opstep_atomicE[elim!]: \<open>opstep a (h, Atomic b) s'\<close>

paragraph \<open> Pretty operational semantics \<close>

abbreviation(input) pretty_opstep :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _\<close> (\<open>_ \<midarrow>(_)\<rightarrow> _\<close> [60,0,60] 60) where
  \<open>hs \<midarrow>a\<rightarrow> ht \<equiv> opstep a hs ht\<close>


subsection \<open> Lemmas about opstep \<close>

named_theorems opstep_iff

lemma opstep_iff_standard[opstep_iff]:
  \<open>opstep a (h, Skip) s' \<longleftrightarrow> False\<close>
  \<open>opstep a (h, c1 ;; c2) s' \<longleftrightarrow>
    a = Tau \<and> c1 = Skip \<and> s' = (h, c2) \<or>
    (\<exists>h' c1'. opstep a (h,c1) (h',c1') \<and> s' = (h', c1' ;; c2))\<close>
  \<open>opstep a (h, c1 \<^bold>+ c2) s' \<longleftrightarrow>
    opstep a (h, c1) s' \<or> opstep a (h, c2) s'\<close>
  \<open>opstep a (h, c1 \<box> c2) s' \<longleftrightarrow>
    a = Local \<and> opstep Local (h, c1) s' \<or>
    a = Local \<and> opstep Local (h, c2) s' \<or>
    a = Tau \<and> (\<exists>h' c1'. s' = (h', c1' \<box> c2) \<and> opstep Tau (h, c1) (h', c1')) \<or>
    a = Tau \<and> (\<exists>h' c2'. s' = (h', c1 \<box> c2') \<and> opstep Tau (h, c2) (h', c2')) \<or>
    a = Tau \<and> c1 = Skip \<and> s' = (h, c2) \<or>
    a = Tau \<and> c2 = Skip \<and> s' = (h, c1)\<close>
  \<open>opstep a (h, c1 \<parallel> c2) s' \<longleftrightarrow>
    a = Tau \<and> c1 = Skip \<and> c2 = Skip \<and> s' = (h, Skip) \<or>
    (\<exists>h' c1'. opstep a (h,c1) (h',c1') \<and> s' = (h', c1' \<parallel> c2)) \<or>
    (\<exists>h' c2'. opstep a (h,c2) (h',c2') \<and> s' = (h', c1 \<parallel> c2'))\<close>
  \<open>opstep a (h, \<mu> c) s' \<longleftrightarrow> a = Tau \<and> s' = (h, c[0 \<leftarrow> \<mu> c])\<close>
  \<open>opstep a (h, Atomic b) s' \<longleftrightarrow>
    a = Local \<and> snd s' = Skip \<and> b h (fst s')\<close>
        apply blast
       apply blast
      apply blast
     apply (rule iffI, (erule opstep_endetE; force), force)
    apply blast
   apply blast
  apply blast
  done

lemma opstep_tau_preserves_heap:
  assumes \<open>s \<midarrow>Tau\<rightarrow> s'\<close>
  shows \<open>fst s' = fst s\<close>
proof -
  { fix a
    have \<open>s \<midarrow>a\<rightarrow> s' \<Longrightarrow> a = Tau \<Longrightarrow> fst s' = fst s\<close>
      by (induct rule: opstep.inducts) force+
  }
  then show ?thesis
    using assms by force
qed

lemma opstep_act_cases:
  \<open>s \<midarrow>a\<rightarrow> s' \<Longrightarrow>
    (a = Tau \<Longrightarrow> s \<midarrow>Tau\<rightarrow> s' \<Longrightarrow> fst s' = fst s \<Longrightarrow> P) \<Longrightarrow>
    (a = Local \<Longrightarrow> s \<midarrow>Local\<rightarrow> s' \<Longrightarrow> P) \<Longrightarrow>
    P\<close>
  by (metis (full_types) act.exhaust opstep_tau_preserves_heap)

lemma all_atom_comm_opstep:
  assumes
    \<open>opstep a (h, c) (h', c')\<close>
    \<open>all_atom_comm p c\<close>
  shows
    \<open>all_atom_comm p c'\<close>
proof -
  { fix s s'
    assume \<open>opstep a s s'\<close>
      and \<open>all_atom_comm p (snd s)\<close>
    then have \<open>all_atom_comm p (snd s')\<close>
      by (induct rule: opstep.inducts) force+
  }
  then show ?thesis
    using assms
    by (metis snd_conv)
qed

lemmas all_atom_comm_opstepD =
  all_atom_comm_opstep[rotated]


subsubsection \<open> adding parallel \<close>

lemma opstep_parallel_leftD:
  \<open>s \<midarrow>a\<rightarrow> s' \<Longrightarrow> (fst s, snd s \<parallel> cy) \<midarrow>a\<rightarrow> (fst s', snd s' \<parallel> cy)\<close>
  by (simp add: par_left)

lemma opstep_parallel_rightD:
  \<open>s \<midarrow>a\<rightarrow> s' \<Longrightarrow> (fst s, cx \<parallel> snd s) \<midarrow>a\<rightarrow> (fst s', cx \<parallel> snd s')\<close>
  by (simp add: par_right)


subsubsection \<open> iteraction with all_atom_comm \<close>

lemma opstep_preserves_all_atom_comm:
  assumes
    \<open>opstep a (h, c) (h', c')\<close>
    \<open>all_atom_comm p c\<close>
  shows \<open>all_atom_comm p c'\<close>
proof -
  { fix s s'
    have \<open>opstep a s s' \<Longrightarrow> all_atom_comm p (snd s) \<Longrightarrow> all_atom_comm p (snd s')\<close>
      by (induct arbitrary: h' rule: opstep.inducts) force+
  }
  then show ?thesis
    using assms
    by (metis snd_conv)
qed

lemmas rev_opstep_preserves_all_atom_comm = opstep_preserves_all_atom_comm[rotated]


subsection \<open> Sugared atomic programs \<close>

definition \<open>passert p \<equiv> \<lambda>a b. p a \<and> a = b\<close>

abbreviation \<open>Assert p \<equiv> Atomic (passert p)\<close>
abbreviation \<open>Assume p \<equiv> Atomic (\<lambda>a. p)\<close>

lemmas Assert_def = arg_cong[where f=Atomic, OF meta_eq_to_obj_eq[OF passert_def]]

lemma passert_simps[simp]:
  \<open>passert p a b \<longleftrightarrow> p a \<and> b = a\<close>
  by (force simp add: passert_def)

lemma opstep_assert[intro!]: \<open>p h \<Longrightarrow> opstep Local (h, Assert p) (h, Skip)\<close>
  by (force simp add: opstep.atomic passert_def)

lemma opstep_assume[intro!]: \<open>q h' \<Longrightarrow> opstep Local (h, Assume q) (h', Skip)\<close>
  by (force simp add: opstep.atomic rel_liftR_def)

subsection \<open> If-then-else and While Loops \<close>

definition \<open>IfThenElse p ct cf \<equiv> Assert p ;; ct \<box> Assert (-p) ;; cf\<close>
definition \<open>WhileLoop p c \<equiv> \<mu> (Assert p ;; map_fixvar Suc c ;; FixVar 0 \<box> Assert (-p))\<close>

lemma IfThenElse_inject[simp]:
  \<open>IfThenElse p1 ct1 cf1 = IfThenElse p2 ct2 cf2 \<longleftrightarrow> p1 = p2 \<and> ct1 = ct2 \<and> cf1 = cf2\<close>
  by (simp add: IfThenElse_def passert_def fun_eq_iff, blast)

lemma WhileLoop_inject[simp]:
  \<open>WhileLoop p1 c1 = WhileLoop p2 c2 \<longleftrightarrow> p1 = p2 \<and> c1 = c2\<close>
  by (simp add: WhileLoop_def map_fixvar_inj_inject passert_def fun_eq_iff, blast)

lemma IfThenElse_distinct[simp]:
  \<open>IfThenElse p ct cf \<noteq> Skip\<close>
  \<open>IfThenElse p ct cf \<noteq> c1 ;; c2\<close>
  \<open>IfThenElse p ct cf \<noteq> c1 \<parallel> c2\<close>
  \<open>IfThenElse p ct cf \<noteq> \<mu> c\<close>
  \<open>IfThenElse p ct cf \<noteq> Atomic b\<close>
  \<open>Skip \<noteq> IfThenElse p ct cf\<close>
  \<open>c1 ;; c2 \<noteq> IfThenElse p ct cf\<close>
  \<open>c1 \<parallel> c2 \<noteq> IfThenElse p ct cf\<close>
  \<open>\<mu> c \<noteq> IfThenElse p ct cf\<close>
  \<open>Atomic b \<noteq> IfThenElse p ct cf\<close>
  by (simp add: IfThenElse_def)+

lemma WhileLoop_distinct[simp]:
  \<open>WhileLoop p c \<noteq> Skip\<close>
  \<open>WhileLoop p c \<noteq> c1 \<box> c2\<close>
  \<open>WhileLoop p c \<noteq> c1 \<parallel> c2\<close>
  \<open>WhileLoop p c \<noteq> Atomic b\<close>
  \<open>Skip \<noteq> WhileLoop p c\<close>
  \<open>c1 \<box> c2 \<noteq> WhileLoop p c\<close>
  \<open>c1 \<parallel> c2 \<noteq> WhileLoop p c\<close>
  \<open>Atomic b \<noteq> WhileLoop p c\<close>
  \<open>WhileLoop p c \<noteq> \<mu> c\<close>
  \<open>\<mu> c \<noteq> WhileLoop p c\<close>
           apply (simp add: WhileLoop_def; fail)+
   apply (rule size_neq_size_imp_neq, simp add: WhileLoop_def)+
  done


lemma opstep_IfThenElse_iff[opstep_iff]:
  \<open>opstep a (h, IfThenElse p ct cf) s' \<longleftrightarrow>
    a = Local \<and> p h \<and> s' = (h, Skip ;; ct) \<or> a = Local \<and> \<not> p h \<and> s' = (h, Skip ;; cf)\<close>
  by (simp add: IfThenElse_def opstep_iff)

lemma opstep_IfThenElse_true[intro]:
  \<open>p h \<Longrightarrow> opstep Local (h, IfThenElse p a b) (h, Skip ;; a)\<close>
  by (simp add: opstep_iff)

lemma opstep_IfThenElse_false[intro]:
  \<open>\<not> p h \<Longrightarrow> opstep Local (h, IfThenElse p a b) (h, Skip ;; b)\<close>
  by (simp add: opstep_iff)

lemma opstep_WhileLoop_iff[opstep_iff]:
  \<open>opstep a (h, WhileLoop p c) s' \<longleftrightarrow>
    a = Tau \<and> s' = (h, Assert p ;; map_fixvar Suc c ;; WhileLoop p c \<box> Assert (- p))\<close>
  by (simp add: WhileLoop_def opstep_iff fixvar_subst_over_map_avoid)


section \<open> Safe \<close>

inductive safe
  :: \<open>nat \<Rightarrow> ('l::perm_alg \<times> 's::perm_alg) comm \<Rightarrow>
      'l \<Rightarrow> 's \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('l \<times> 's \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where
  safe_nil[intro!]: \<open>safe 0 c hl hs r g q\<close>
| safe_suc[intro]:
  \<open>\<comment> \<open> if the command is Skip, the postcondition is established \<close>
    \<comment> \<open> TODO: This requires termination is represented as infinite stuttering past the end.
               We may want a different model, but that would be more complicated. \<close>
    (c = Skip \<longrightarrow> q (hl, hs)) \<Longrightarrow>
    \<comment> \<open> rely steps are safe \<close>
    (\<And>hs'. r hs hs' \<Longrightarrow> safe n c hl hs' r g q) \<Longrightarrow>
    \<comment> \<open> opsteps are safe \<close>
    (\<And>a c' hx'.
        ((hl, hs), c) \<midarrow>a\<rightarrow> (hx', c') \<Longrightarrow>
        (a = Local \<longrightarrow> g hs (snd hx')) \<and>
        safe n c' (fst hx') (snd hx') r g q) \<Longrightarrow>
    \<comment> \<open> opsteps are frame closed and establish the guarantee \<close>
    (\<And>a c' hlf hx'.
        ((hl + hlf, hs), c) \<midarrow>a\<rightarrow> (hx', c') \<Longrightarrow>
        hl ## hlf \<Longrightarrow>
        (a = Local \<longrightarrow> g hs (snd hx')) \<and>
        (\<exists>hl'.
          hl' ## hlf \<and> fst hx' = hl' + hlf \<and>
          (a = Tau \<longrightarrow> hl' = hl) \<and>
          safe n c' hl' (snd hx') r g q)) \<Longrightarrow>
    \<comment> \<open> conclude a step can be made \<close>
    safe (Suc n) c hl hs r g q\<close>

subsection \<open> Proofs about safe \<close>

inductive_cases safe_zeroE[elim!]: \<open>safe 0 c hl hs r g q\<close>
inductive_cases safe_sucE[elim]: \<open>safe (Suc n) c hl hs r g q\<close>

lemma safe_nil_iff[simp]:
  \<open>safe 0 c hl hs r g q \<longleftrightarrow> True\<close>
  by force

lemma safe_suc_iff:
  \<open>safe (Suc n) c hl hs r g q \<longleftrightarrow>
    (c = Skip \<longrightarrow> q (hl, hs)) \<and>
    (\<forall>hs'. r hs hs' \<longrightarrow> safe n c hl hs' r g q) \<and>
    (\<forall>a c' hx'.
        ((hl, hs), c) \<midarrow>a\<rightarrow> (hx', c') \<longrightarrow>
        (a = Local \<longrightarrow> g hs (snd hx')) \<and>
        safe n c' (fst hx') (snd hx') r g q) \<and>
    (\<forall>a c' hlf hx'.
        ((hl + hlf, hs), c) \<midarrow>a\<rightarrow> (hx', c') \<longrightarrow>
        hl ## hlf \<longrightarrow>
        (a = Local \<longrightarrow> g hs (snd hx')) \<and>
        (\<exists>hl'.
          hl' ## hlf \<and> fst hx' = hl' + hlf \<and>
          (a = Tau \<longrightarrow> hl' = hl) \<and>
          safe n c' hl' (snd hx') r g q))\<close>
  apply (rule iffI)
   apply (erule safe_sucE, (simp; fail))
  apply (rule safe_suc; presburger)
  done

lemma safe_sucD:
  \<open>safe (Suc n) c hl hs r g q \<Longrightarrow> c = Skip \<Longrightarrow> q (hl, hs)\<close>
  \<open>safe (Suc n) c hl hs r g q \<Longrightarrow> r hs hs' \<Longrightarrow> safe n c hl hs' r g q\<close>
  \<open>safe (Suc n) c hl hs r g q \<Longrightarrow> ((hl, hs), c) \<midarrow>a\<rightarrow> (hx', c') \<Longrightarrow> safe n c' (fst hx') (snd hx') r g q\<close>
  \<open>safe (Suc n) c hl hs r g q \<Longrightarrow> ((hl, hs), c) \<midarrow>Local\<rightarrow> (hx', c') \<Longrightarrow> g hs (snd hx')\<close>
  \<open>safe (Suc n) c hl hs r g q \<Longrightarrow>
      ((hl + hlf, hs), c) \<midarrow>a\<rightarrow> (hx', c') \<Longrightarrow>
      hl ## hlf \<Longrightarrow>
      (a = Local \<longrightarrow> g hs (snd hx')) \<and>
      (\<exists>hl'.
        hl' ## hlf \<and> fst hx' = hl' + hlf \<and>
        (a = Tau \<longrightarrow> hl' = hl) \<and>
        safe n c' hl' (snd hx') r g q)\<close>
  by (erule safe_sucE, simp; fail)+


subsubsection \<open> Monotonicity of safe \<close>

lemma safe_postpred_monoD:
  \<open>safe n c hl hs r g q \<Longrightarrow> q \<le> q' \<Longrightarrow> safe n c hl hs r g q'\<close>
  apply (induct rule: safe.induct)
   apply blast
  apply (rule safe_suc)
      apply (clarsimp simp add: le_fun_def; fail)+
  apply metis
  done

lemmas safe_postpred_mono = safe_postpred_monoD[rotated]

lemma safe_guarantee_monoD:
  \<open>safe n c hl hs r g q \<Longrightarrow> g \<le> g' \<Longrightarrow> safe n c hl hs r g' q\<close>
proof (induct rule: safe.induct)
  case safe_nil
  then show ?case by blast
next
  case (safe_suc c q hl hs r n g)
  show ?case
    using safe_suc.prems
    apply -
    apply (rule safe.safe_suc)
       apply (simp add: safe_suc.hyps; fail)
      apply (blast intro: safe_suc.hyps)
     apply (metis predicate2D safe_suc.hyps(4))
    apply (simp add: le_fun_def, fast dest: safe_suc.hyps(5))
    done
qed

lemmas safe_guarantee_mono = safe_guarantee_monoD[rotated]

lemma safe_rely_antimonoD:
  \<open>safe n c hl hs r g q \<Longrightarrow> r' \<le> r \<Longrightarrow> safe n c hl hs r' g q\<close>
  apply (induct rule: safe.induct)
   apply force
  apply (rule safe_suc)
        apply presburger
       apply (metis predicate2D)
    apply presburger+
  apply metis
  done

lemmas safe_rely_antimono = safe_rely_antimonoD[rotated]

lemma safe_step_monoD:
  \<open>safe n c hl hs r g q \<Longrightarrow> m \<le> n \<Longrightarrow> safe m c hl hs r g q\<close>
  apply (induct arbitrary: m rule: safe.inducts)
   apply force
  apply (clarsimp simp add: le_Suc_iff0)
  apply (erule disjE, fast)
  apply clarsimp
  apply (rule safe_suc)
        apply (clarsimp; metis)+
  done


subsection \<open> Safety of Skip \<close>

lemma safe_skip':
  \<open>sswa r q (hl, hs) \<Longrightarrow> safe n Skip hl hs r g (sswa r q)\<close>
  apply (induct n arbitrary: hl hs q)
   apply force
  apply (rule safe_suc)
        apply blast
       apply (simp add: weak_framed_subresource_rel_def all_conj_distrib sp_def)
       apply (meson opstep_skipE rtranclp.rtrancl_into_rtrancl; fail)
      apply blast+
  done

lemma safe_skip:
  \<open>p (hl, hs) \<Longrightarrow> sswa r p \<le> q \<Longrightarrow> safe n Skip hl hs r g q\<close>
  apply (rule safe_postpred_monoD[OF safe_skip'[where q=p]])
   apply (metis (mono_tags, lifting) rel_Times_iff rtranclp.rtrancl_refl sp_def)
  apply blast
  done


subsection \<open> Safety of Atomic \<close>

lemma safe_atom':
  \<open>sp b (wlp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) p) \<le> sswa r q \<Longrightarrow>
    \<forall>f. sp b (wlp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) (p \<^emph>\<and> f)) \<le> sswa r (q \<^emph>\<and> f) \<Longrightarrow>
    b \<le> \<top> \<times>\<^sub>R g \<Longrightarrow>
    wlp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) p (hl, hs) \<Longrightarrow>
    safe n (Atomic b) hl hs r g (sswa r q)\<close>
proof (induct n arbitrary: hl hs)
  case 0
  then show ?case by force
next
  case (Suc n)
  show ?case
    using Suc.prems
    apply (intro safe.safe_suc)
      (* subgoal: skip *)
          apply force
      (* subgoal: rely *)
         apply (rule Suc.hyps; force simp add: wlp_rely_step_rtranclp)
      (* subgoal: plain opstep *)
     apply (simp add: opstep_iff del: top_apply sup_apply)
     apply (rule conjI)
      apply (metis predicate2D prod.collapse rel_Times_iff)
     apply (rule safe_skip[where p=\<open>sswa r q\<close>])
      apply (simp del: sup_apply, blast)
     apply (force simp add: sp_rely_absorb)
      (* subgoal: local framed opstep *)
    apply (clarsimp simp add: opstep_iff sp_def[of b] imp_ex_conjL le_fun_def simp del: sup_apply)
    apply (drule_tac x=\<open>(=) hlf \<times>\<^sub>P \<top>\<close> in spec, drule spec2, drule spec2, drule mp, fast, drule mp,
        rule predicate1D[OF wlp_rely_sepconj_conj_semidistrib])
     apply (rule sepconj_conjI; force)
    apply (drule predicate1D[OF sp_rely_sepconj_conj_semidistrib])
    apply (clarsimp simp add: sepconj_conj_def)
    apply (metis safe_skip')
    done
qed

lemma safe_atom:
  \<open>sp b (wssa r p) \<le> sswa r q \<Longrightarrow>
    \<forall>f. sp b (wssa r (p \<^emph>\<and> f)) \<le> sswa r (q \<^emph>\<and> f) \<Longrightarrow>
    b \<le> \<top> \<times>\<^sub>R g \<Longrightarrow>
    wssa r p (hl, hs) \<Longrightarrow>
    sswa r q \<le> q' \<Longrightarrow>
    safe n (Atomic b) hl hs r g q'\<close>
  by (meson safe_postpred_mono safe_atom')


subsection \<open> Safety of Sequencing \<close>

lemma safe_seq_assoc_left:
  \<open>safe n c hl hs r g q \<Longrightarrow>
    c = (c1 ;; c2 ;; c3) \<Longrightarrow>
    safe n ((c1 ;; c2) ;; c3) hl hs r g q\<close>
  apply (induct arbitrary: c1 c2 c3 rule: safe.inducts)
   apply force
  apply (rule safe_suc)
     apply blast
    apply blast
   apply (clarsimp simp add: opstep_iff, metis)+
  done

lemma safe_seq_assoc_right:
  \<open>safe n c hl hs r g q \<Longrightarrow>
    c = ((c1 ;; c2) ;; c3) \<Longrightarrow>
    safe n (c1 ;; c2 ;; c3) hl hs r g q\<close>
  apply (induct arbitrary: c1 c2 c3 rule: safe.inducts)
   apply force
  apply (rule safe_suc)
     apply blast
    apply blast
   apply (clarsimp simp add: opstep_iff, metis)+
  done

lemma safe_seq':
  \<open>safe n c1 hl hs r g q \<Longrightarrow>
    (\<forall>m\<le>n. \<forall>hl' hs'. q (hl', hs') \<longrightarrow> safe m c2 hl' hs' r g q') \<Longrightarrow>
    safe n (c1 ;; c2) hl hs r g q'\<close>
proof (induct arbitrary: c2 q' rule: safe.inducts)
  case (safe_suc c q hl hs r n g)

  have safe_c2:
    \<open>\<And>m hl' hs'. m \<le> n \<Longrightarrow> q (hl', hs') \<Longrightarrow> safe m c2 hl' hs' r g q'\<close>
    \<open>\<And>hl' hs'. q (hl', hs') \<Longrightarrow> safe (Suc n) c2 hl' hs' r g q'\<close>
    using safe_suc.prems
    by force+
  then show ?case
    using safe_suc.prems(1) safe_suc.hyps(1)
    apply -
    apply (rule safe.safe_suc)
       apply force
      (* subgoal: rely *)
      apply (simp add: safe_suc.hyps(3); fail)
      (* subgoal: plain opstep *)
     apply (clarsimp simp add: opstep_iff simp del: sup_apply)
     apply (elim disjE conjE exE)
      apply (force dest: reflp_onD)
     apply (frule safe_suc.hyps(4))
     apply (clarsimp simp del: sup_apply)
      (* subgoal: local framed opstep *)
    apply (clarsimp simp add: opstep_iff simp del: sup_apply)
    apply (erule disjE, force)
    apply (clarsimp simp del: sup_apply)
    apply (metis safe_c2(1) safe_suc.hyps(5) fst_conv snd_conv)
    done
qed force


lemma safe_seq:
  \<open>safe n c1 hl hs r g q \<Longrightarrow>
    (\<forall>hl' hs'. q (hl', hs') \<longrightarrow> safe n c2 hl' hs' r g q') \<Longrightarrow>
    safe n (c1 ;; c2) hl hs r g q'\<close>
  by (force intro: safe_seq' safe_step_monoD)


subsection \<open> Safety of Fixpoint \<close>

(*
lemma safe_fixpt':
  \<open>(\<forall>m<n. \<forall>hl' hs'.
      safe m (\<mu> c) hl hs r g (sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>* ) i (hl', hs')) \<longrightarrow>
      sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>* ) i (hl', hs') \<longrightarrow>
      safe n c[0 \<leftarrow> \<mu> c] hl' hs' r g (sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>* ) i)) \<Longrightarrow>
    sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>* ) i (hl, hs) \<Longrightarrow>
    safe n (\<mu> c) hl hs r g (sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>* ) i)\<close>
proof (induct n arbitrary: i hl hs)
  case (Suc n)
  show ?case
    using Suc.prems
    apply -
    apply (rule safe.safe_suc)
       apply blast
      (* subgoal: rely *)
      apply (rule Suc.hyps)
       apply force
      apply (force intro: sp_rely_step_rtranclp)
      (* subgoal: plain opstep *)
     apply (clarsimp simp add: le_Suc_eq all_conj_distrib opstep_iff reflp_onD; fail)
      (* subgoal: locally framed opstep *)
    apply (clarsimp simp add: le_Suc_eq all_conj_distrib opstep_iff reflp_onD simp del: sup_apply)
    apply blast
    done
qed force


lemma safe_fixpt:
  \<open>(\<And>n hl hs. p' (hl, hs) \<Longrightarrow> safe n c[0 \<leftarrow> \<mu> c] hl hs r g q') \<Longrightarrow>
    p \<le> i \<Longrightarrow>
    sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>* ) i \<le> p' \<Longrightarrow>
    q' \<le> i \<Longrightarrow>
    sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>* ) i \<le> q \<Longrightarrow>
    p (hl, hs) \<Longrightarrow>
    safe n (\<mu> c) hl hs r g q\<close>
  apply (rule safe_postpred_mono, assumption)
  apply (rule safe_fixpt')
   apply (metis (mono_tags) predicate1D safe_postpred_monoD sp_rely_stronger)
  apply blast
  done
*)


subsubsection \<open> Safety of internal nondeterminism \<close>

lemma safe_indet:
    \<open>safe n c1 hl hs r g q \<Longrightarrow>
      safe n c2 hl hs r g q \<Longrightarrow>
      safe n (c1 \<^bold>+ c2) hl hs r g q\<close>
proof (induct n arbitrary: c1 c2 hl hs)
  case 0
  then show ?case by blast
next
  case (Suc n)

  have safeSuc:
    \<open>safe (Suc n) c1 hl hs r g q\<close>
    \<open>safe (Suc n) c2 hl hs r g q\<close>
    using Suc.prems
    by simp+
  note safe_suc1 = safe_sucD[OF safeSuc(1)]
  note safe_suc2 = safe_sucD[OF safeSuc(2)]

  have
    \<open>\<forall>m\<le>n. safe m c1 hl hs r g q\<close>
    \<open>\<forall>m\<le>n. safe m c2 hl hs r g q\<close>
    using Suc.prems
    by (meson le_SucI safe_step_monoD)+
  then show ?case
    apply -
    apply (rule safe_suc)
       apply blast
      (* subgoal: rely *)
      apply (metis Suc.hyps safe_suc1(2) safe_suc2(2))
      (* subgoal: plain opstep *)
     apply (clarsimp simp add: opstep_iff simp del: sup_apply)
     apply (elim disjE conjE exE)
      apply (force dest: safe_suc1(3,4))
     apply (force dest: safe_suc2(3,4))
      (* subgoal: local frame opstep *)
    apply (clarsimp simp add: opstep_iff simp del: sup_apply)
    apply (elim disjE conjE exE)
     apply (erule opstep_act_cases; metis safe_suc1(5) fst_conv snd_conv)
    apply (erule opstep_act_cases; metis safe_suc2(5) fst_conv snd_conv)
    done
qed


subsubsection \<open> Safety of external nondeterminism \<close>

lemma safe_endet:
    \<open>safe n c1 hl hs r g q \<Longrightarrow>
      safe n c2 hl hs r g q \<Longrightarrow>
      safe n (c1 \<box> c2) hl hs r g q\<close>
proof (induct n arbitrary: c1 c2 hl hs)
  case 0
  then show ?case by blast
next
  case (Suc n)

  have safeSuc:
    \<open>safe (Suc n) c1 hl hs r g q\<close>
    \<open>safe (Suc n) c2 hl hs r g q\<close>
    using Suc.prems
    by simp+
  note safe_suc1 = safe_sucD[OF safeSuc(1)]
  note safe_suc2 = safe_sucD[OF safeSuc(2)]

  have
    \<open>\<forall>m\<le>n. safe m c1 hl hs r g q\<close>
    \<open>\<forall>m\<le>n. safe m c2 hl hs r g q\<close>
    using Suc.prems
    by (meson le_SucI safe_step_monoD)+
  then show ?case
    apply -
    apply (rule safe_suc)
       apply blast
      (* subgoal: rely *)
      apply (metis Suc.hyps safe_suc1(2) safe_suc2(2))
      (* subgoal: plain opstep *)
     apply (clarsimp simp add: opstep_iff simp del: sup_apply)
     apply (elim disjE conjE exE)
          apply (force dest: safe_suc1(3,4))
         apply (force dest: safe_suc2(3,4))
        apply (frule opstep_tau_preserves_heap, clarsimp)
        apply (fastforce intro: Suc.hyps dest: safe_suc1(3))
       apply (frule opstep_tau_preserves_heap, clarsimp)
       apply (fastforce intro: Suc.hyps dest: safe_suc2(3))
      apply blast
     apply blast
      (* subgoal: local frame opstep *)
    apply (clarsimp simp add: opstep_iff simp del: sup_apply)
    apply (elim disjE conjE exE)
         apply (erule opstep_act_cases; metis safe_suc1(5) fst_conv snd_conv)
        apply (erule opstep_act_cases; metis safe_suc2(5) fst_conv snd_conv)
      (* subsubgoal: left tau passthrough *)
       apply (frule safe_suc1(5), blast)
       apply clarsimp
       apply (frule opstep_tau_preserves_heap)
       apply (clarsimp simp del: sup_apply)
       apply (metis Suc.hyps order.refl)
      (* subsubgoal: right tau passthrough *)
      apply (frule safe_suc2(5), blast)
      apply clarsimp
      apply (frule opstep_tau_preserves_heap)
      apply (clarsimp simp del: sup_apply)
      apply (metis Suc.hyps order.refl)
      (* subsubgoal: right skip tau *)
     apply blast
      (* subsubgoal: left skip tau *)
    apply blast
    done
qed


subsection \<open> Safety of frame \<close>

lemma safe_frame':
  \<open>safe n c hl hs r g q \<Longrightarrow>
    hl ## hlf \<Longrightarrow>
    sp ((=) \<times>\<^sub>R (r \<squnion> g)\<^sup>*\<^sup>*) f (hlf, hs) \<Longrightarrow>
    safe n c (hl + hlf) hs r g (q \<^emph>\<and> sp ((=) \<times>\<^sub>R (r \<squnion> g)\<^sup>*\<^sup>*) f)\<close>
proof (induct arbitrary: hlf rule: safe.induct)
  case (safe_nil c hl hs r g q)
  then show ?case by blast
next
  case (safe_suc c q hl hs r n g)

  show ?case
    using safe_suc.prems
    apply -
    apply (rule safe.safe_suc)
      (* subgoal: skip *)
       apply (clarsimp simp add: sepconj_conj_def simp del: sup_apply)
       apply (drule mp[OF safe_suc.hyps(1)])
       apply blast
      (* subgoal: rely step *)
      apply (metis safe_suc.hyps(3) sup2I1 sp_rely_step_rtranclp)
      (* subgoal: plain opstep *)
     apply (frule safe_suc.hyps(5), blast)
     apply (clarsimp simp del: sup_apply top_apply)
     apply (metis fst_conv opstep_act_cases snd_eqD sp_rely_step_rtranclp sup2I2)
      (* subgoal: local framed opstep *)
    apply (clarsimp simp add: partial_add_assoc2[of hl hlf] simp del: sup_apply top_apply)
    apply (rename_tac hlf2 hl'hlfhlf2 hs')
    apply (frule safe_suc.hyps(5), metis disjoint_add_swap_lr)
    apply (clarsimp simp del: sup_apply top_apply)
    apply (intro exI conjI)
       prefer 2 (* instantiating a schematic *)
       apply (rule partial_add_assoc[symmetric])
         apply (metis disjoint_add_leftR disjoint_add_rightL)
        apply (metis disjoint_add_leftR)
       apply (metis disjoint_add_leftR disjoint_add_rightR)
      apply (metis disjoint_add_leftR disjoint_add_swap_rl)
     apply blast
    apply (metis disjoint_add_leftR disjoint_add_rightL fst_eqD opstep_act_cases snd_eqD
        sp_rely_step_rtranclp sup2I2)
    done
qed

lemma safe_frame:
  \<open>safe n c hl hs r g q \<Longrightarrow>
    hl ## hlf \<Longrightarrow>
    f (hlf, hs) \<Longrightarrow>
    sp ((=) \<times>\<^sub>R (r \<squnion> g)\<^sup>*\<^sup>*) f \<le> f' \<Longrightarrow>
    safe n c (hl + hlf) hs r g (q \<^emph>\<and> f')\<close>
  apply (rule safe_postpred_monoD)
   apply (rule safe_frame'[where f=f]; blast)
  apply (blast dest: sepconj_conj_monoR)
  done


subsection \<open> Safety of parallel \<close>

lemma safe_parallel':
  \<open>safe n c1 hl1 hs (r \<squnion> g2) g1 (sp ((=) \<times>\<^sub>R (r \<squnion> g2)\<^sup>*\<^sup>*) q1) \<Longrightarrow>
    safe n c2 hl2 hs (r \<squnion> g1) g2 (sp ((=) \<times>\<^sub>R (r \<squnion> g1)\<^sup>*\<^sup>*) q2) \<Longrightarrow>
    hl1 ## hl2 \<Longrightarrow>
    safe n (c1 \<parallel> c2) (hl1 + hl2) hs r (g1 \<squnion> g2)
      ((sp ((=) \<times>\<^sub>R (r \<squnion> g2)\<^sup>*\<^sup>*) q1) \<^emph>\<and> (sp ((=) \<times>\<^sub>R (r \<squnion> g1)\<^sup>*\<^sup>*) q2))\<close>
proof (induct n arbitrary: c1 c2 hl1 hl2 hs)
  case 0
  then show ?case by force
next
  case (Suc n)

  note safe_suc1 = safe_sucD[OF Suc.prems(1)]
  note safe_suc2 = safe_sucD[OF Suc.prems(2)]

  have
    \<open>\<forall>m\<le>n. safe m c1 hl1 hs (r \<squnion> g2) g1 (sp ((=) \<times>\<^sub>R (r \<squnion> g2)\<^sup>*\<^sup>*) q1)\<close>
    \<open>\<forall>m\<le>n. safe m c2 hl2 hs (r \<squnion> g1) g2 (sp ((=) \<times>\<^sub>R (r \<squnion> g1)\<^sup>*\<^sup>*) q2)\<close>
     apply (metis Suc.prems(1) le_Suc_eq safe_step_monoD)
    apply (metis Suc.prems(2) le_Suc_eq safe_step_monoD)
    done
  then show ?case
    using Suc.hyps Suc.prems(3-)
    apply -
    apply (rule safe_suc)
       apply blast
      apply (metis safe_suc1(2) safe_suc2(2) sup2CI)
    subgoal
      apply (simp add: opstep_iff del: sup_apply)
      apply (elim disjE conjE exE)
        (* subgoal: tau *)
        apply (rule conjI)
         apply blast
        apply (clarsimp simp del: sup_apply)
        apply (insert safe_suc1(1) safe_suc2(1))
        apply (clarsimp simp del: sup_apply)
        apply (rule safe_skip[of \<open>sp ((=) \<times>\<^sub>R (r \<squnion> g2)\<^sup>*\<^sup>*) q1 \<^emph>\<and> sp ((=) \<times>\<^sub>R (r \<squnion> g1)\<^sup>*\<^sup>*) q2\<close>])
         apply (clarsimp simp add: sepconj_conj_def[of \<open>sp _ _\<close>] simp del: sup_apply)
         apply blast
        apply (rule sp_rely_sepconj_conj_semidistrib_mono)
         apply (clarsimp simp add: sp_comp_rel simp del: sup_apply; fail)
        apply (clarsimp simp add: sp_comp_rel simp del: sup_apply; fail)
        (* subgoal: left *)
       apply (frule safe_suc1(5), force)
       apply (clarsimp simp del: sup_apply)
       apply (rule conjI, force)
       apply (erule opstep_act_cases)
        apply (metis add_le_imp_le_left add_le_mono1 fstI le_numeral_extra(3) snd_eqD)
       apply (metis safe_suc2(2) sup2CI)
        (* subgoal: right *)
      apply (clarsimp simp add: partial_add_commute[of hl1] simp del: sup_apply)
      apply (frule safe_suc2(5), metis disjoint_sym)
      apply (clarsimp simp add: partial_add_commute[symmetric, of hl1] disjoint_sym_iff
          simp del: sup_apply)
      apply (erule opstep_act_cases)
       apply (simp; fail)
      apply (clarsimp simp del: top_apply)
      apply (metis safe_suc1(2) sup2CI disjoint_sym)
      done
    subgoal
      apply (simp add: opstep_iff del: top_apply sup_apply)
      apply (elim disjE conjE exE)
        (* subgoal: tau *)
        apply (rule conjI, blast)
        apply (clarsimp simp del: top_apply sup_apply)
        apply (insert safe_suc1(1) safe_suc2(1))
        apply (clarsimp simp del: top_apply sup_apply)
        apply (rule safe_skip[of \<open>sp ((=) \<times>\<^sub>R (r \<squnion> g2)\<^sup>*\<^sup>*) q1 \<^emph>\<and> sp ((=) \<times>\<^sub>R (r \<squnion> g1)\<^sup>*\<^sup>*) q2\<close>])
         apply (clarsimp simp add: sepconj_conj_def[of \<open>sp _ _\<close>] simp del: top_apply sup_apply)
         apply blast
        apply (rule sp_rely_sepconj_conj_semidistrib_mono)
         apply (simp add: sp_comp_rel; fail)
        apply (simp add: sp_comp_rel; fail)
          (* subgoal: left *)
       apply (simp add: partial_add_assoc2[of hl1] disjoint_sym_iff del: top_apply sup_apply)
       apply (frule safe_suc1(5))
        apply (metis disjoint_add_swap_lr disjoint_sym_iff)
       apply (clarsimp simp del: top_apply sup_apply)
       apply (rule conjI, blast)
       apply (rule_tac x=\<open>_ + _\<close> in exI)
       apply (intro conjI)
          apply (rule disjoint_add_swap_rl[rotated], fast)
          apply (metis disjoint_add_leftR disjoint_sym_iff)
         apply (metis disjoint_add_leftR disjoint_sym partial_add_assoc3)
        apply blast
       apply (erule opstep_act_cases, force)
       apply (metis disjoint_add_rightL disjoint_add_rightR disjoint_sym_iff safe_suc2(2) sup2CI)
        (* subgoal right *)
      apply (simp add: partial_add_commute[of hl1] partial_add_assoc2[of hl2] disjoint_sym_iff
          del: top_apply sup_apply)
      apply (frule safe_suc2(5))
       apply (metis disjoint_add_swap_lr disjoint_sym_iff)
      apply (clarsimp simp del: top_apply sup_apply)
      apply (rule conjI, force)
      apply (rule_tac x=\<open>_ + _\<close> in exI)
      apply (intro conjI)
         apply (rule disjoint_add_swap_rl[rotated], fast)
         apply (metis disjoint_add_leftR disjoint_sym_iff)
        apply (metis disjoint_add_leftR disjoint_sym partial_add_assoc3)
       apply blast
      apply (simp add: partial_add_commute[of _ hl1] disjoint_sym_iff del: top_apply sup_apply)
      apply (subst partial_add_commute, metis disjoint_add_leftL disjoint_sym)
      apply (erule opstep_act_cases, (simp; fail))
      apply (metis disjoint_add_rightL disjoint_sym_iff safe_suc1(2) sup2CI)
      done
    done
qed

lemma safe_parallel:
  \<open>safe n c1 hl1 hs (r \<squnion> g2) g1 (sp ((=) \<times>\<^sub>R (r \<squnion> g2)\<^sup>*\<^sup>*) q1) \<Longrightarrow>
    safe n c2 hl2 hs (r \<squnion> g1) g2 (sp ((=) \<times>\<^sub>R (r \<squnion> g1)\<^sup>*\<^sup>*) q2) \<Longrightarrow>
    hl1 ## hl2 \<Longrightarrow>
    sp ((=) \<times>\<^sub>R (r \<squnion> g2)\<^sup>*\<^sup>*) q1 \<^emph>\<and> sp ((=) \<times>\<^sub>R (r \<squnion> g1)\<^sup>*\<^sup>*) q2 \<le> q \<Longrightarrow>
    g1 \<squnion> g2 \<le> g \<Longrightarrow>
    safe n (c1 \<parallel> c2) (hl1 + hl2) hs r g q\<close>
  by (meson safe_guarantee_monoD safe_parallel' safe_postpred_mono)


section \<open> Soundness \<close>

lemma soundness:
  assumes \<open>rgsat c r g p q\<close>
    and \<open>p (hl, hs)\<close>
  shows \<open>safe n c hl hs r g q\<close>
  using assms
proof (induct c r g p q arbitrary: n hl hs rule: rgsat.inducts)
  case (rgsat_skip p r q g as h)
  then show ?case
    by (simp add: safe_skip)
next
  case (rgsat_seq c1 r g p1 p2 c2 p3)
  then show ?case
    using safe_seq[of n c1 hl hs r g p2 c2 p3]
    by blast
next
  case (rgsat_indet c1 r g1 p q1 c2 g2 q2 g q)
  then show ?case
    using safe_indet[of n c1 hl hs r g q c2]
    by (meson safe_guarantee_mono safe_postpred_mono)
next
  case (rgsat_endet c1 r g1 p q1 c2 g2 q2 g q)
  then show ?case
    using safe_endet[of n c1 hl hs r g q c2]
    by (meson safe_guarantee_mono safe_postpred_mono)
next
  case (rgsat_parallel s1 r g2 g1 p1 q1 s2 p2 q2 g p q)
  then show ?case
    apply -
    apply (clarsimp simp add: sepconj_conj_def[of p1 p2] le_fun_def[of p] simp del: sup_apply)
    apply (drule spec2, drule mp, assumption)
    apply (clarsimp simp del: sup_apply)
    apply (drule meta_spec2, drule meta_spec[of _ n], drule meta_mp, assumption)
    apply (drule meta_spec2, drule meta_spec[of _ n], drule meta_mp, assumption)
    apply (rule safe_parallel[where ?q1.0=q1 and ?q2.0=q2])
        apply (rule safe_postpred_mono[of q1], metis sp_rely_stronger, blast)
       apply (rule safe_postpred_mono[of q2], metis sp_rely_stronger, blast)
      apply blast
     apply blast
    apply blast
    done
next
  case (rgsat_fixpt c r g p' q' p i q)
  then show ?case
    sorry
next
  case (rgsat_atom b r p q g p' q')
  then show ?case
    by (intro safe_atom; blast)
next
  case (rgsat_frame c r g p q f1' f f2')
  then show ?case
    apply (clarsimp simp add: sepconj_conj_def[of p] simp del: sup_apply)
    apply (intro safe_frame; blast)
    done
next
  case (rgsat_weaken c r' g' p' q' p q r g)
  moreover have \<open>p' (hl, hs)\<close>
    using rgsat_weaken.hyps(3) rgsat_weaken.prems
    by (metis rev_predicate1D)
  ultimately show ?case
    by (meson safe_guarantee_mono safe_postpred_monoD safe_rely_antimonoD)
qed


end