theory Soundness3
  imports RGSep
begin

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

declare eq_OO[simp] OO_eq[simp]

lemma rel_Times_comp[simp]:
  \<open>(a \<times>\<^sub>R b) OO (c \<times>\<^sub>R d) = (a OO c) \<times>\<^sub>R (b OO d)\<close>
  by (force simp add: fun_eq_iff OO_def)


lemma sp_rely_step:
  \<open>r y y' \<Longrightarrow>
    sp ((=) \<times>\<^sub>R rx) p (x, y) \<Longrightarrow>
    sp ((=) \<times>\<^sub>R (rx OO r)) p (x, y')\<close>
  by (force simp add: sp_def)

lemma sp_rely_step_tranclp:
  \<open>r y y' \<Longrightarrow>
    sp ((=) \<times>\<^sub>R r\<^sup>+\<^sup>+) p (x, y) \<Longrightarrow>
    sp ((=) \<times>\<^sub>R r\<^sup>+\<^sup>+) p (x, y')\<close>
  by (simp add: sp_def, meson tranclp.trancl_into_trancl)

lemma sp_rely_step_rtranclp:
  \<open>r y y' \<Longrightarrow>
    sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) p (x, y) \<Longrightarrow>
    sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) p (x, y')\<close>
  by (simp add: sp_def, meson rtranclp.rtrancl_into_rtrancl)

lemma wlp_rely_step_tranclp:
  \<open>r y y' \<Longrightarrow>
    wlp ((=) \<times>\<^sub>R r\<^sup>+\<^sup>+) p (x, y) \<Longrightarrow>
    wlp ((=) \<times>\<^sub>R r\<^sup>+\<^sup>+) p (x, y')\<close>
  by (simp add: wlp_def tranclp_into_tranclp2)
  
lemma wlp_rely_step_rtranclp:
  \<open>r y y' \<Longrightarrow>
    wlp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) p (x, y) \<Longrightarrow>
    wlp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) p (x, y')\<close>
  by (simp add: wlp_def converse_rtranclp_into_rtranclp)


lemmas sp_rely_stronger = sp_refl_rel_le[where r=\<open>(=) \<times>\<^sub>R r\<^sup>*\<^sup>*\<close> for r, simplified]
lemmas sp_rely_absorb =
  sp_comp_rel[where ?r1.0=\<open>(=) \<times>\<^sub>R ra\<^sup>*\<^sup>*\<close> and ?r2.0=\<open>(=) \<times>\<^sub>R rb\<^sup>*\<^sup>*\<close> for ra rb, simplified]

lemma trivial_sp_rely_step[intro]:
  \<open>p x \<Longrightarrow> sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) p x\<close>
  by (simp add: sp_refl_relI)

section \<open> Operational Semantics \<close>

subsection \<open> Actions \<close>

datatype act = Tau | Local

lemma act_not_eq_iff[simp]:
  \<open>a \<noteq> Tau \<longleftrightarrow> a = Local\<close>
  \<open>a \<noteq> Local \<longleftrightarrow> a = Tau\<close>
  by (meson act.distinct act.exhaust)+

subsection \<open> Operational semantics steps \<close>

inductive opstep :: \<open>act \<Rightarrow> ('l \<times> 's) \<times> ('l,'s) comm \<Rightarrow> (('l \<times> 's) \<times> ('l,'s) comm) \<Rightarrow> bool\<close> where
  seq_left[intro!]: \<open>opstep a (h, c1) (h', c1') \<Longrightarrow> opstep a (h, c1 ;; c2) (h', c1' ;; c2)\<close>
| seq_right[intro!]: \<open>opstep Tau (h, Skip ;; c2) (h, c2)\<close>
| ndet_tau_left[intro]:  \<open>opstep Tau (h, c1) (h', c1') \<Longrightarrow> opstep Tau (h, c1 \<^bold>+ c2) (h', c1' \<^bold>+ c2)\<close>
| ndet_tau_right[intro]: \<open>opstep Tau (h, c2) (h', c2') \<Longrightarrow> opstep Tau (h, c1 \<^bold>+ c2) (h', c1 \<^bold>+ c2')\<close>
| ndet_skip_left[intro!]:  \<open>opstep Tau (h, Skip \<^bold>+ c2) (h, c2)\<close>
| ndet_skip_right[intro!]: \<open>opstep Tau (h, c1 \<^bold>+ Skip) (h, c1)\<close>
| ndet_local_left[intro]:  \<open>opstep Local (h, c1) s' \<Longrightarrow> opstep Local (h, c1 \<^bold>+ c2) s'\<close>
| ndet_local_right[intro]: \<open>opstep Local (h, c2) s' \<Longrightarrow> opstep Local (h, c1 \<^bold>+ c2) s'\<close>
| par_left[intro]: \<open>opstep a (h, s) (h', s') \<Longrightarrow> opstep a (h, s \<parallel> t) (h', s' \<parallel> t)\<close>
| par_right[intro]: \<open>opstep a (h, t) (h', t') \<Longrightarrow> opstep a (h, s \<parallel> t) (h', s \<parallel> t')\<close>
| par_skip[intro!]: \<open>opstep Tau (h, Skip \<parallel> Skip) (h, Skip)\<close>
| iter_skip[intro]: \<open>opstep Tau (h, c\<^sup>\<star>) (h, Skip)\<close>
  \<comment> \<open> TODO: not quite right... c has to not be able to take a move? \<close>
| iter_step[intro]: \<open>opstep Tau (h, c\<^sup>\<star>) (h, c ;; c\<^sup>\<star>)\<close>
| atomic[intro!]: \<open>a = Local \<Longrightarrow> snd s' = Skip \<Longrightarrow> b h (fst s') \<Longrightarrow> opstep a (h, Atomic b) s'\<close>

inductive_cases opstep_tauE[elim]: \<open>opstep Tau s s'\<close>
inductive_cases opstep_localE[elim]: \<open>opstep Local s s'\<close>

inductive_cases opstep_skipE[elim!]: \<open>opstep a (h, Skip) s'\<close>
inductive_cases opstep_seqE[elim]: \<open>opstep a (h, c1 ;; c2) s'\<close>
inductive_cases opstep_ndetE[elim]: \<open>opstep a (h, c1 \<^bold>+ c2) s'\<close>
inductive_cases opstep_parE[elim]: \<open>opstep a (h, c1 \<parallel> c2) s'\<close>
inductive_cases opstep_iterE[elim]: \<open>opstep a (h, c\<^sup>\<star>) s'\<close>
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
    a = Local \<and> opstep Local (h, c1) s' \<or>
    a = Local \<and> opstep Local (h, c2) s' \<or>
    a = Tau \<and> (\<exists>h' c1'. s' = (h', c1' \<^bold>+ c2) \<and> opstep Tau (h, c1) (h', c1')) \<or>
    a = Tau \<and> (\<exists>h' c2'. s' = (h', c1 \<^bold>+ c2') \<and> opstep Tau (h, c2) (h', c2')) \<or>
    a = Tau \<and> c1 = Skip \<and> s' = (h, c2) \<or>
    a = Tau \<and> c2 = Skip \<and> s' = (h, c1)\<close>
  \<open>opstep a (h, c1 \<parallel> c2) s' \<longleftrightarrow>
    a = Tau \<and> c1 = Skip \<and> c2 = Skip \<and> s' = (h, Skip) \<or>
    (\<exists>h' c1'. opstep a (h,c1) (h',c1') \<and> s' = (h', c1' \<parallel> c2)) \<or>
    (\<exists>h' c2'. opstep a (h,c2) (h',c2') \<and> s' = (h', c1 \<parallel> c2'))\<close>
  \<open>opstep a (h, c\<^sup>\<star>) s' \<longleftrightarrow>
    a = Tau \<and> s' = (h, Skip) \<or>
    a = Tau \<and> s' = (h, c ;; c\<^sup>\<star>)\<close>
  \<open>opstep a (h, Atomic b) s' \<longleftrightarrow>
    a = Local \<and> snd s' = Skip \<and> b h (fst s')\<close>
       apply force
      apply force
     apply (rule iffI, (erule opstep_ndetE; force), force)
    apply (rule iffI, (erule opstep_parE; force), force)
   apply (rule iffI, (erule opstep_iterE; force), force)
  apply (rule iffI, (erule opstep_atomicE; force), force)
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

lemma opstep_to_ndet_originally_ndet_subexpr:
  \<open>opstep a s s' \<Longrightarrow> snd s' = c1' \<^bold>+ c2' \<Longrightarrow>
    (\<exists>c1. c1 \<^bold>+ c2' \<le> snd s) \<or> (\<exists>c2. c1' \<^bold>+ c2 \<le> snd s)\<close>
  by (induct arbitrary: c1' c2' rule: opstep.inducts) force+

lemma opstep_step_to_under_left_ndet_impossible:
  \<open>opstep a s s' \<Longrightarrow> c1' \<^bold>+ c2' \<le> snd s' \<Longrightarrow> snd s \<le> c1' \<Longrightarrow> False\<close>
  apply (induct arbitrary: c1' c2' rule: opstep.inducts; clarsimp)
            apply (metis less_eq_comm_no_constructorsD(3) less_eq_comm_subexprsD(1,2))
           apply (metis less_eq_comm_no_constructorsD(3) less_eq_comm_subexprsD(2))
          apply (metis order.refl less_eq_comm_no_constructorsD(3) less_eq_comm_subexprsD(3,4))
         apply (metis order.refl less_eq_comm_no_constructorsD(3) less_eq_comm_subexprsD(3,4))
        apply (metis less_eq_comm_no_constructorsD(3) less_eq_comm_subexprsD(4))
       apply (metis less_eq_comm_no_constructorsD(3) less_eq_comm_subexprsD(3))
      apply (metis less_eq_comm_subexprsD(3))
     apply (metis less_eq_comm_subexprsD(4))
    apply (metis less_eq_comm_no_constructorsD(3) less_eq_comm_subexprsD(5,6))
   apply (metis less_eq_comm_no_constructorsD(3) less_eq_comm_subexprsD(5,6))
  apply (metis less_eq_comm_no_constructorsD(3) less_eq_comm_subexprsD(7))
  done

lemma opstep_step_to_left_ndet_impossible:
  \<open>opstep a (h, c1) (h', c1 \<^bold>+ c2) \<Longrightarrow> False\<close>
  by (metis order.refl opstep_step_to_under_left_ndet_impossible snd_conv)

lemma opstep_step_to_under_right_ndet_impossible:
  \<open>opstep a s s' \<Longrightarrow> c1' \<^bold>+ c2' \<le> snd s' \<Longrightarrow> snd s \<le> c2' \<Longrightarrow> False\<close>
  apply (induct arbitrary: c1' c2' rule: opstep.inducts; clarsimp)
            apply (metis less_eq_comm_no_constructorsD(4) less_eq_comm_subexprsD(1,2))
           apply (metis less_eq_comm_no_constructorsD(4) less_eq_comm_subexprsD(2))
          apply (metis order.refl less_eq_comm_no_constructorsD(4) less_eq_comm_subexprsD(3,4))
         apply (metis order.refl less_eq_comm_no_constructorsD(4) less_eq_comm_subexprsD(3,4))
        apply (metis less_eq_comm_no_constructorsD(4) less_eq_comm_subexprsD(4))
       apply (metis less_eq_comm_no_constructorsD(4) less_eq_comm_subexprsD(3))
      apply (metis less_eq_comm_subexprsD(3))
     apply (metis less_eq_comm_subexprsD(4))
    apply (metis less_eq_comm_no_constructorsD(4) less_eq_comm_subexprsD(5,6))
   apply (metis less_eq_comm_no_constructorsD(4) less_eq_comm_subexprsD(5,6))
  apply (metis less_eq_comm_no_constructorsD(4) less_eq_comm_subexprsD(7))
  done

lemma opstep_step_to_right_ndet_impossible:
  \<open>opstep a (h, c2) (h', c1 \<^bold>+ c2) \<Longrightarrow> False\<close>
  by (metis order.refl opstep_step_to_under_right_ndet_impossible snd_conv)

lemma opstep_always_changes_comm:
  \<open>opstep a s s' \<Longrightarrow> snd s' \<noteq> snd s\<close>
  by (induct rule: opstep.inducts)
    (force dest: opstep_step_to_left_ndet_impossible opstep_step_to_right_ndet_impossible)+

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


subsection \<open> Operational Semantics \<close>

inductive opsem
  :: \<open>act list \<Rightarrow> ('l \<times> 's) \<times> ('l,'s) comm \<Rightarrow> ('l \<times> 's) \<times> ('l,'s) comm \<Rightarrow> bool\<close>
  where
  base[intro!]: \<open>opsem [] s s\<close>
| step[intro!]: \<open>s \<midarrow>a\<rightarrow> s' \<Longrightarrow> opsem as s' s'' \<Longrightarrow> opsem (a # as) s s''\<close>

inductive_cases opsem_NilE[elim!]: \<open>opsem [] s s'\<close>
inductive_cases opsem_ConsE[elim!]: \<open>opsem (a # as) s s'\<close>

lemma opsem_iff[simp]:
  \<open>opsem [] s s' \<longleftrightarrow> s' = s\<close>
  \<open>opsem (a # as) s s'' \<longleftrightarrow> (\<exists>s'. (s \<midarrow>a\<rightarrow> s') \<and> opsem as s' s'')\<close>
  by force+


section \<open> Sugared atomic programs \<close>

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

definition \<open>IfThenElse p ct cf \<equiv> Assert p ;; ct \<^bold>+ Assert (-p) ;; cf\<close>
definition \<open>WhileLoop p c \<equiv> (Assert p ;; c)\<^sup>\<star> ;; Assert (-p)\<close>

lemma IfThenElse_inject[simp]:
  \<open>IfThenElse p1 ct1 cf1 = IfThenElse p2 ct2 cf2 \<longleftrightarrow> p1 = p2 \<and> ct1 = ct2 \<and> cf1 = cf2\<close>
  by (simp add: IfThenElse_def,
      metis less_le_not_le order_neq_less_conv(2) passert_simps predicate1I)

lemma WhileLoop_inject[simp]:
  \<open>WhileLoop p1 c1 = WhileLoop p2 c2 \<longleftrightarrow> p1 = p2 \<and> c1 = c2\<close>
  by (simp add: WhileLoop_def, metis IfThenElse_def IfThenElse_inject)

lemma IfThenElse_distinct[simp]:
  \<open>IfThenElse p ct cf \<noteq> Skip\<close>
  \<open>IfThenElse p ct cf \<noteq> c1 ;; c2\<close>
  \<open>IfThenElse p ct cf \<noteq> c1 \<parallel> c2\<close>
  \<open>IfThenElse p ct cf \<noteq> c\<^sup>\<star>\<close>
  \<open>IfThenElse p ct cf \<noteq> Atomic b\<close>
  \<open>Skip \<noteq> IfThenElse p ct cf\<close>
  \<open>c1 ;; c2 \<noteq> IfThenElse p ct cf\<close>
  \<open>c1 \<parallel> c2 \<noteq> IfThenElse p ct cf\<close>
  \<open>c\<^sup>\<star> \<noteq> IfThenElse p ct cf\<close>
  \<open>Atomic b \<noteq> IfThenElse p ct cf\<close>
  by (simp add: IfThenElse_def)+

lemma WhileLoop_distinct[simp]:
  \<open>WhileLoop p c \<noteq> Skip\<close>
  \<open>WhileLoop p c \<noteq> c1 \<^bold>+ c2\<close>
  \<open>WhileLoop p c \<noteq> c1 \<parallel> c2\<close>
  \<open>WhileLoop p c \<noteq> c\<^sup>\<star>\<close>
  \<open>WhileLoop p c \<noteq> Atomic b\<close>
  \<open>Skip \<noteq> WhileLoop p c\<close>
  \<open>c1 \<^bold>+ c2 \<noteq> WhileLoop p c\<close>
  \<open>c1 \<parallel> c2 \<noteq> WhileLoop p c\<close>
  \<open>c\<^sup>\<star> \<noteq> WhileLoop p c\<close>
  \<open>Atomic b \<noteq> WhileLoop p c\<close>
  by (simp add: WhileLoop_def)+


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
    (a = Tau \<and> s' = (h, Skip ;; Assert (- p)) \<or>
      a = Tau \<and> s' = (h, ((Assert p ;; c) ;; (Assert p ;; c)\<^sup>\<star>) ;; Assert (- p)))\<close>
  by (simp add: WhileLoop_def opstep_iff, metis surj_pair)

lemma opstep_WhileLoop_true[intro]:
  \<open>p h \<Longrightarrow> opstep Tau (h, WhileLoop p c) (h, (((Assert p ;; c) ;; (Assert p ;; c)\<^sup>\<star>) ;; Assert (-p)))\<close>
  by (simp add: opstep_iff)

lemma opstep_WhileLoop_false[intro]:
  \<open>\<not> p h \<Longrightarrow> opstep Tau (h, WhileLoop p c) (h, (((Assert p ;; c) ;; (Assert p ;; c)\<^sup>\<star>) ;; Assert (-p)))\<close>
  by (simp add: opstep_iff)


section \<open> Safe \<close>

inductive safe
  :: \<open>nat \<Rightarrow> ('l::perm_alg, 's::perm_alg) comm \<Rightarrow>
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
    (\<And>c' hx'. ((hl, hs), c) \<midarrow>Local\<rightarrow> (hx', c') \<Longrightarrow> safe n c' (fst hx') (snd hx') r g q) \<Longrightarrow>
    \<comment> \<open> opsteps are frame closed and establish the guarantee \<close>
    (\<And>c' hx'. ((hl, hs), c) \<midarrow>Local\<rightarrow> (hx', c') \<Longrightarrow> g hs (snd hx')) \<Longrightarrow>
\<comment> \<open>
    (\<And>c' hsf hx'.
        ((hl, hs + hsf), c) \<midarrow>Local\<rightarrow> (hx', c') \<Longrightarrow>
        hs ## hsf \<Longrightarrow>
        g (hs + hsf) (snd hx') \<and> (\<exists>hs'. hs' ## hsf \<and> snd hx' = hs' + hsf)) \<Longrightarrow> \<close>
    (\<And>c' hlf hx'.
        ((hl + hlf, hs), c) \<midarrow>Local\<rightarrow> (hx', c') \<Longrightarrow>
        hl ## hlf \<Longrightarrow>
        g hs (snd hx') \<and>
        (\<exists>hl'. hl' ## hlf \<and> fst hx' = hl' + hlf \<and>
          safe n c' hl' (snd hx') r g q)) \<Longrightarrow>
\<comment> \<open>
    (\<And>c' hsf hlf hx'.
        ((hl + hlf, hs + hsf), c) \<midarrow>Local\<rightarrow> (hx', c') \<Longrightarrow>
        hl ## hlf \<Longrightarrow>
        hs ## hsf \<Longrightarrow>
        g (hs + hsf) (snd hx') \<and>
        (\<exists>hl'. hl' ## hlf \<and> fst hx' = hl' + hlf) \<and>
        (\<exists>hs'. hs' ## hsf \<and> snd hx' = hs' + hsf))  \<Longrightarrow> \<close>
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
    (\<forall>c' hx'. ((hl, hs), c) \<midarrow>Local\<rightarrow> (hx', c') \<longrightarrow> safe n c' (fst hx') (snd hx') r g q) \<and>
    (\<forall>c' hx'. ((hl, hs), c) \<midarrow>Local\<rightarrow> (hx', c') \<longrightarrow> g hs (snd hx')) \<and>
    \<comment> \<open>(\<forall>c' hsf hx'.
        ((hl, hs + hsf), c) \<midarrow>Local\<rightarrow> (hx', c') \<longrightarrow>
        hs ## hsf \<longrightarrow>
        g (hs + hsf) (snd hx') \<and> (\<exists>hs'. hs' ## hsf \<and> snd hx' = hs' + hsf)) \<and>\<close>
    (\<forall>c' hlf hx'.
        ((hl + hlf, hs), c) \<midarrow>Local\<rightarrow> (hx', c') \<longrightarrow>
        hl ## hlf \<longrightarrow>
        g hs (snd hx') \<and> (\<exists>hl'. hl' ## hlf \<and> fst hx' = hl' + hlf \<and> safe n c' hl' (snd hx') r g q))
    \<comment> \<open>\<and> (\<forall>c' hsf hlf hx'.
        ((hl + hlf, hs + hsf), c) \<midarrow>Local\<rightarrow> (hx', c') \<longrightarrow>
        hl ## hlf \<longrightarrow>
        hs ## hsf \<longrightarrow>
        g (hs + hsf) (snd hx') \<and>
        (\<exists>hl'. hl' ## hlf \<and> fst hx' = hl' + hlf) \<and>
        (\<exists>hs'. hs' ## hsf \<and> snd hx' = hs' + hsf)) \<close>\<close>
  apply (rule iffI)
   apply (erule safe_sucE, (simp; fail))
  apply (rule safe_suc; presburger)
  done

lemma safe_sucD:
  \<open>safe (Suc n) c hl hs r g q \<Longrightarrow> c = Skip \<Longrightarrow> q (hl, hs)\<close>
  \<open>safe (Suc n) c hl hs r g q \<Longrightarrow> r hs hs' \<Longrightarrow> safe n c hl hs' r g q\<close>
  \<open>safe (Suc n) c hl hs r g q \<Longrightarrow> ((hl, hs), c) \<midarrow>Local\<rightarrow> (hx', c') \<Longrightarrow> safe n c' (fst hx') (snd hx') r g q\<close>
  \<open>safe (Suc n) c hl hs r g q \<Longrightarrow> ((hl, hs), c) \<midarrow>Local\<rightarrow> (hx', c') \<Longrightarrow> g hs (snd hx')\<close>
  \<comment> \<open>safe (Suc n) c hl hs r g q \<Longrightarrow>
      ((hl, hs + hsf), c) \<midarrow>Local\<rightarrow> (hx', c') \<Longrightarrow>
      hs ## hsf \<Longrightarrow>
      g (hs + hsf) (snd hx') \<and> (\<exists>hs'. hs' ## hsf \<and> snd hx' = hs' + hsf)\<close>
  \<open>safe (Suc n) c hl hs r g q \<Longrightarrow>
      ((hl + hlf, hs), c) \<midarrow>Local\<rightarrow> (hx', c') \<Longrightarrow>
      hl ## hlf \<Longrightarrow>
      g hs (snd hx') \<and> (\<exists>hl'. hl' ## hlf \<and> fst hx' = hl' + hlf \<and> safe n c' hl' (snd hx') r g q)\<close>
  \<comment> \<open>safe (Suc n) c hl hs r g q \<Longrightarrow>
      ((hl + hlf, hs + hsf), c) \<midarrow>Local\<rightarrow> (hx', c') \<Longrightarrow>
      hl ## hlf \<Longrightarrow>
      hs ## hsf \<Longrightarrow>
      g (hs + hsf) (snd hx') \<and>
      (\<exists>hl'. hl' ## hlf \<and> fst hx' = hl' + hlf) \<and>
      (\<exists>hs'. hs' ## hsf \<and> snd hx' = hs' + hsf)\<close>
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
        apply (blast intro: safe_suc.hyps)
       apply (blast intro: safe_suc.hyps)
    apply (metis predicate2D safe_suc.hyps(7))
(*
     apply (metis predicate2D safe_suc.hyps(8))
    apply (metis predicate2D safe_suc.hyps(9)) *)
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
  \<open>sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) q (hl, hs) \<Longrightarrow> safe n Skip hl hs r g (sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) q)\<close>
  apply (induct n arbitrary: hl hs q)
   apply force
  apply (rule safe_suc)
        apply blast
       apply (simp add: weak_framed_subresource_rel_def all_conj_distrib sp_def)
       apply (meson opstep_skipE rtranclp.rtrancl_into_rtrancl; fail)
      apply blast+
  done

lemma safe_skip:
  \<open>p (hl, hs) \<Longrightarrow> sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) p \<le> q \<Longrightarrow> safe n Skip hl hs r g q\<close>
  apply (rule safe_postpred_monoD[OF safe_skip'[where q=p]])
   apply (metis (mono_tags, lifting) rel_Times_iff rtranclp.rtrancl_refl sp_def)
  apply blast
  done


subsection \<open> Safety of Atomic \<close>

abbreviation plus_fst :: \<open>'a::plus \<times> 'b \<Rightarrow> 'a \<Rightarrow> 'a \<times> 'b\<close> (infixl \<open>+\<^sub>L\<close> 65) where
  \<open>plus_fst xy a \<equiv> apfst (\<lambda>z. z + a) xy\<close>

abbreviation plus_snd :: \<open>'a \<times> 'b::plus \<Rightarrow> 'b \<Rightarrow> 'a \<times> 'b\<close> (infixl \<open>+\<^sub>R\<close> 65) where
  \<open>plus_snd xy a \<equiv> apsnd (\<lambda>z. z + a) xy\<close>

lemma plus_fst_accum[simp]:
  fixes x :: \<open>'a :: semigroup_add\<close>
  shows \<open>(xy +\<^sub>L x) +\<^sub>L x' = xy +\<^sub>L (x + x')\<close>
  by (cases xy, simp add: add.assoc)

lemma perm_alg_plus_fst_accum[simp]:
  fixes x :: \<open>'a :: perm_alg\<close>
  shows \<open>fst xy ## x \<Longrightarrow> fst xy ## x' \<Longrightarrow> x ## x' \<Longrightarrow> (xy +\<^sub>L x) +\<^sub>L x' = xy +\<^sub>L (x + x')\<close>
  by (cases xy, simp add: partial_add_assoc)

lemma plus_snd_accum[simp]:
  fixes y :: \<open>'a :: semigroup_add\<close>
  shows \<open>(xy +\<^sub>L y) +\<^sub>L y' = xy +\<^sub>L (y + y')\<close>
  by (cases xy, simp add: add.assoc)

lemma perm_alg_plus_snd_accum[simp]:
  fixes y :: \<open>'a :: perm_alg\<close>
  shows \<open>snd xy ## y \<Longrightarrow> snd xy ## y' \<Longrightarrow> y ## y' \<Longrightarrow> (xy +\<^sub>R y) +\<^sub>R y' = xy +\<^sub>R (y + y')\<close>
  by (cases xy, simp add: partial_add_assoc)

lemma perm_alg_plus_fst_plus_snd_eq[simp]:
  fixes y :: \<open>'a :: perm_alg\<close>
  shows
    \<open>xy +\<^sub>L x +\<^sub>R y = xy + (x, y)\<close>
    \<open>xy +\<^sub>R y +\<^sub>L x = xy + (x, y)\<close>
  by simp+

definition
  \<open>atom_unframe_prop b xy \<equiv>
    (\<forall>xf xxfy'.
      b (xy +\<^sub>L xf) xxfy' \<longrightarrow> fst xy ## xf \<longrightarrow>
      (\<exists>xy'. fst xy' ## xf \<and> xxfy' = xy' +\<^sub>L xf \<and> b xy xy'))
    \<comment> \<open> \<and> (\<forall>yf xyyf'.
      b (xy +R yf) xyyf' \<longrightarrow> snd xy ## yf \<longrightarrow>
      (\<exists>xy'. snd xy' ## yf \<and> xyyf' = xy' +R yf \<and> b xy xy')) \<and>
    (\<forall>xyf xyxyf'.
      b (xy + xyf) xyxyf' \<longrightarrow> xy ## xyf \<longrightarrow>
      (\<exists>xy'. xy' ## xyf \<and> xyxyf' = xy' + xyf \<and> b xy xy')) \<close>\<close>

lemma safe_atom':
  \<open>sp b (wlp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) p) \<le> sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) q \<Longrightarrow>
    wlp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) p (hl, hs) \<Longrightarrow>
    ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) (hl, hs) \<le> atom_unframe_prop b \<Longrightarrow>
    b \<le> \<top> \<times>\<^sub>R g \<Longrightarrow>
    safe n (Atomic b) hl hs r g (sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) q)\<close>
proof (induct n arbitrary: hl hs)
  case 0
  then show ?case by force
next
  case (Suc n)
  show ?case
    using Suc.prems
    apply (intro safe.safe_suc)
      (* Skip *)
          apply force
      (* Rely safe *)
         apply (rule Suc.hyps; force simp add: wlp_rely_step_rtranclp)
      (* Opstep safe *)
        apply (simp add: opstep_iff del: top_apply sup_apply)
        apply (rule safe_skip[where p=\<open>sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) q\<close>])
         apply (simp del: sup_apply, blast)
        apply (force simp add: sp_rely_absorb)
      (* Opstep guarantee 1 *)
       apply (simp add: opstep_iff del: top_apply sup_apply)
     apply (metis predicate2D prod.collapse rel_Times_iff)
(*
      (* Opstep guarantee 2 *)
      apply (clarsimp simp add: opstep_iff atom_unframe_prop_def le_fun_def
        simp del: top_apply sup_apply, blast) *)
      (* Opstep guarantee 3 *)
     apply (clarsimp simp add: opstep_iff atom_unframe_prop_def le_fun_def
        simp del: sup_apply)
    apply (drule spec, drule mp, rule rtranclp.rtrancl_refl)
    apply (drule spec2, drule spec, drule mp, fast, drule mp, fast)
    apply clarsimp
    apply (intro exI conjI, fast, fast)
    apply (rule safe_skip')
    apply (simp add: sp_def[of b] imp_ex_conjL; fail)
      (* (* Opstep guarantee 4 *)
    apply (clarsimp simp add: opstep_iff atom_unframe_prop_def le_fun_def
        simp del: top_apply sup_apply, fast) *)
    done
qed

lemma safe_atom:
  \<open>sp b (wlp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) p) \<le> sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) q \<Longrightarrow>
    wlp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) p (hl, hs) \<Longrightarrow>
    ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) (hl, hs) \<le> atom_unframe_prop b \<Longrightarrow>
    b \<le> \<top> \<times>\<^sub>R g \<Longrightarrow>
    sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) q \<le> q' \<Longrightarrow>
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
    apply (clarsimp simp add: opstep_iff; fail)
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
      apply (clarsimp simp add: opstep_iff; fail)
     apply (clarsimp simp add: opstep_iff, metis)+
  done

lemma safe_seq':
  \<open>safe n c1 hl hs r g q \<Longrightarrow>
    (\<forall>m hl' hs'. m \<le> n \<longrightarrow> q (hl', hs') \<longrightarrow> safe m c2 hl' hs' r g q') \<Longrightarrow>
    safe n (c1 ;; c2) hl hs r g q'\<close>
  apply (induct arbitrary: c2 q' rule: safe.inducts)
   apply force
  apply (rule safe_suc)
      apply force
     apply force
    apply (clarsimp simp add: opstep_iff; fail)+
  apply (clarsimp simp add: le_Suc_eq opstep_iff)
  apply metis
  done

lemma safe_seq:
  \<open>safe n c1 hl hs r g q \<Longrightarrow>
    (\<forall>hl' hs'. q (hl', hs') \<longrightarrow> safe n c2 hl' hs' r g q') \<Longrightarrow>
    safe n (c1 ;; c2) hl hs r g q'\<close>
  by (rule safe_seq', fast, metis safe_step_monoD)


subsection \<open> Safety of Iteration \<close>

lemma safe_iter':
  \<open>(\<forall>m\<le>n. \<forall>hl' hs'. sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) i (hl', hs') \<longrightarrow> safe m c hl' hs' r g (sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) i)) \<Longrightarrow>
    sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) i (hl, hs) \<Longrightarrow>
    safe n (c\<^sup>\<star>) hl hs r g (sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) i)\<close>
  apply (induct n arbitrary: i hl hs)
   apply force
  apply (rule safe_suc)
        apply blast
       apply (clarsimp simp add: sp_rely_step_rtranclp; fail)
      apply (simp add: le_Suc_eq all_conj_distrib opstep_iff; fail)+
  done


lemma safe_iter:
  \<open>(\<And>n hl hs. p' (hl, hs) \<Longrightarrow> safe n c hl hs r g q') \<Longrightarrow>
    p \<le> i \<Longrightarrow>
    sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) i \<le> p' \<Longrightarrow>
    q' \<le> i \<Longrightarrow>
    sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) i \<le> q \<Longrightarrow>
    p (hl, hs) \<Longrightarrow>
    safe n (c\<^sup>\<star>) hl hs r g q\<close>
  apply (rule safe_postpred_mono, assumption)
  apply (rule safe_iter')
   apply (metis (mono_tags) predicate1D safe_postpred_monoD sp_rely_stronger)
  apply (metis predicate1D sp_rely_stronger)
  done


subsubsection \<open> Safety of Nondeterminism \<close>

lemma safe_ndet:
  \<open>\<forall>m\<le>n. safe m c1 hl hs r g q \<Longrightarrow>
    \<forall>m\<le>n. safe m c2 hl hs r g q \<Longrightarrow>
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
    by simp+
  then show ?case
    apply -
    apply (rule safe_suc)
          apply blast
         apply (meson Suc.hyps safe_step_monoD safe_suc1(2) safe_suc2(2); fail)
        apply (force dest: safe_suc1(3) safe_suc2(3) simp add: opstep_iff)
       apply (fastforce dest: safe_suc1(4) safe_suc2(4))
    apply (simp add: opstep_iff, metis safe_suc1(5) safe_suc2(5))
(*
     apply (simp add: opstep_iff, metis safe_suc1(6) safe_suc2(6))
    apply (simp add: opstep_iff, metis safe_suc1(7) safe_suc2(7))
*)
    done
qed


subsection \<open> Safety of frame \<close>

lemma safe_frame':
  \<open>safe n c hl hs r g q \<Longrightarrow>
    \<forall>hs'. (r \<squnion> g)\<^sup>*\<^sup>* hs hs' \<longrightarrow> unframe_prop f (\<lambda>x y. \<exists>c c' hs''. opstep Local ((x, hs'), c) ((y, hs''), c')) \<Longrightarrow>
    hl ## hlf \<Longrightarrow>
    f hlf \<Longrightarrow>
    safe n c (hl + hlf) hs r g (q \<^emph>\<and> sp ((=) \<times>\<^sub>R (r \<squnion> g)\<^sup>*\<^sup>*) (f \<times>\<^sub>P \<top>))\<close>
proof (induct arbitrary: hlf rule: safe.induct)
  case (safe_nil c hl hs r g q)
  then show ?case by blast
next
  case (safe_suc c q hl hs r n g)

  show ?case
    using safe_suc.prems
    apply -
    apply (rule safe.safe_suc)
      (* subgoal Skip *)
          apply (clarsimp simp add: sepconj_conj_def simp del: sup_apply)
          apply (drule mp[OF safe_suc.hyps(1)])
          apply (intro exI conjI, fast, fast, fast, force simp add: trivial_sp_rely_step)
      (* subgoal rely *)
       apply (frule safe_suc.hyps(3))
          apply (meson converse_rtranclp_into_rtranclp sup2I1; fail)
         apply fast
        apply fast
       apply fast
      (* subgoal opstep safe *)
      apply (frule safe_suc.hyps(7), blast)
      apply (clarsimp simp del: sup_apply top_apply)
      apply (blast intro: converse_rtranclp_into_rtranclp)
      (* subgoal opstep guar 1 *)
     apply (clarsimp simp del: sup_apply simp add: safe_suc.hyps(7); fail)
(*
      (* subgoal opstep guar 2 *)
      apply (clarsimp simp del: sup_apply)
      apply (simp add: partial_add_assoc2[of hs hsf])
      apply (drule safe_suc.hyps(9), fast, force simp add: disjoint_add_swap_lr)
      apply (metis disjoint_add_leftR disjoint_add_swap_rl partial_add_assoc3 snd_conv)
*)
      (* subgoal opstep guar 3 *)
    apply (rename_tac c' hlf2 hx')
    apply (clarsimp simp add: partial_add_assoc2[of hl hlf] simp del: sup_apply top_apply)
    apply (frule safe_suc.hyps(7), force simp add: disjoint_add_swap_lr)
    apply (clarsimp simp del: sup_apply top_apply)
    apply (frule mp, (meson converse_rtranclp_into_rtranclp sup2CI; fail))
    apply (clarsimp simp del: sup_apply top_apply)
    apply (drule spec, drule mp, blast)
    apply (rule_tac x=\<open>hl' + hlf\<close> in exI, rule conjI)
     apply (meson disjoint_add_leftR disjoint_add_swap_rl; fail)
    apply (rule conjI)
     apply (metis disjoint_add_leftR partial_add_assoc3)
    apply (meson disjoint_add_leftR disjoint_add_rightL)
(*
      (* subgoal opstep guar 4 *)
    apply (clarsimp simp del: sup_apply)
    apply (simp add: partial_add_assoc2)
    apply (drule safe_suc.hyps(9), force simp add: disjoint_add_swap_lr,
        force simp add: disjoint_add_swap_lr)
    apply (metis disjoint_add_leftR disjoint_add_swap_rl partial_add_assoc3 fst_conv snd_conv)
*)
    done
qed

lemma sepconj_conj_monoR:
  \<open>q \<le> q' \<Longrightarrow> p \<^emph>\<and> q \<le> p \<^emph>\<and> q'\<close>
  by (force simp add: sepconj_conj_def)

lemma safe_frame:
  \<open>safe n c hl hs r g q \<Longrightarrow>
    \<forall>hs'. (r \<squnion> g)\<^sup>*\<^sup>* hs hs' \<longrightarrow> unframe_prop f (\<lambda>x y. \<exists>c c' hs''. opstep Local ((x, hs'), c) ((y, hs''), c')) \<Longrightarrow>
    hl ## hlf \<Longrightarrow>
    f hlf \<Longrightarrow>
    sp ((=) \<times>\<^sub>R (r \<squnion> g)\<^sup>*\<^sup>*) (f \<times>\<^sub>P \<top>) \<le> f' \<Longrightarrow>
    safe n c (hl + hlf) hs r g (q \<^emph>\<and> f')\<close>
  apply (rule safe_postpred_monoD)
   apply (rule safe_frame')
      apply blast
     apply blast
    apply blast
   apply blast
  apply (blast dest: sepconj_conj_monoR)
  done


(*
subsection \<open> Safety of splitting parallel \<close>

lemma safe_parallel':
  \<open>safe n c1 hl1 hs1 (r \<squnion> g2) g1 (sp ((=) \<times>\<^sub>R (r \<squnion> g2)\<^sup>*\<^sup>* ) q1) \<Longrightarrow>
    safe n c2 hl2 hs2 (r \<squnion> g1) g2 (sp ((=) \<times>\<^sub>R (r \<squnion> g1)\<^sup>*\<^sup>* ) q2) \<Longrightarrow>
    parallel_unframe_prop \<top> \<top> r (r \<squnion> g2) (r \<squnion> g1) \<Longrightarrow>
    hl1 ## hl2 \<Longrightarrow>
    hs1 ## hs2 \<Longrightarrow>
    safe n (c1 \<parallel> c2) (hl1 + hl2) (hs1 + hs2) r (g1 \<squnion> g2)
      ((sp ((=) \<times>\<^sub>R (r \<squnion> g2)\<^sup>*\<^sup>* ) q1) \<^emph> (sp ((=) \<times>\<^sub>R (r \<squnion> g1)\<^sup>*\<^sup>* ) q2))\<close>
proof (induct n arbitrary: c1 c2 hl1 hs1 hl2 hs2)
  case 0
  then show ?case by force
next
  case (Suc n)

  note safe_suc1 = safe_sucD[OF Suc.prems(1)]
  note safe_suc2 = safe_sucD[OF Suc.prems(2)]

  note safe_suc1_4 =
    safe_suc1(4)[of \<open>(hlf,hsf)\<close> for hlf hsf, simplified plus_prod_def fst_conv snd_conv]
  note safe_suc2_4 =
    safe_suc2(4)[of \<open>(hlf,hsf)\<close> for hlf hsf, simplified plus_prod_def fst_conv snd_conv]

  have safe_suc2_4':
    \<open>\<And>hlf hsf hx' c'.
      opstep Local ((hlf + hl2, hsf + hs2), c2) (hx', c') \<Longrightarrow>
      (hlf, hsf) ## (hl2, hs2) \<Longrightarrow>
      \<exists>hl' hs'.
        hx' = (hlf + hl', hsf + hs') \<and>
        (hlf, hsf) ## (hl', hs') \<and>
        g2 (hsf + hs2) (hsf + hs') \<and>
        safe n c' hl' hs' (r \<squnion> g1) g2 (sp ((=) \<times>\<^sub>R (r \<squnion> g1)\<^sup>*\<^sup>* ) q2)\<close>
    apply (clarsimp simp add: partial_add_commute[of _ hl2] partial_add_commute[of _ hs2])
    apply (drule safe_suc2_4, (simp add: disjoint_sym_iff; fail))
    apply (clarsimp simp del: sup_apply)
    apply (metis disjoint_sym partial_add_commute)
    done
  have safe_suc2_4'':
    \<open>\<And>hlf hsf hx' c' hlf2 hsf2.
      opstep Local ((hlf + (hl2 + hlf2), hsf + (hs2 + hsf2)), c2) (hx', c') \<Longrightarrow>
      hlf ## hl2 \<Longrightarrow>
      hsf ## hs2 \<Longrightarrow>
      hlf + hl2 ## hlf2 \<Longrightarrow>
      hsf + hs2 ## hsf2 \<Longrightarrow>
      \<exists>hl' hs'.
        hx' = (hlf + (hl' + hlf2), hsf + (hs' + hsf2)) \<and>
        (hlf2, hsf2) ## (hl', hs') \<and>
        (hlf, hsf) ## (hl' + hlf2, hs' + hsf2) \<and>
        g2 (hsf + (hs2 + hsf2)) (hsf + (hs' + hsf2)) \<and>
        safe n c' hl' hs' (r \<squnion> g1) g2 (sp ((=) \<times>\<^sub>R (r \<squnion> g1)\<^sup>*\<^sup>* ) q2)\<close>
    apply (subst (asm) partial_add_left_commute2[symmetric, of hl2])
      apply (metis disjoint_add_leftR)
     apply (metis disjoint_add_swap_lr)
    apply (subst (asm) partial_add_left_commute2[symmetric, of hs2])
      apply (metis disjoint_add_leftR)
     apply (metis disjoint_add_swap_lr)
    apply (drule safe_suc2_4, (simp, metis disjoint_add_left_commute2 disjoint_sym_iff))
    apply (clarsimp simp del: sup_apply)
    apply (rule exI, rule conjI)
     apply (rule partial_add_left_commute)
       apply (metis disjoint_add_leftL disjoint_sym)
      apply (metis disjoint_add_leftL)
     apply (metis disjoint_add_leftL disjoint_add_rightR)
    apply (rule exI, rule conjI)
     apply (rule partial_add_left_commute)
       apply (metis disjoint_add_leftL disjoint_sym)
      apply (metis disjoint_add_leftL)
     apply (meson disjoint_add_leftL disjoint_add_rightR)
    apply (rule conjI, metis disjoint_add_leftL disjoint_add_rightR disjoint_sym)
    apply (rule conjI, metis disjoint_add_leftL disjoint_add_rightR disjoint_sym)
    apply (rule conjI, metis disjoint_add_leftL disjoint_add_right_commute)
    apply (rule conjI, metis disjoint_add_leftL disjoint_add_right_commute)
    apply (metis disjoint_add_leftL disjoint_sym_iff partial_add_commute partial_add_left_commute)
    done

  show ?case
    using Suc.prems(3-)
    apply -
    apply (rule safe_suc)
       apply blast
    subgoal
      apply (frule parallel_unframe_propD, fast, fast)
      apply (clarsimp simp del: top_apply sup_apply)
      apply (rule Suc.hyps)
          apply (rule safe_suc1(2), force)
         apply (rule safe_suc2(2), force)
        apply force
       apply force
      apply force
      done
    subgoal
      apply (simp add: opstep_iff del: top_apply sup_apply)
      apply (elim disjE conjE exE)
       apply (drule safe_suc1_4, force)
       apply (clarsimp simp del: top_apply sup_apply)
       apply (rule conjI, fast)
       apply (rule Suc.hyps[rotated 2], fast, fast, fast, fast)
       apply (metis Suc.prems(2) le_add2 plus_1_eq_Suc safe_step_monoD)
      apply (drule safe_suc2_4', force)
      apply (clarsimp simp del: top_apply sup_apply)
      apply (rule conjI, fast)
      apply (rule Suc.hyps[rotated 1], fast, fast, fast, fast)
      apply (metis Suc.prems(1) le_add2 plus_1_eq_Suc safe_step_monoD)
      done
    subgoal
      apply (simp add: partial_add_assoc2 opstep_iff del: top_apply sup_apply)
      apply (elim disjE conjE exE)
      subgoal
        apply (drule safe_suc1_4, (simp add: disjoint_add_swap_lr; fail))
        apply (clarsimp simp del: top_apply sup_apply)
        apply (rule exI, rule conjI)
         apply (rule disjoint_add_swap[rotated], fast, metis disjoint_add_leftR)
        apply (rule exI, rule conjI)
         apply (rule disjoint_add_swap[rotated], fast, metis disjoint_add_leftR)
        apply (rule conjI, metis disjoint_add_leftR partial_add_assoc3)
        apply (rule conjI, metis disjoint_add_leftR partial_add_assoc3)
        apply (rule conjI, metis disjoint_add_leftR partial_add_assoc3 sup2I1)
        apply (rule Suc.hyps)
            apply fast
           apply (metis Suc.prems(2) le_add2 plus_1_eq_Suc safe_step_monoD)
          apply fast
         apply (meson disjoint_add_leftR disjoint_preservation2 partial_le_plus)
        apply (meson disjoint_add_leftR disjoint_preservation2 partial_le_plus)
        done
      subgoal
        apply (drule safe_suc2_4'', fast, fast, fast, fast)
        apply (clarsimp simp del: top_apply sup_apply)
        apply (rule exI, rule conjI)
         apply (rule disjoint_add_swap[rotated], fast, metis disjoint_sym)
        apply (rule exI, rule conjI)
         apply (rule disjoint_add_swap[rotated], fast, metis disjoint_sym)
        apply (rule conjI, metis disjoint_sym partial_add_assoc3)
        apply (rule conjI, metis disjoint_sym partial_add_assoc3)
        apply (rule conjI, metis disjoint_sym partial_add_assoc3 sup2I2)
        apply (rule Suc.hyps)
            apply (metis Suc.prems(1) le_add2 plus_1_eq_Suc safe_step_monoD)
           apply fast
          apply fast
         apply (metis disjoint_add_rightL disjoint_sym)
        apply (metis disjoint_add_rightL disjoint_sym)
        done
      done
    done
qed
*)

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

  note safe_suc1_4 =
    safe_suc1(4)[of \<open>(hlf,hsf)\<close> for hlf hsf, simplified plus_prod_def fst_conv snd_conv]
  note safe_suc2_4 =
    safe_suc2(4)[of \<open>(hlf,hsf)\<close> for hlf hsf, simplified plus_prod_def fst_conv snd_conv]

  show ?case
    using Suc.prems(3-)
    apply -
    apply (rule safe_suc)
       apply blast
    subgoal
      apply (rule Suc.hyps)
        apply (rule safe_suc1(2), force)
       apply (rule safe_suc2(2), force)
      apply force
      done
    subgoal
      apply (simp add: opstep_iff del: top_apply sup_apply)
      apply (elim disjE conjE exE)
       apply (frule safe_suc1(5), force)
       apply (clarsimp simp del: top_apply sup_apply)
       apply (meson Suc.hyps safe_suc2(2) sup2CI; fail)
      apply (clarsimp simp add: partial_add_commute[of hl1] simp del: top_apply sup_apply)
      apply (frule safe_suc2(5), metis disjoint_sym)
      apply (clarsimp simp del: top_apply sup_apply)
      apply (clarsimp simp add: partial_add_commute[symmetric, of hl1] disjoint_sym_iff
          simp del: top_apply sup_apply)
      apply (meson Suc.hyps disjoint_sym safe_suc1(2) sup2CI)
      done
    subgoal
      apply (simp add: partial_add_assoc2 opstep_iff del: top_apply sup_apply)
      apply (elim disjE conjE exE)
       apply (frule safe_suc1(5), force, force)
      apply (clarsimp simp add: partial_add_commute[of hl1] simp del: top_apply sup_apply)
      apply (frule safe_suc2(5), metis disjoint_sym, force)
      done
(*
    subgoal
      apply (simp add: opstep_iff del: top_apply sup_apply)
      apply (elim disjE conjE exE)
       apply (frule safe_suc1(7), force, force, force)
      apply (clarsimp simp add: partial_add_commute[of hl1] simp del: top_apply sup_apply)
      apply (frule safe_suc2(7), metis disjoint_sym, force, force)
      done
*)
    subgoal
      apply (simp add: opstep_iff del: top_apply sup_apply)
      apply (elim disjE conjE exE)
       apply (simp add: partial_add_assoc2 del: top_apply sup_apply)
       apply (frule safe_suc1(5), force simp add: disjoint_add_swap_lr)
       apply (clarsimp simp del: top_apply sup_apply)
       apply (frule safe_suc2(2)[unfolded sup_apply, OF sup_boolI2])
       apply (metis (mono_tags, lifting) Suc.hyps disjoint_add_leftR disjoint_add_rightL
          disjoint_add_swap_rl partial_add_assoc3 safe_suc2(2) sup2CI)
      apply (simp add: partial_add_commute[of hl1] partial_add_assoc2[of hl2] disjoint_sym_iff
          del: top_apply sup_apply)
      apply (frule safe_suc2(5), force simp add: disjoint_add_swap_lr disjoint_sym_iff)
      apply (clarsimp simp del: top_apply sup_apply)
      apply (frule safe_suc1(2)[unfolded sup_apply, OF sup_boolI2])
      apply (intro conjI exI)
         prefer 4
         apply (rule Suc.hyps, force, blast)
         apply (metis disjoint_add_leftL disjoint_add_rightR disjoint_sym)
        apply blast
       apply (metis disjoint_add_left_commute2 disjoint_add_rightR disjoint_sym)
      apply (metis disjoint_add_rightL disjoint_add_rightR partial_add_assoc_commute_left
          disjoint_sym)
      done
(*
    subgoal
      apply (simp add: opstep_iff del: top_apply sup_apply)
      apply (elim disjE conjE exE)
       apply (simp add: partial_add_assoc2 del: top_apply sup_apply)
       apply (frule safe_suc1(7), force simp add: disjoint_add_swap_lr, force)
       apply (metis disjoint_add_leftR disjoint_add_rightL disjoint_add_swap_rl fstI partial_add_assoc2 snd_eqD sup2I1)
      apply (simp add: partial_add_commute[of hl1] partial_add_assoc2[of hl2] disjoint_sym_iff
          del: top_apply sup_apply)
      apply (frule safe_suc2(7), force simp add: disjoint_add_swap_lr disjoint_sym_iff, force)
      apply (metis disjoint_add_rightL disjoint_add_swap_rl disjoint_sym fstI partial_add_assoc sndI
          sup2I2)
*)
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
  case (rgsat_iter c r g p' q' p i q)
  then show ?case
    using safe_iter[of p' _ _ _ q' p i]
    by force
next
  case (rgsat_seq c1 r g p1 p2 c2 p3)
  then show ?case
    using safe_seq[of n c1 hl hs r g p2 c2 p3]
    by blast
next
  case (rgsat_ndet c1 r g1 p q1 c2 g2 q2 g q)
  then show ?case
    using safe_ndet[of n c1 hl hs r g q c2]
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
  case (rgsat_atom b r p q g pf f q')
  then show ?case
    thm safe_atom
    sorry
next
  case (rgsat_frame c r g p q f f' n)
  then show ?case
    apply -
    apply (clarsimp simp add: sepconj_def[of p f] simp del: sup_apply)
    apply (drule meta_spec2, drule meta_spec[of _ n], drule meta_mp, assumption)
    sorry
next
  case (rgsat_weaken c r' g' p' q' p q r g)
  moreover have \<open>p' (hl, hs)\<close>
    using rgsat_weaken.hyps(3) rgsat_weaken.prems
    by (metis rev_predicate1D)
  ultimately show ?case
    by (meson safe_guarantee_mono safe_postpred_monoD safe_rely_antimonoD)
qed


subsection \<open> Refinement closure \<close>

lemma safe_refinement_mono:
  \<open>safe n prg hl hs r g q \<Longrightarrow> prg = (Atomic a) \<Longrightarrow> c \<le> a \<Longrightarrow> safe n (Atomic c) hl hs r g q\<close>
  apply (induct arbitrary: a c rule: safe.inducts)
   apply force
  apply (simp add: safe_sucE)
  apply (rule safe_suc)
        apply blast
       apply blast
      apply (clarsimp simp add: opstep_iff le_fun_def; fail)
     apply (clarsimp simp add: opstep_iff le_fun_def, metis)
    apply (clarsimp simp add: opstep_iff le_fun_def, metis)
   apply (clarsimp simp add: opstep_iff le_fun_def, metis)
  apply (clarsimp simp add: opstep_iff le_fun_def, metis)
  done

lemma refinement_atomic_condition1:
  \<open>b' \<le> b \<Longrightarrow> sp b (wlp R P) s \<le> Q \<Longrightarrow> sp b' (wlp R P) s \<le> Q\<close>
  using sp_rel_mono
  by auto

lemma refinement_atomic_condition2:
  \<open>b' \<le> b \<Longrightarrow> unframe_prop f b \<Longrightarrow> unframe_prop f b'\<close>
  oops

end