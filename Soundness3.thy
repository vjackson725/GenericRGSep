theory Soundness3
  imports RGSep
begin


definition \<open>all_atom_comm2 p c1 c2 \<equiv> all_atom_comm (\<lambda>b1. all_atom_comm (\<lambda>b2. p b1 b2) c2) c1\<close>

lemma all_atom_comm2_commute:
  \<open>all_atom_comm2 p c1 c2 \<longleftrightarrow> all_atom_comm2 (\<lambda>x y. p y x) c2 c1\<close>
proof -
  {
    fix q
    assume
      \<open>all_atom_comm q c1\<close>
      \<open>q = (\<lambda>b1. all_atom_comm (p b1) c2)\<close>
    then have \<open>all_atom_comm (\<lambda>b1. all_atom_comm (\<lambda>b2. p b2 b1) c1) c2\<close>
      by (induct rule: all_atom_comm.induct) simp+
  }
  moreover {
    fix q
    assume
      \<open>all_atom_comm q c2\<close>
      \<open>q = (\<lambda>b1. all_atom_comm (\<lambda>b2. p b2 b1) c1)\<close>
    then have \<open>all_atom_comm (\<lambda>b1. all_atom_comm (p b1) c2) c1\<close>
      by (induct rule: all_atom_comm.induct) simp+
  }
  ultimately show ?thesis
    by (force simp add: all_atom_comm2_def)
qed 

lemma all_atom_comm2_simps[simp]:
  \<open>all_atom_comm2 p Skip cy \<longleftrightarrow> True\<close>
  \<open>all_atom_comm2 p (c1 ;; c2) cy \<longleftrightarrow> all_atom_comm2 p c1 cy \<and> all_atom_comm2 p c2 cy\<close>
  \<open>all_atom_comm2 p (c1 \<^bold>+ c2) cy \<longleftrightarrow> all_atom_comm2 p c1 cy \<and> all_atom_comm2 p c2 cy\<close>
  \<open>all_atom_comm2 p (c1 \<parallel> c2) cy \<longleftrightarrow> all_atom_comm2 p c1 cy \<and> all_atom_comm2 p c2 cy\<close>
  \<open>all_atom_comm2 p (c\<^sup>\<star>) cy \<longleftrightarrow> all_atom_comm2 p c cy\<close>
  \<open>all_atom_comm2 p (Atomic b1) cy \<longleftrightarrow> all_atom_comm (p b1) cy\<close>
  \<open>all_atom_comm2 p cx Skip \<longleftrightarrow> True\<close>
  \<open>all_atom_comm2 p cx (c1 ;; c2) \<longleftrightarrow> all_atom_comm2 p cx c1 \<and> all_atom_comm2 p cx c2\<close>
  \<open>all_atom_comm2 p cx (c1 \<^bold>+ c2) \<longleftrightarrow> all_atom_comm2 p cx c1 \<and> all_atom_comm2 p cx c2\<close>
  \<open>all_atom_comm2 p cx (c1 \<parallel> c2) \<longleftrightarrow> all_atom_comm2 p cx c1 \<and> all_atom_comm2 p cx c2\<close>
  \<open>all_atom_comm2 p cx (c\<^sup>\<star>) \<longleftrightarrow> all_atom_comm2 p cx c\<close>
  \<open>all_atom_comm2 p cx (Atomic b2) \<longleftrightarrow> all_atom_comm (\<lambda>b1. p b1 b2) cx\<close>
  by (clarsimp simp add: all_atom_comm2_def)+


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

lemma sp_rely_step:
  \<open>r y y' \<Longrightarrow>
    sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) p (x, y) \<Longrightarrow>
    sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) p (x, y')\<close>
  by (clarsimp simp add: sp_def,
      meson rtranclp.rtrancl_into_rtrancl)

declare eq_OO[simp] OO_eq[simp]

lemma rel_Times_comp[simp]:
  \<open>(a \<times>\<^sub>R b) OO (c \<times>\<^sub>R d) = (a OO c) \<times>\<^sub>R (b OO d)\<close>
  by (force simp add: fun_eq_iff OO_def)

lemmas sp_rely_stronger = sp_refl_rel_le[where r=\<open>(=) \<times>\<^sub>R r\<^sup>*\<^sup>*\<close> for r, simplified]
lemmas sp_rely_absorb =
  sp_comp_rel[where ?r1.0=\<open>(=) \<times>\<^sub>R ra\<^sup>*\<^sup>*\<close> and ?r2.0=\<open>(=) \<times>\<^sub>R rb\<^sup>*\<^sup>*\<close> for ra rb, simplified,
    symmetric]

lemma wlp_rely_step[dest]:
  \<open>wlp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) p (hl, hs) \<Longrightarrow>r hs hs' \<Longrightarrow> wlp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) p (hl, hs')\<close>
  by (simp add: converse_rtranclp_into_rtranclp wlp_def)

section \<open> Operational Semantics \<close>

subsection \<open> Actions \<close>

datatype act = Tau | Local

lemma act_not_eq_iff[simp]:
  \<open>a \<noteq> Tau \<longleftrightarrow> a = Local\<close>
  \<open>a \<noteq> Local \<longleftrightarrow> a = Tau\<close>
  by (meson act.distinct act.exhaust)+

subsection \<open> Operational semantics steps \<close>

inductive opstep :: \<open>act \<Rightarrow> ('h::perm_alg) \<times> 'h comm \<Rightarrow> ('h \<times> 'h comm) \<Rightarrow> bool\<close> where
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
    by force
qed

lemmas all_atom_comm_opstepD =
  all_atom_comm_opstep[rotated]

subsubsection \<open> Frame properties \<close>

definition
  \<open>local_frame_safe \<ff> \<equiv> \<lambda>r.
    \<forall>l s l' s' lf lf'.
      r (l,s) (l',s') \<longrightarrow> \<ff> lf lf' \<longrightarrow> l ## lf \<longrightarrow> l' ## lf' \<longrightarrow> r (l + lf,s) (l' + lf', s')\<close>

lemma local_frame_safe_framerel_antimonoD[dest]:
  \<open>\<ff>1 \<le> \<ff>2 \<Longrightarrow> local_frame_safe \<ff>2 r \<Longrightarrow> local_frame_safe \<ff>1 r\<close>
  by (force simp add: local_frame_safe_def)

lemma opstep_local_frame':
  \<open>s \<midarrow>a\<rightarrow> s' \<Longrightarrow>
    weak_framed_subresource_rel f (fst (fst s)) (fst (fst s')) lf lf' \<Longrightarrow>
    all_atom_comm (local_frame_safe (rel_lift f)) (snd s) \<Longrightarrow>
    ((lf, snd (fst s)), snd s) \<midarrow>a\<rightarrow> ((lf', snd (fst s')), snd s')\<close>
  apply (induct rule: opstep.inducts)
               apply (force simp add: opstep_iff ndet_local_left ndet_local_right
      weak_framed_subresource_rel_def)+
  apply (force simp add: weak_framed_subresource_rel_def framed_subresource_rel_def
      local_frame_safe_def)
  done

lemma opstep_local_frame:
  \<open>((l, s), c) \<midarrow>a\<rightarrow> ((l', s'), c') \<Longrightarrow>
    weak_framed_subresource_rel f l l' lf lf' \<Longrightarrow>
    all_atom_comm (local_frame_safe (rel_lift f)) c \<Longrightarrow>
    ((lf, s), c) \<midarrow>a\<rightarrow> ((lf', s'), c')\<close>
  by (metis fst_conv opstep_local_frame' snd_conv)

lemma opstep_local_frame2:
  \<open>((l, s), c) \<midarrow>a\<rightarrow> ((l', s'), c') \<Longrightarrow>
    framed_subresource_rel f l l' lf lf' \<Longrightarrow>
    all_atom_comm (local_frame_safe (rel_lift f)) c \<Longrightarrow>
    ((lf, s), c) \<midarrow>a\<rightarrow> ((lf', s'), c')\<close>
  using opstep_local_frame by blast


lemma opstep_sameheap_frameD:
  assumes
    \<open>s \<midarrow>a\<rightarrow> s'\<close>
    \<open>fst s' = fst s\<close>
    \<open>fst s ## hf\<close>
    \<open>all_atom_comm (frame_pred_closed ((=) hf)) (snd s)\<close>
  shows
    \<open>(fst s + hf, snd s) \<midarrow>a\<rightarrow> (fst s' + hf, snd s')\<close>
  using assms
  by (induct rule: opstep.induct)
    (force simp add: frame_pred_safe_def atomic frame_pred_closed_def)+

lemma opstep_sameheap_frame:
  assumes
    \<open>(h, c) \<midarrow>a\<rightarrow> (h, c')\<close>
    \<open>h ## hf\<close>
    \<open>all_atom_comm (frame_pred_closed ((=) hf)) c\<close>
  shows
    \<open>(h + hf, c) \<midarrow>a\<rightarrow> (h + hf, c')\<close>
  using assms opstep_sameheap_frameD
  by fastforce

lemma opstep_frame_closedD:
  assumes
    \<open>s \<midarrow>a\<rightarrow> s'\<close>
    \<open>all_atom_comm (frame_pred_closed ((=) hf)) (snd s)\<close>
    \<open>fst s ## hf\<close>
    \<open>fst s' ## hf\<close>
  shows
    \<open>(fst s + hf, snd s) \<midarrow>a\<rightarrow> (fst s' + hf, snd s')\<close>
  using assms
  by (induct rule: opstep.induct)
    (force simp add: frame_pred_closed_def)+

lemma opstep_frame_closed:
  assumes
    \<open>(h, c) \<midarrow>a\<rightarrow> (h', c')\<close>
    \<open>all_atom_comm (frame_pred_closed ((=) hf)) c\<close>
    \<open>h ## hf\<close>
    \<open>h' ## hf\<close>
  shows
    \<open>(h + hf, c) \<midarrow>a\<rightarrow> (h' + hf, c')\<close>
  using assms opstep_frame_closedD
  by fastforce

lemma opstep_frameD:
  assumes
    \<open>s \<midarrow>a\<rightarrow> s'\<close>
    \<open>all_atom_comm (frame_pred_safe (rel_lift ((=) hf))) (snd s)\<close>
    \<open>fst s ## hf\<close>
    \<open>fst s' ## hf\<close>
  shows
    \<open>(fst s + hf, snd s) \<midarrow>a\<rightarrow> (fst s' + hf, snd s')\<close>
  using assms
  by (induct rule: opstep.induct)
    (force simp add: frame_pred_safe_def)+

lemma opstep_frame:
  assumes
    \<open>(h, c) \<midarrow>a\<rightarrow> (h', c')\<close>
    \<open>all_atom_comm (frame_pred_safe (rel_lift ((=) hf))) c\<close>
    \<open>h ## hf\<close>
    \<open>h' ## hf\<close>
  shows
    \<open>(h + hf, c) \<midarrow>a\<rightarrow> (h' + hf, c')\<close>
  using assms opstep_frameD
  by fastforce

lemma opstep_frame_pred_extendsD:
  assumes
    \<open>s1 \<midarrow>a\<rightarrow> s2\<close>
    \<open>all_atom_comm (frame_pred_extends f) (snd s1)\<close>
    \<open>fst s1 ## hf\<close>
    \<open>f hf\<close>
  shows
    \<open>\<exists>hf'. f hf' \<and> fst s2 ## hf' \<and> (fst s1 + hf, snd s1) \<midarrow>a\<rightarrow> (fst s2 + hf', snd s2)\<close>
  using assms
  by (induct arbitrary: hf rule: opstep.inducts)
    (force simp add: frame_pred_extends_def)+

lemma opstep_frame_pred_extends:
  assumes
    \<open>(h, c) \<midarrow>a\<rightarrow> (h', c')\<close>
    \<open>all_atom_comm (frame_pred_extends f) c\<close>
    \<open>h ## hf\<close>
    \<open>f hf\<close>
  shows
    \<open>\<exists>hf'. f hf' \<and> h' ## hf' \<and> (h + hf, c) \<midarrow>a\<rightarrow> (h' + hf', c')\<close>
  using assms
  by (force dest: opstep_frame_pred_extendsD)


lemma opstep_frame_pred_maintainsD:
  assumes
    \<open>s1 \<midarrow>a\<rightarrow> s2\<close>
    \<open>all_atom_comm (frame_pred_maintains f) (snd s1)\<close>
    \<open>fst s1 ## hf\<close>
    \<open>f hf\<close>
  shows
    \<open>fst s2 ## hf \<and> (fst s1 + hf, snd s1) \<midarrow>a\<rightarrow> (fst s2 + hf, snd s2)\<close>
  using assms
  by (induct arbitrary: hf rule: opstep.inducts)
    (force simp add: frame_pred_maintains_def opstep_iff)+

lemma opstep_frame_pred_maintains:
  assumes
    \<open>(h, c) \<midarrow>a\<rightarrow> (h', c')\<close>
    \<open>all_atom_comm (frame_pred_maintains f) c\<close>
    \<open>h ## hf\<close>
    \<open>f hf\<close>
  shows
    \<open>(h + hf, c) \<midarrow>a\<rightarrow> (h' + hf, c')\<close>
  using assms opstep_frame_pred_maintainsD
  by fastforce

lemma opstep_frame_pred_maintains2:
  assumes
    \<open>(h, c) \<midarrow>a\<rightarrow> (h', c')\<close>
    \<open>all_atom_comm (frame_pred_maintains f) c\<close>
    \<open>h ## hf\<close>
    \<open>f hf\<close>
  shows
    \<open>h' ## hf\<close>
  using assms opstep_frame_pred_maintainsD
  by fastforce

subsubsection \<open> Opstep Unframe \<close>

lemma opstep_unframe':
  fixes s s' :: \<open>('a::cancel_perm_alg) \<times> 'a comm\<close>
  assumes
    \<open>s \<midarrow>a\<rightarrow> s'\<close>
    \<open>s = (h + hf, c)\<close>
    \<open>s' = (h' + hf, c')\<close>
    \<open>all_atom_comm (unframe_safe (rel_lift ((=) hf))) c\<close>
    \<open>h ## hf\<close>
    \<open>h' ## hf\<close>
  shows
    \<open>(h, c) \<midarrow>a\<rightarrow> (h', c')\<close>
  using assms
  apply -
  apply (induct arbitrary: h h' c c' hf rule: opstep.induct)
                apply (simp add: opstep_iff; fail)+ (* slow *)
  apply (simp add: opstep_iff unframe_safeD)
  done

lemma opstep_unframe_right:
  fixes h :: \<open>'a::cancel_perm_alg\<close>
  assumes
    \<open>(h + hf, c) \<midarrow>a\<rightarrow> (h' + hf, c')\<close>
    \<open>all_atom_comm (unframe_safe (rel_lift ((=) hf))) c\<close>
    \<open>h ## hf\<close>
    \<open>h' ## hf\<close>
  shows
    \<open>(h, c) \<midarrow>a\<rightarrow> (h', c')\<close>
  using assms opstep_unframe'
  by blast

lemma opstep_unframe_left:
  fixes h :: \<open>'a::cancel_perm_alg\<close>
  assumes
    \<open>(hf + h, c) \<midarrow>a\<rightarrow> (hf + h', c')\<close>
    \<open>all_atom_comm (unframe_safe (rel_lift ((=) hf))) c\<close>
    \<open>hf ## h\<close>
    \<open>hf ## h'\<close>
  shows
    \<open>(h, c) \<midarrow>a\<rightarrow> (h', c')\<close>
  using assms opstep_unframe'
  by (metis disjoint_sym_iff partial_add_commute)


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
    by force
qed

lemmas rev_opstep_preserves_all_atom_comm = opstep_preserves_all_atom_comm[rotated]


subsection \<open> Operational Semantics \<close>

inductive opsem
  :: \<open>act list \<Rightarrow> ('a::perm_alg) \<times> 'a comm \<Rightarrow> 'a \<times> 'a comm \<Rightarrow> bool\<close>
  where
  base[intro!]: \<open>opsem [] s s\<close>
| step[intro!]: \<open>s \<midarrow>a\<rightarrow> s' \<Longrightarrow> opsem as s' s'' \<Longrightarrow> opsem (a # as) s s''\<close>

inductive_cases opsem_NilE[elim!]: \<open>opsem [] s s'\<close>
inductive_cases opsem_ConsE[elim!]: \<open>opsem (a # as) s s'\<close>

lemma opsem_iff[simp]:
  \<open>opsem [] s s' \<longleftrightarrow> s' = s\<close>
  \<open>opsem (a # as) s s'' \<longleftrightarrow> (\<exists>s'. (s \<midarrow>a\<rightarrow> s') \<and> opsem as s' s'')\<close>
  by force+


(*
paragraph \<open> pretty opsem \<close>

abbreviation(input) pretty_opsem :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _\<close> (\<open>_ \<midarrow>(_)\<rightarrow>\<^sup>\<star> _\<close> [60,0,60] 60) where
  \<open>hc \<midarrow>as\<rightarrow>\<^sup>\<star> hc' \<equiv> opsem as hc hc'\<close>

subsection \<open> Theorems about the operational semantics \<close>

paragraph \<open> Reverse-cons transitive closure rules \<close>

lemma opsem_step_rev:
  \<open>opsem as s s' \<Longrightarrow> s' \<midarrow>a\<rightarrow> s'' \<Longrightarrow> opsem (as @ [a]) s s''\<close>
  apply (induct rule: opsem.induct)
   apply (metis append_self_conv2 opsem.simps)
  apply force
  done

lemma opsem_step_revE:
  \<open>opsem (as @ [a]) s s'' \<Longrightarrow> (\<And>s'. opsem as s s' \<Longrightarrow> opstep a s' s'' \<Longrightarrow> P) \<Longrightarrow> P\<close>
  by (induct as arbitrary: a s s'')
    (simp, blast)+

lemma opsem_rev_cons_iff[simp]:
  \<open>opsem (as @ [a]) s s'' \<longleftrightarrow> (\<exists>s'. opsem as s s' \<and> (s' \<midarrow>a\<rightarrow> s''))\<close>
  by (meson opsem_step_rev opsem_step_revE)

lemma opsem_rev_induct[consumes 1, case_names Nil Snoc]:
  \<open>opsem as s s' \<Longrightarrow>
    (\<And>r s. P r [] s s) \<Longrightarrow>
    (\<And>s r a s' as s''.
      opsem as s s' \<Longrightarrow>
      opstep a s' s'' \<Longrightarrow>
      P r as s s' \<Longrightarrow>
      P r (as @ [a]) s s'') \<Longrightarrow>
    P r as s s'\<close>
  by (induct as arbitrary: s s' rule: rev_induct) force+

lemma opsem_stepI:
  \<open>s \<midarrow>a\<rightarrow> s' \<Longrightarrow> s \<midarrow>[a]\<rightarrow>\<^sup>\<star> s'\<close>
  by blast

lemma opsem_trans:
  \<open>s \<midarrow>as1\<rightarrow>\<^sup>\<star> s' \<Longrightarrow> s' \<midarrow>as2\<rightarrow>\<^sup>\<star> s'' \<Longrightarrow> s \<midarrow>as1 @ as2\<rightarrow>\<^sup>\<star> s''\<close>
  by (induct arbitrary: as2 s'' rule: opsem.induct)
    force+

lemma skipped_opsem_only_env:
  \<open>s \<midarrow>as\<rightarrow>\<^sup>\<star> s' \<Longrightarrow> snd s = Skip \<Longrightarrow> as = []\<close>
  by (induct rule: opsem.induct)
    (force elim: opstep.cases)+

inductive opstep_trancl :: \<open>act list \<Rightarrow> ('h::perm_alg) \<times> 'h comm \<Rightarrow> ('h \<times> 'h comm) \<Rightarrow> bool\<close> where
  step1[intro!]: \<open>opstep a s s' \<Longrightarrow> opstep_trancl [a] s s'\<close>
| step[intro!]: \<open>opstep a s s' \<Longrightarrow> opstep_trancl as s' s'' \<Longrightarrow> opstep_trancl (a # as) s s''\<close>

inductive opstep_rtrancl :: \<open>act list \<Rightarrow> ('h::perm_alg) \<times> 'h comm \<Rightarrow> ('h \<times> 'h comm) \<Rightarrow> bool\<close> where
  refl[intro!]: \<open>opstep_rtrancl [] s s\<close>
| step[intro!]: \<open>opstep a s s' \<Longrightarrow> opstep_rtrancl as s' s'' \<Longrightarrow> opstep_rtrancl (a # as) s s''\<close>

paragraph \<open> Pretty operational semantics \<close>

abbreviation(input) pretty_opstep_trancl :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _\<close> (\<open>_ \<midarrow>(_)\<rightarrow>\<^sup>+ _\<close> [60,0,60] 60) where
  \<open>hs \<midarrow>as\<rightarrow>\<^sup>+ ht \<equiv> opstep_trancl as hs ht\<close>

abbreviation(input) pretty_opstep_rtrancl :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _\<close> (\<open>_ \<midarrow>(_)\<rightarrow>\<^sup>\<star> _\<close> [60,0,60] 60) where
  \<open>hs \<midarrow>as\<rightarrow>\<^sup>\<star> ht \<equiv> opstep_rtrancl as hs ht\<close>
*)


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
  by (force simp add: WhileLoop_def opstep_iff)

lemma opstep_WhileLoop_true[intro]:
  \<open>p h \<Longrightarrow> opstep Tau (h, WhileLoop p c) (h, (((Assert p ;; c) ;; (Assert p ;; c)\<^sup>\<star>) ;; Assert (-p)))\<close>
  by (simp add: opstep_iff)

lemma opstep_WhileLoop_false[intro]:
  \<open>\<not> p h \<Longrightarrow> opstep Tau (h, WhileLoop p c) (h, (((Assert p ;; c) ;; (Assert p ;; c)\<^sup>\<star>) ;; Assert (-p)))\<close>
  by (simp add: opstep_iff)


section \<open> Safe \<close>

inductive safe
  :: \<open>nat \<Rightarrow> (('l::perm_alg) \<times> ('s::perm_alg)) comm \<Rightarrow>
      'l \<Rightarrow> 's \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('l \<times> 's \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where
  safe_nil[intro!]: \<open>safe 0 c hl hs r g q\<close>
| safe_suc[intro]:
  \<open>\<comment> \<open> if the command is Skip, the postcondition is established \<close>
    (c = Skip \<longrightarrow> q (hl, hs)) \<Longrightarrow>
    \<comment> \<open> rely steps are safe \<close>
    (\<And>hs'. r hs hs' \<comment> \<open> \<and> hl ## hs' \<close> \<Longrightarrow> safe n c hl hs' r g q) \<Longrightarrow>
    \<comment> \<open>
      \<comment> \<open> stuttering steps are safe \<close>
      (\<And>hs'. r hs hs' \<Longrightarrow> safe n c hl hs' r g q) \<Longrightarrow>
    \<close>
    \<comment> \<open> opsteps respect opsteps + the guarantee \<close>
    (\<And>a hlf hsf c' hx'.
       ((hl + hlf, hs + hsf), c) \<midarrow>a\<rightarrow> (hx', c') \<Longrightarrow>
       hl ## hlf \<Longrightarrow>
       hs ## hsf \<Longrightarrow>
       (\<exists>hl' hs' hsf'.
          hx' = (hl' + hlf, hs' + hsf') \<and>
          hl' ## hlf \<and>
          hs' ## hsf' \<and>
          g hs hs' \<and>
          g hsf hsf' \<and>
          g (hs + hsf) (hs' + hsf') \<and>
          safe n c' hl' hs' r g q)) \<Longrightarrow>
    \<comment> \<open> conclude a step can be made \<close>
    safe (Suc n) c hl hs r g q\<close>

inductive_cases safe_zeroE[elim!]: \<open>safe 0 c hl hs r g q\<close>
inductive_cases safe_sucE[elim]: \<open>safe (Suc n) c hl hs r g q\<close>

subsection \<open> Proofs about safe \<close>

lemma safe_nil_iff[simp]:
  \<open>safe 0 c hl hs r g q \<longleftrightarrow> True\<close>
  by force

lemma safe_suc_iff:
  \<open>safe (Suc n) c hl hs r g q \<longleftrightarrow>
    (c = Skip \<longrightarrow> q (hl, hs)) \<and>
    (\<forall>hs'. r hs hs' \<longrightarrow> safe n c hl hs' r g q) \<and>
    (\<forall>a hlf hsf c' hx'.
       ((hl + hlf, hs + hsf), c) \<midarrow>a\<rightarrow> (hx', c') \<longrightarrow>
       hl ## hlf \<longrightarrow>
       hs ## hsf \<longrightarrow>
       (\<exists>hl' hs' hsf'.
          hx' = (hl' + hlf, hs' + hsf') \<and>
          hl' ## hlf \<and>
          hs' ## hsf' \<and>
          g hs hs' \<and>
          g hsf hsf' \<and>
          g (hs + hsf) (hs' + hsf') \<and>
          safe n c' hl' hs' r g q))\<close>
  apply (rule iffI)
   apply (erule safe_sucE, presburger)
  apply (rule safe_suc; presburger)
  done


subsubsection \<open> Monotonicity \<close>

lemma safe_postpred_monoD:
  \<open>safe n c hl hs r g q \<Longrightarrow> q \<le> q' \<Longrightarrow> safe n c hl hs r g q'\<close>
  apply (induct rule: safe.induct)
   apply blast
  apply (simp add: le_fun_def safe_suc_iff, fast)
  done

lemmas safe_postpred_mono = safe_postpred_monoD[rotated]

lemma safe_guarantee_monoD:
  \<open>safe n c hl hs r g q \<Longrightarrow> g \<le> g' \<Longrightarrow> safe n c hl hs r g' q\<close>
  apply (induct rule: safe.induct)
   apply blast
  apply (simp add: le_fun_def)
  apply (rule safe_suc; metis)
  done

lemmas safe_guarantee_mono = safe_guarantee_monoD[rotated]

lemma safe_rely_antimonoD:
  \<open>safe n c hl hs r g q \<Longrightarrow> r' \<le> r \<Longrightarrow> safe n c hl hs r' g q\<close>
  apply (induct rule: safe.induct)
   apply force
  apply (rule safe_suc; fast)
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
    apply fast
   apply fast
  apply fast
  done


subsubsection \<open> Skip \<close>

lemma safe_skip':
  \<open>sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) q (hl, hs) \<Longrightarrow> safe n Skip hl hs r g (sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) q)\<close>
  apply (induct n arbitrary: hl hs q)
   apply force
  apply (subst safe_suc_iff)
  apply (clarsimp simp add: sp_def)
  apply (meson opstep_skipE rtranclp.rtrancl_into_rtrancl; fail)
  done

lemma safe_skip:
  \<open>p (hl, hs) \<Longrightarrow> sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) p \<le> q \<Longrightarrow> safe n Skip hl hs r g q\<close>
  apply (rule safe_postpred_monoD[OF safe_skip'[where q=p]])
   apply (metis (mono_tags, lifting) rel_Times_iff rtranclp.rtrancl_refl sp_def)
  apply blast
  done


subsubsection \<open> Atomic \<close>

lemma rel_lift_impl_iff_sp_impl:
  \<open>rel_liftL p \<sqinter> b \<le> rel_liftR q \<longleftrightarrow> sp b p \<le> q\<close>
  by (force simp add: le_fun_def sp_def wlp_def pre_state_def)


lemma safe_atom':
  \<open>rel_liftL (wlp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) p) \<sqinter> b \<le> rel_liftR q \<Longrightarrow>
    wlp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) p (hl, hs) \<Longrightarrow>
    (\<forall>hlf hs2 hsf hx'.
      r\<^sup>*\<^sup>* hs hs2 \<longrightarrow>
      b (hl + hlf, hs2 + hsf) hx' \<longrightarrow>
      hl ## hlf \<longrightarrow>
      hs2 ## hsf \<longrightarrow>
      (\<exists>hl'. fst hx' = hl' + hlf \<and>
        (\<exists>hs' hsf'.
          snd hx' = hs' + hsf' \<and>
          hl' ## hlf \<and>
          hs' ## hsf' \<and>
          g hs2 hs' \<and>
          g hsf hsf' \<and>
          g (hs2 + hsf) (hs' + hsf')))) \<Longrightarrow>
    \<comment> \<open> TODO: review this assumption \<close>
    (\<forall>hl' hlf hsf hs' hsf' hs2. 
      r\<^sup>*\<^sup>* hs hs2 \<longrightarrow>
      b (hl + hlf, hs2 + hsf) (hl' + hlf, hs' + hsf') \<longrightarrow>
      hl' ## hlf \<longrightarrow>
      hs' ## hsf' \<longrightarrow>
      g hs2 hs' \<longrightarrow>
      g hsf hsf' \<longrightarrow>
      b (hl, hs2) (hl', hs')) \<Longrightarrow>
    safe n (Atomic b) hl hs r g (sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) q)\<close>
proof (induct n arbitrary: hl hs)
  case 0
  then show ?case by force
next
  case (Suc n)
  show ?case
    using Suc.prems
    apply (intro safe.safe_suc)
      apply force
     apply (rule Suc.hyps, fast, fast, meson converse_rtranclp_into_rtranclp,
        meson converse_rtranclp_into_rtranclp)
    apply (subst (asm) rel_lift_impl_iff_sp_impl)
    apply clarsimp
    apply (drule spec, drule mp, rule rtranclp.rtrancl_refl)
    apply (drule spec2, drule spec2, drule mp, assumption)
    apply clarsimp
    apply (rule_tac x=hl' in exI, simp)
    apply (rule_tac x=hs' in exI, rule_tac x=hsf' in exI, simp)
    apply (rule safe_skip[where p=\<open>sp b (wlp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) p)\<close>, rotated])
     apply (clarsimp simp add: rel_Times_def)
     apply (rule sp_mono2, assumption)
     apply (rule subst[of _ _ \<open>\<lambda>x. sp x p s\<close> for p s, rotated], fast)
     apply fastforce
    apply (simp add: sp_def)
    apply (meson Suc.prems(2) rtranclp.rtrancl_refl)
    done
qed


subsubsection \<open> Sequencing \<close>

lemma safe_seq_assoc_left:
  \<open>safe n c hl hs r g q \<Longrightarrow>
    all_atom_comm (local_frame_safe (=)) c1 \<Longrightarrow>
    c = (c1 ;; c2 ;; c3) \<Longrightarrow>
    safe n ((c1 ;; c2) ;; c3) hl hs r g q\<close>
  apply (induct arbitrary: c1 c2 c3 rule: safe.inducts)
   apply force
  apply (rule safe_suc)
    apply blast
   apply blast
  apply (clarsimp simp add: opstep_iff)
  apply (elim disjE conjE exE)
   apply metis
  sledgehammer
  oops

lemma safe_seq_assoc_right:
  \<open>safe n c hl hs r g q \<Longrightarrow>
    all_atom_comm (local_frame_safe (=)) c1 \<Longrightarrow>
    c = ((c1 ;; c2) ;; c3) \<Longrightarrow>
    safe n (c1 ;; c2 ;; c3) hl hs r g q\<close>
  apply (induct arbitrary: c1 c2 c3 rule: safe.inducts)
   apply force
  apply (subst safe_suc_iff)
  apply (simp add: opstep_iff)
  apply (intro conjI impI allI)
         apply metis
        apply metis
       apply metis
      apply metis
     apply metis
    apply (metis (no_types) weak_framed_subresource_rel_def framed_subresource_rel_def)
   apply (clarify, metis comm.inject(1) opstep_iff(1)) (* slow *)
  apply (metis opstep_preserves_all_atom_comm)
  done

lemma safe_seq':
  \<open>safe n c1 hl hs r g q \<Longrightarrow>
    (\<forall>m hl' hs'. m \<le> n \<longrightarrow> q (hl', hs') \<longrightarrow> safe m c2 hl' hs' r g q') \<Longrightarrow>
    safe n (c1 ;; c2) hl hs r g q'\<close>
  apply (induct arbitrary: c2 q' rule: safe.inducts)
   apply force
  apply (rule safe_suc)
        apply blast
       apply (clarsimp simp add: opstep_iff, (elim disjE exE conjE; force))
      apply (simp add: opstep_iff, metis)
     apply (simp add: opstep_iff, metis)
    apply (simp add: opstep_iff weak_framed_subresource_rel_def framed_subresource_rel_def, metis)
   apply (simp add: opstep_iff, (elim disjE exE conjE; force))
  apply force
  done

lemma safe_seq:
  \<open>safe n c1 hl hs r g q \<Longrightarrow>
    (\<forall>hl' hs'. q (hl', hs') \<longrightarrow> safe n c2 hl' hs' r g q') \<Longrightarrow>
    safe n (c1 ;; c2) hl hs r g q'\<close>
  by (rule safe_seq', fast, metis safe_step_monoD)

subsection \<open> Iteration \<close>

lemma safe_iter':
  \<open>(\<forall>m hl' hs'. m \<le> n \<longrightarrow> sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) i (hl', hs') \<longrightarrow> safe m c hl' hs' r g (sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) i)) \<Longrightarrow>
    sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) i (hl, hs) \<Longrightarrow>
    safe n (c\<^sup>\<star>) hl hs r g (sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) i)\<close>
  apply (induct n arbitrary: i hl hs)
   apply force
  apply (rule safe_suc)
        apply blast
       apply (force simp add: opstep_iff)
      apply (force simp add: opstep_iff)
     apply (force simp add: opstep_iff)
    apply (force simp add: opstep_iff weak_framed_subresource_rel_def)
    (* subgoal *)
   apply (simp add: le_Suc_eq opstep_iff)
   apply (elim disjE)
    apply (simp add: safe_skip'; fail)
   apply (clarsimp simp add: all_conj_distrib)
   apply (rule_tac q=\<open>sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) i\<close> in safe_seq; blast)
    (* done *)
  apply (simp add: le_Suc_eq all_conj_distrib sp_rely_step)
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


subsubsection \<open> Nondeterminism \<close>

lemma safe_ndet:
  \<open>\<forall>m\<le>n. safe m c1 hl hs r g q \<Longrightarrow>
    \<forall>m\<le>n. safe m c2 hl hs r g q \<Longrightarrow>
    safe n (c1 \<^bold>+ c2) hl hs r g q\<close>
proof (induct n arbitrary: c1 c2 hl hs)
  case 0
  then show ?case by blast
next
  case (Suc n)

  have c1_Suc:
    \<open>c1 = Skip \<longrightarrow> q (hl, hs)\<close>
    \<open>\<And>c' hl' hs'. opstep Tau ((hl, hs), c1) ((hl', hs'), c') \<Longrightarrow> hl = hl' \<and> hs = hs'\<close>
    \<open>\<And>c' hl' hs'. opstep Local ((hl, hs), c1) ((hl', hs'), c') \<Longrightarrow> g hs hs'\<close>
    \<open>\<And>c' hl' hsf hsx'.
        hs ## hsf \<Longrightarrow>
        opstep Local ((hl, hs + hsf), c1) ((hl', hsx'), c') \<Longrightarrow>
        g (hs + hsf) hsx' \<and> (\<exists>hs' hsf'. hs' ## hsf' \<and> hsx' = hs' + hsf' \<and> g hs hs' \<and> g hsf hsf')\<close>
    \<open>\<And>a c' hl' hs' hlb hlb' hf.
        opstep a ((hl, hs), c1) ((hl', hs'), c') \<Longrightarrow>
        weak_framed_subresource_rel ((=) hf) hl hl' hlb hlb' \<Longrightarrow> opstep a ((hlb, hs), c1) ((hlb', hs'), c')\<close>
    \<open>\<And>a c' hl' hs'. opstep a ((hl, hs), c1) ((hl', hs'), c') \<Longrightarrow> safe n c' hl' hs' r g q\<close>
    \<open>\<And>hs'. r hs hs' \<Longrightarrow> safe n c1 hl hs' r g q\<close>
    using Suc.prems(1)
    by (clarsimp simp add: le_Suc_eq all_conj_distrib, elim safe_sucE, metis)+

  have c2_Suc:
    \<open>c2 = Skip \<longrightarrow> q (hl, hs)\<close>
    \<open>\<And>c' hl' hs'. opstep Tau ((hl, hs), c2) ((hl', hs'), c') \<Longrightarrow> hl = hl' \<and> hs = hs'\<close>
    \<open>\<And>c' hl' hs'. opstep Local ((hl, hs), c2) ((hl', hs'), c') \<Longrightarrow> g hs hs'\<close>
     \<open>\<And>c' hl' hsf hsx'.
        hs ## hsf \<Longrightarrow>
        opstep Local ((hl, hs + hsf), c2) ((hl', hsx'), c') \<Longrightarrow>
        g (hs + hsf) hsx' \<and> (\<exists>hs' hsf'. hs' ## hsf' \<and> hsx' = hs' + hsf' \<and> g hs hs' \<and> g hsf hsf')\<close>
    \<open>\<And>a c' hl' hs' hlb hlb' hf.
        opstep a ((hl, hs), c2) ((hl', hs'), c') \<Longrightarrow>
        weak_framed_subresource_rel ((=) hf) hl hl' hlb hlb' \<Longrightarrow> opstep a ((hlb, hs), c2) ((hlb', hs'), c')\<close>
    \<open>\<And>a c' hl' hs'. opstep a ((hl, hs), c2) ((hl', hs'), c') \<Longrightarrow> safe n c' hl' hs' r g q\<close>
    \<open>\<And>hs'. r hs hs' \<Longrightarrow> safe n c2 hl hs' r g q\<close>
    using Suc.prems(2)
    by (clarsimp simp add: le_Suc_eq all_conj_distrib, elim safe_sucE, metis)+

  have
    \<open>\<forall>m\<le>n. safe m c1 hl hs r g q\<close>
    \<open>\<forall>m\<le>n. safe m c2 hl hs r g q\<close>
    using Suc.prems
    by simp+
  then show ?case
    apply -
    apply (rule safe_suc)
          apply blast
         apply (rule opstep_act_cases)
           apply blast
          apply (force simp add: opstep_iff)
         apply (force simp add: opstep_iff)
        apply (simp add: opstep_iff, metis c1_Suc(3) c2_Suc(3))
       apply (simp add: opstep_iff, metis c1_Suc(4) c2_Suc(4))
    subgoal
      apply (simp add: opstep_iff)
      apply (elim disjE exE conjE)
           apply (metis c1_Suc(5))
          apply (metis c2_Suc(5))
         apply (metis c1_Suc(5))
        apply (metis c2_Suc(5))
       apply (metis framed_subresource_rel_top_same_sub_iff weak_framed_subresource_rel_def)
      apply (metis framed_subresource_rel_top_same_sub_iff weak_framed_subresource_rel_def)
      done
    subgoal
      apply (simp add: opstep_iff)
      apply (elim disjE exE conjE)
           apply (metis c1_Suc(6))
          apply (metis c2_Suc(6))
         apply (frule c1_Suc(2), drule c1_Suc(6), meson Suc.hyps safe_step_monoD; fail)
        apply (frule c2_Suc(2), drule c2_Suc(6), meson Suc.hyps safe_step_monoD; fail)
       apply force
      apply force
      done
    apply (meson Suc.hyps c1_Suc(7) c2_Suc(7) safe_step_monoD)
    done
qed


subsubsection \<open> Frame rule \<close>

lemma opstep_strong_unframe_right:
  \<open>opstep a s s' \<Longrightarrow>
    s = (hx + hf, c) \<Longrightarrow>
    s' = (h', c') \<Longrightarrow>
    hx ## hf \<Longrightarrow>
    all_atom_comm (strong_unframe_safe (rel_lift f)) c \<Longrightarrow>
    f hf \<Longrightarrow>
    (\<exists>hx' hf'. f hf' \<and> hx' ## hf' \<and> h' = hx' + hf' \<and> opstep a (hx, c) (hx', c'))\<close>
  apply (induct arbitrary: hx hf c h' c' rule: opstep.inducts)
               apply (blast+)[13]
  apply (simp add: opstep_iff rel_lift_def inf_fun_def)
  apply (drule_tac strong_unframe_safeD, blast, blast)
  apply blast
  done

lemma opstep_strong_unframe_left:
  \<open>opstep a s s' \<Longrightarrow>
    s = (hf + hx, c) \<Longrightarrow>
    s' = (h', c') \<Longrightarrow>
    hf ## hx \<Longrightarrow>
    all_atom_comm (strong_unframe_safe (rel_lift f)) c \<Longrightarrow>
    f hf \<Longrightarrow>
    (\<exists>hx' hf'. f hf' \<and> hf' ## hx' \<and> h' = hf' + hx' \<and> opstep a (hx, c) (hx', c'))\<close>
  by (metis disjoint_sym_iff opstep_strong_unframe_right partial_add_commute)

lemma safe_frame:
  \<open>safe n c hl hs r g q \<Longrightarrow>
    all_atom_comm (strong_unframe_safe (rel_lift f)) c \<Longrightarrow>
    hl ## hlf \<Longrightarrow>
    hs ## hsf \<Longrightarrow>
    f (hlf, hsf) \<Longrightarrow>
    safe n c (hl + hlf) (hs + hsf) r g (q \<^emph> f)\<close>
proof (induct arbitrary: hlf hsf rule: safe.induct)
  case (safe_nil c hl hs r g q)
  then show ?case by blast
next
  case (safe_suc c q hl hs g n r)
  show ?case
    using safe_suc.hyps(1) safe_suc.prems
    apply -
    apply (rule safe.safe_suc)
          apply (clarsimp simp add: sepconj_def, fast)
         apply (metis fst_conv opstep_tau_preserves_heap)
        apply (frule opstep_strong_unframe_right[where hx=\<open>(hl, hs)\<close> and hf=\<open>(hlf, hsf)\<close>])
             apply (simp; fail)
            apply (simp; fail)
           apply (simp; fail)
          apply blast
         apply blast
        apply clarsimp

    sorry
qed

(*
lemma safe_frame2:
  \<open>safe n c hl hs r g q \<Longrightarrow>
    all_atom_comm (frame_pred_maintains f) c \<Longrightarrow>
    frame_pred_extends f r \<Longrightarrow>
    frame_pred_closed f g \<Longrightarrow>
    h ## hf \<Longrightarrow>
    f hf \<Longrightarrow>
    safe n c (h + hf) r g (q \<^emph> f)\<close>
proof (induct arbitrary: hf rule: safe.induct)
  case safe_nil
  then show ?case by fast
next
  case (safe_step h c a h' c' g q n r)

  have
    \<open>h' ## hf\<close>
    \<open>opstep a (h + hf, c) (h' + hf, c')\<close>
    using safe_step opstep_frame_pred_maintains opstep_frame_pred_maintains2
    by meson+
  moreover then have \<open>safe n c' (h' + hf) r g (q \<^emph> f)\<close>
    using safe_step
    by (blast dest: opstep_preserves_all_atom_comm)
  ultimately show ?case
    using safe_step.prems safe_step.hyps(1-5)
    apply -
    apply (rule safe.safe_step)
        apply assumption
       apply (blast intro: opstep_frame)
      apply (simp add: frame_pred_closed_def; fail)
     apply (metis sepconj_def)
    apply force
    done
qed
*)


subsubsection \<open> Parallel \<close>

lemma framed_subresource_rel_frame_extend_right:
  \<open>\<forall>x. p x \<longrightarrow> x ## hf \<and> p (x + hf) \<Longrightarrow>
    h ## hf \<Longrightarrow>
    h' ## hf \<Longrightarrow>
    framed_subresource_rel p hs hs' h h' \<Longrightarrow>
    framed_subresource_rel p hs hs' (h + hf) (h' + hf)\<close>
  by (clarsimp simp add: framed_subresource_rel_def le_iff_sepadd_weak)
    (meson disjoint_add_swap2 partial_add_assoc2)

lemma framed_subresource_rel_frame_extend_left:
  \<open>\<forall>x. p x \<longrightarrow> hf ## x \<and> p (hf + x) \<Longrightarrow>
    hf ## h \<Longrightarrow>
    hf ## h' \<Longrightarrow>
    framed_subresource_rel p hs hs' h h' \<Longrightarrow>
    framed_subresource_rel p hs hs' (hf + h) (hf + h')\<close>
  using framed_subresource_rel_frame_extend_right
  by (metis disjoint_sym_iff partial_add_commute)




lemma (in perm_alg)
  \<open>x ## y \<Longrightarrow> core_rel x x \<Longrightarrow> core_rel y y \<Longrightarrow> core_rel (x + y) (x + y)\<close>
  unfolding sepadd_dup_def core_rel_def
  by (metis disjoint_add_swap disjoint_middle_swap order_refl partial_add_double_assoc)

lemma (in perm_alg)
  \<open>x ## y \<Longrightarrow> core_rel x cx \<Longrightarrow> core_rel y cy \<Longrightarrow> core_rel (x + y) cxy \<Longrightarrow> cx + cy \<le> cxy\<close>
  unfolding sepadd_dup_def core_rel_def
  by (metis (mono_tags, opaque_lifting) disjoint_preservation2 disjoint_sym_iff order.trans
      partial_add_commute partial_le_plus2 sepadd_right_mono)

lemma wframe_with_top:
  \<open>(wframe r with \<top>) h h'
    \<longleftrightarrow> (r h h' \<or> (\<exists>hx hx' hf. hx ## hf \<and> hx' ## hf \<and> r hx hx' \<and> h = hx + hf \<and> h' = hx' + hf))\<close>
  by (force simp add: wframe_with_def weak_framed_subresource_rel_def framed_subresource_rel_def)

lemma wframe_with_top':
  fixes h h' :: \<open>'a::sep_alg\<close>
  shows \<open>(wframe r with \<top>) h h' \<longleftrightarrow>
    (\<exists>hx hx' hf. hx ## hf \<and> hx' ## hf \<and> r hx hx' \<and> h = hx + hf \<and> h' = hx' + hf)\<close>
  by (fastforce simp add: wframe_with_top)

lemma pre_state_wframe_with_top':
  fixes h h' :: \<open>'a::sep_alg\<close>
  shows \<open>pre_state (wframe r with \<top>) h \<longleftrightarrow>
    (\<exists>h' hx hx' hf. hx ## hf \<and> hx' ## hf \<and> r hx hx' \<and> h = hx + hf \<and> h' = hx' + hf)\<close>
  by (fastforce simp add: pre_state_def wframe_with_top)


definition
  \<open>strong_local_unframe_safe \<ff> r \<equiv>
    \<forall>x z xz' s s'.
      Ex (\<ff> z) \<longrightarrow>
      r (x+z, s) (xz', s') \<longrightarrow> x ## z \<longrightarrow>
      (\<exists>x' z'. \<ff> z z' \<and> x' ## z' \<and> xz' = x' + z') \<and> (\<exists>x''. r (x, s) (x'', s'))\<close>

lemma strong_unframe_safeD:
  \<open>strong_local_unframe_safe \<ff> r \<Longrightarrow> 
    Ex (\<ff> z) \<Longrightarrow> x ## z \<Longrightarrow> r (x+z, s) (xz', s') \<Longrightarrow>
    (\<exists>x' z'. \<ff> z z' \<and> x' ## z' \<and> xz' = x' + z') \<and> (\<exists>x''. r (x, s) (x'', s'))\<close>
  by (simp add: strong_local_unframe_safe_def)

lemma strong_unframe_safe_mono:
  \<open>\<ff>1 \<le> \<ff>2 \<Longrightarrow> \<forall>x. \<ff>1 x \<ge> \<ff>2 x \<Longrightarrow> strong_local_unframe_safe \<ff>1 r \<Longrightarrow> strong_local_unframe_safe \<ff>2 r\<close>
  by (simp add: strong_local_unframe_safe_def post_state_def le_fun_def, meson)


lemma opstep_local_unframe':
  \<open>s \<midarrow>a\<rightarrow> s' \<Longrightarrow>
    all_atom_comm (strong_local_unframe_safe \<ff>) (snd s) \<Longrightarrow>
    \<ff> hf hf \<Longrightarrow>
    hl ## hf \<Longrightarrow>
    fst (fst s) = hl + hf \<Longrightarrow>
    (\<exists>hl' hf'.
      hl' ## hf' \<and>
      \<ff> hf hf' \<and>
      fst (fst s') = hl' + hf') \<and>
    (\<exists>hl''. ((hl, snd (fst s)), snd s) \<midarrow>a\<rightarrow> ((hl'', snd (fst s')), snd s'))\<close>
  apply (induct rule: opstep.inducts)
               apply fastforce
              apply fastforce
             apply (force dest: reflp_onD)
            apply (force dest: reflp_onD)
           apply fastforce
          apply fastforce
         apply (force dest: reflp_onD)
        apply (force dest: reflp_onD)
       apply fastforce
      apply fastforce
     apply fastforce
    apply fastforce
   apply fastforce
  apply (fastforce simp add: strong_local_unframe_safe_def local_frame_safe_def)
  done

lemma opstep_local_unframe_right:
  \<open>((hl + hf, hs), c) \<midarrow>a\<rightarrow> ((hlf', hs'), c') \<Longrightarrow>
    all_atom_comm (strong_local_unframe_safe \<ff>) c \<Longrightarrow>
    \<ff> hf hf \<Longrightarrow>
    hl ## hf \<Longrightarrow>
    (\<exists>hl' hf'.
      hl' ## hf' \<and>
      hlf' = hl' + hf' \<and>
      \<ff> hf hf') \<and>
    (\<exists>hl''. ((hl, hs), c) \<midarrow>a\<rightarrow> ((hl'', hs'), c'))\<close>
  using opstep_local_unframe' by fastforce

lemma opstep_local_unframe_left:
  \<open>((hf + hl, hs), c) \<midarrow>a\<rightarrow> ((hlf', hs'), c') \<Longrightarrow>
    all_atom_comm (strong_local_unframe_safe \<ff>) c \<Longrightarrow>
    \<ff> hf hf \<Longrightarrow>
    hf ## hl \<Longrightarrow>
    (\<exists>hl' hf'.
      hf' ## hl' \<and>
      hlf' = hf' + hl' \<and>
      \<ff> hf hf') \<and>
    (\<exists>hl''. ((hl, hs), c) \<midarrow>a\<rightarrow> ((hl'', hs'), c'))\<close>
  apply (subst (asm) partial_add_commute, blast)
  apply (drule disjoint_sym)
  apply (drule opstep_local_unframe_right, blast, blast, blast)
  apply (meson disjoint_sym_iff partial_add_commute)
  done


lemma safe_parallel_skip:
  \<open>safe n Skip hl1 hs1 (r \<squnion> g2) g1 (sp ((=) \<times>\<^sub>R (r \<squnion> g2)\<^sup>*\<^sup>*) q1) \<Longrightarrow>
    safe n Skip hl2 hs2 (r \<squnion> g1) g2 (sp ((=) \<times>\<^sub>R (r \<squnion> g1)\<^sup>*\<^sup>*) q2) \<Longrightarrow>
    hl1 ## hl2 \<Longrightarrow>
    hs1 ## hs2 \<Longrightarrow>
    weak_rel_add_preserve ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) (sp ((=) \<times>\<^sub>R (r \<squnion> g2)\<^sup>*\<^sup>*) q1) (sp ((=) \<times>\<^sub>R (r \<squnion> g1)\<^sup>*\<^sup>*) q2) \<Longrightarrow>
    safe n Skip (hl1 + hl2) (hs1 + hs2) r (g1 \<squnion> g2)
      (sp ((=) \<times>\<^sub>R (r \<squnion> g2)\<^sup>*\<^sup>*) q1 \<^emph> sp ((=) \<times>\<^sub>R (r \<squnion> g1)\<^sup>*\<^sup>*) q2)\<close>
  apply (induct n arbitrary: hl1 hl2 hs1 hs2)
   apply force
  apply (elim safe_sucE)
  apply (rule safe_skip[where p=\<open>(sp ((=) \<times>\<^sub>R (r \<squnion> g2)\<^sup>*\<^sup>*) q1 \<^emph> sp ((=) \<times>\<^sub>R (r \<squnion> g1)\<^sup>*\<^sup>*) q2)\<close>])
   apply (simp add: sepconj_def, blast)
  apply (rule order.trans)
   apply (rule sp_sepconj_semidistrib, blast)
  apply (simp add: weak_framed_rel_mono sp_rely_absorb rel_le_rtranscp_relcompp_absorb)
  done


lemma disjoint_map_insert_fresh_iff[simp]:
  \<open>b x = None \<Longrightarrow> a(x \<mapsto> 0) ## b \<longleftrightarrow> a ## b\<close>
  \<open>a x = None \<Longrightarrow> a ## b(x \<mapsto> 0) \<longleftrightarrow> a ## b\<close>
  by (force simp add: disjoint_fun_def)+

lemma plus_map_empty_eq[simp]:
  \<open>a + Map.empty = a\<close>
  \<open>Map.empty + b = b\<close>
  by fastforce+

lemma plus_map_insert_eq[simp]:
  \<open>b x = None \<Longrightarrow> a(x \<mapsto> v) + b = (a + b)(x \<mapsto> v)\<close>
  \<open>a x = None \<Longrightarrow> a + b(x \<mapsto> v) = (a + b)(x \<mapsto> v)\<close>
  by fastforce+

lemma alloc_frame_safe:
  \<open>h1 ## h2 \<Longrightarrow>
    b = (\<lambda>h h'. snd h = snd h' \<and> (\<exists>x. x \<notin> dom (fst h) \<and> fst h' = (fst h)(x \<mapsto> 0))) \<Longrightarrow>
    strong_local_unframe_safe (rel_lift ((=) h2)) b\<close>
  apply (clarsimp simp add: strong_local_unframe_safe_def)
  apply (metis (lifting) disjoint_map_insert_fresh_iff(1) domIff plus_map_insert_eq(1))
  done


definition
  \<open>strong_shared_unframe_safe \<ff> r \<equiv>
    \<forall>x x' s z sz'.
      Ex (\<ff> z) \<longrightarrow>
      r (x, s+z) (x', sz') \<longrightarrow>
      s ## z \<longrightarrow>
      (\<exists>s' z'. \<ff> z z' \<and> s' ## z' \<and> sz' = s' + z' \<and> r (x, s) (x', s'))\<close>

lemma strong_shared_unframe_safeD:
  \<open>strong_shared_unframe_safe \<ff> r \<Longrightarrow> 
    Ex (\<ff> z) \<Longrightarrow> s ## z \<Longrightarrow> r (x, s+z) (x', sz') \<Longrightarrow>
    (\<exists>s' z'. \<ff> z z' \<and> s' ## z' \<and> sz' = s' + z' \<and> r (x, s) (x', s'))\<close>
  by (simp add: strong_shared_unframe_safe_def)

lemma strong_shared_unframe_safe_mono:
  \<open>\<ff>1 \<le> \<ff>2 \<Longrightarrow> \<forall>x. \<ff>1 x \<ge> \<ff>2 x \<Longrightarrow>
    strong_shared_unframe_safe \<ff>1 r \<Longrightarrow>
    strong_shared_unframe_safe \<ff>2 r\<close>
  by (simp add: strong_shared_unframe_safe_def post_state_def le_fun_def, meson)

lemma opstep_shared_unframe:
  fixes hs2 :: \<open>'a :: cancel_perm_alg\<close>
  shows
    \<open>opstep a s s' \<Longrightarrow>
      hs1 ## hs2 \<Longrightarrow>
      hs1' ## hs2 \<Longrightarrow>
      s = ((hl, hs1 + hs2), c) \<Longrightarrow>
      s' = ((hl', hs1' + hs2), c') \<Longrightarrow>
      all_atom_comm (strong_shared_unframe_safe (rel_lift ((=) hs2))) c \<Longrightarrow>
      opstep a ((hl, hs1), c) ((hl', hs1'), c')\<close>
  by (induct arbitrary: hl hs1 c hl' hs1' c' hs2 rule: opstep.inducts)
    (fastforce simp add: opstep_iff strong_shared_unframe_safe_def)+

lemma safe_parallel_extend:
  \<open>safe n c1 hl hs rg2 g1 (sp ((=) \<times>\<^sub>R (r \<squnion> g2)\<^sup>*\<^sup>*) q1) \<Longrightarrow>
    rg2 = r \<squnion> g2 \<Longrightarrow>
    safe n (c1 \<parallel> c2) hl hs r (g1 \<squnion> g2)
      (sp ((=) \<times>\<^sub>R (r \<squnion> g2)\<^sup>*\<^sup>*) q1 \<^emph> \<top>)\<close>
  apply (induct arbitrary: r g2 rule: safe.inducts)
   apply blast
  apply (rule safe_suc)
        apply blast+
       apply (frule opstep_tau_preserves_heap)
       apply (erule opstep_parE) (* 6 \<rightarrow> 8 *)
         apply fast
        apply (simp; fail)
       apply blast
      apply clarsimp
  oops



lemma safe_parallel:
  fixes hl1 hl2 :: \<open>'a::sep_alg\<close>
    and hs1 hs2 :: \<open>'b::sep_alg\<close>
  shows                       
  \<open>safe n c1 hl1 hs1 (r \<squnion> g2) g1 (sp ((=) \<times>\<^sub>R (r \<squnion> g2)\<^sup>*\<^sup>*) q1) \<Longrightarrow>
    safe n c2 hl2 hs2 (r \<squnion> g1) g2 (sp ((=) \<times>\<^sub>R (r \<squnion> g1)\<^sup>*\<^sup>*) q2) \<Longrightarrow>
    weak_rel_add_preserve ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*)
      (sp ((=) \<times>\<^sub>R (r \<squnion> g2)\<^sup>*\<^sup>*) q1)
      (sp ((=) \<times>\<^sub>R (r \<squnion> g1)\<^sup>*\<^sup>*) q2) \<Longrightarrow>
    rel_add_preserve r \<top> \<top> \<Longrightarrow>
    rel_add_preserve g1 \<top> \<top> \<Longrightarrow>
    rel_add_preserve g2 \<top> \<top> \<Longrightarrow>
    all_atom_comm (strong_local_unframe_safe (rel_lift ((=) hl2))) c1 \<Longrightarrow>
    all_atom_comm (strong_local_unframe_safe (rel_lift ((=) hl1))) c2 \<Longrightarrow>
    all_atom_comm (local_frame_safe (=)) c1 \<Longrightarrow>
    all_atom_comm (local_frame_safe (=)) c2 \<Longrightarrow>
    hl1 ## hl2 \<Longrightarrow>
    hs1 ## hs2 \<Longrightarrow>
    safe n (c1 \<parallel> c2) (hl1 + hl2) (hs1 + hs2) r (g1 \<squnion> g2)
      ((sp ((=) \<times>\<^sub>R (r \<squnion> g2)\<^sup>*\<^sup>*) q1) \<^emph> (sp ((=) \<times>\<^sub>R (r \<squnion> g1)\<^sup>*\<^sup>*) q2))\<close>
proof (induct n arbitrary: c1 c2 hl1 hs1 hl2 hs2)
  case 0
  then show ?case by force
next
  case (Suc n)
  
  show ?case
  proof (rule safe_suc; (intro impI)?)
    assume \<open>c1 \<parallel> c2 = Skip\<close>
    then show \<open>(sp ((=) \<times>\<^sub>R (r \<squnion> g2)\<^sup>*\<^sup>*) q1 \<^emph> sp ((=) \<times>\<^sub>R (r \<squnion> g1)\<^sup>*\<^sup>*) q2) (hl1 + hl2, hs1 + hs2)\<close>
      by blast
  next
    fix c' hl' hs'
    assume \<open>opstep Tau ((hl1 + hl2, hs1 + hs2), c1 \<parallel> c2) ((hl', hs'), c')\<close>
    then show \<open>(hl1 + hl2, hs1 + hs2) = (hl', hs')\<close>
      by (metis (no_types, lifting) opstep_tau_preserves_heap prod_eq_decompose(2))
  next
    fix c' hl' hs12'
    assume \<open>opstep Local ((hl1 + hl2, hs1 + hs2), c1 \<parallel> c2) ((hl', hs12'), c')\<close>
    then show \<open>(g1 \<squnion> g2) (hs1 + hs2) hs12'\<close>
      using Suc.prems(1-2,6-)
      apply (clarsimp simp add: opstep_iff)
      apply (elim disjE)
        (* c1 step *)
       apply clarsimp
       apply (frule opstep_local_unframe_right, blast, blast, blast)
       apply clarsimp
       apply (elim safe_sucE)
       apply presburger
        (* c2 step *)
      apply clarsimp
      apply (frule opstep_local_unframe_left, blast, blast, blast)
      apply clarsimp
      apply (elim safe_sucE)
      apply (metis (lifting) disjoint_sym partial_add_commute)
      done
  next
    fix c' hl' hsf hsx'
    assume lassms:
      \<open>hs1 + hs2 ## hsf\<close>
      \<open>opstep Local ((hl1 + hl2, hs1 + hs2 + hsf), c1 \<parallel> c2) ((hl', hsx'), c')\<close>

    have safe_c1:
      \<open>c1 = Skip \<longrightarrow> sp ((=) \<times>\<^sub>R (r \<squnion> g2)\<^sup>*\<^sup>*) q1 (hl1, hs1)\<close>
      \<open>\<And>c' hl' hs'. opstep Tau ((hl1, hs1), c1) ((hl', hs'), c') \<Longrightarrow> hl1 = hl' \<and> hs1 = hs'\<close>
      \<open>\<And>c' hl' hs'. opstep Local ((hl1, hs1), c1) ((hl', hs'), c') \<Longrightarrow> g1 hs1 hs'\<close>
      \<open>\<And>c' hl' hsf hsx'.
        hs1 ## hsf \<Longrightarrow>
        opstep Local ((hl1, hs1 + hsf), c1) ((hl', hsx'), c') \<Longrightarrow>
        g1 (hs1 + hsf) hsx' \<and> (\<exists>hs' hsf'. hs' ## hsf' \<and> hsx' = hs' + hsf' \<and> g1 hs1 hs' \<and> g1 hsf hsf')\<close>
      \<open>\<And>a c' hl' hs' hlb hlb' hf.
        opstep a ((hl1, hs1), c1) ((hl', hs'), c') \<Longrightarrow>
        weak_framed_subresource_rel ((=) hf) hl1 hl' hlb hlb' \<Longrightarrow> opstep a ((hlb, hs1), c1) ((hlb', hs'), c')\<close>
      \<open>\<And>a c' hl' hs'. opstep a ((hl1, hs1), c1) ((hl', hs'), c') \<Longrightarrow> safe n c' hl' hs' (r \<squnion> g2) g1 (sp ((=) \<times>\<^sub>R (r \<squnion> g2)\<^sup>*\<^sup>*) q1)\<close>
      \<open>\<And>hs'. (r \<squnion> g2) hs1 hs' \<Longrightarrow> safe n c1 hl1 hs' (r \<squnion> g2) g1 (sp ((=) \<times>\<^sub>R (r \<squnion> g2)\<^sup>*\<^sup>*) q1)\<close>
      using Suc.prems(1)
      by (elim safe_sucE, metis)+
    have safe_c2:
      \<open>c2 = Skip \<longrightarrow> sp ((=) \<times>\<^sub>R (r \<squnion> g1)\<^sup>*\<^sup>*) q2 (hl2, hs2)\<close>
      \<open>\<And>c' hl' hs'. opstep Tau ((hl2, hs2), c2) ((hl', hs'), c') \<Longrightarrow> hl2 = hl' \<and> hs2 = hs'\<close>
      \<open>\<And>c' hl' hs'. opstep Local ((hl2, hs2), c2) ((hl', hs'), c') \<Longrightarrow> g2 hs2 hs'\<close>
      \<open>\<And>c' hl' hsf hsx'.
        hs2 ## hsf \<Longrightarrow>
        opstep Local ((hl2, hs2 + hsf), c2) ((hl', hsx'), c') \<Longrightarrow>
        g2 (hs2 + hsf) hsx' \<and> (\<exists>hs' hsf'. hs' ## hsf' \<and> hsx' = hs' + hsf' \<and> g2 hs2 hs' \<and> g2 hsf hsf')\<close>
      \<open>\<And>a c' hl' hs' hlb hlb' hf.
        opstep a ((hl2, hs2), c2) ((hl', hs'), c') \<Longrightarrow>
        weak_framed_subresource_rel ((=) hf) hl2 hl' hlb hlb' \<Longrightarrow> opstep a ((hlb, hs2), c2) ((hlb', hs'), c')\<close>
      \<open>\<And>a c' hl' hs'. opstep a ((hl2, hs2), c2) ((hl', hs'), c') \<Longrightarrow> safe n c' hl' hs' (r \<squnion> g1) g2 (sp ((=) \<times>\<^sub>R (r \<squnion> g1)\<^sup>*\<^sup>*) q2)\<close>
      \<open>\<And>hs'. (r \<squnion> g1) hs2 hs' \<Longrightarrow> safe n c2 hl2 hs' (r \<squnion> g1) g2 (sp ((=) \<times>\<^sub>R (r \<squnion> g1)\<^sup>*\<^sup>*) q2)\<close>
      using Suc.prems(2)
      by (elim safe_sucE, metis)+

    have h1:
      \<open>\<And>hl' hsx' c'.
        opstep Local ((hl1, hs1 + hs2 + hsf), c1) ((hl', hsx'), c') \<Longrightarrow>
        g1 (hs1 + hs2 + hsf) hsx' \<and> (\<exists>hs' hsf'. hs' ## hsf' \<and> hsx' = hs' + hsf' \<and> g1 hs1 hs' \<and> g1 (hs2 + hsf) hsf')\<close>
      using Suc.prems lassms safe_c1(4)[where hsf=\<open>hs2 + hsf\<close>]
      by (metis disjoint_add_leftR disjoint_add_swap2 partial_add_assoc3)
    have h2:
      \<open>\<And>hl' hsx' c'.
        opstep Local ((hl2, hs1 + hs2 + hsf), c2) ((hl', hsx'), c') \<Longrightarrow>
        g2 (hs1 + hs2 + hsf) hsx' \<and> (\<exists>hs' hsf'. hs' ## hsf' \<and> hsx' = hs' + hsf' \<and> g2 hs2 hs' \<and> g2 (hs1 + hsf) hsf')\<close>
      using Suc.prems lassms safe_c2(4)[where hsf=\<open>hs1 + hsf\<close>]
      by (metis partial_add_assoc_commute_left disjoint_sym disjoint_add_rightL disjoint_add_rightR
          disjoint_add_left_commute2)

    show
      \<open>(g1 \<squnion> g2) (hs1 + hs2 + hsf) hsx' \<and>
          (\<exists>hs' hsf'. hs' ## hsf' \<and> hsx' = hs' + hsf' \<and> (g1 \<squnion> g2) (hs1 + hs2) hs' \<and> (g1 \<squnion> g2) hsf hsf')\<close>
      using Suc.prems(5-) lassms
      apply (clarsimp simp add: opstep_iff)
      apply (elim disjE)
        (* c1 step *)
       apply clarsimp
       apply (frule opstep_local_unframe_right, blast, blast, blast)
       apply clarsimp
       apply (frule h1)
       apply clarsimp
       apply (frule rel_add_preserveD[of g1], blast, blast, blast, blast)
       apply blast
        (* c2 step *)
      apply clarsimp
      apply (frule opstep_local_unframe_left, blast, blast, blast)
      apply clarsimp
      apply (frule h2)
      apply clarsimp
      apply (frule rel_add_preserveD[of g2], blast, blast, blast, blast)
      apply blast
      done
  next
    fix a c' hl' hs' hlb hlb' hf
    assume
      \<open>opstep a ((hl1 + hl2, hs1 + hs2), c1 \<parallel> c2) ((hl', hs'), c')\<close>
      \<open>weak_framed_subresource_rel ((=) hf) (hl1 + hl2) hl' hlb hlb'\<close>
    then show
      \<open>opstep a ((hlb, hs1 + hs2), c1 \<parallel> c2) ((hlb', hs'), c')\<close>
      using Suc.prems(5-)
      apply -
      apply (elim opstep_parE safe_sucE) (* 1 \<rightarrow> 3 *)
        (* c1 \<parallel> c2 \<rightarrow> c1' \<parallel> c2 *)
        apply clarify
        apply (drule opstep_local_frame, blast)
         apply (rule all_atom_comm_pred_mono[of \<open>local_frame_safe _\<close> \<open>local_frame_safe _\<close>, rotated],
          blast)
         apply clarsimp
         apply (rule local_frame_safe_framerel_antimonoD[rotated], blast)
         apply force
        apply blast
        (* c1 \<parallel> c2 \<rightarrow> c1 \<parallel> c2' *)
       apply clarify
       apply (drule opstep_local_frame, blast)
        apply (rule all_atom_comm_pred_mono[of \<open>local_frame_safe _\<close> \<open>local_frame_safe _\<close>, rotated],
          blast)
        apply clarsimp
        apply (rule local_frame_safe_framerel_antimonoD[rotated], blast)
        apply force
       apply blast
          (* Skip \<parallel> Skip \<rightarrow> Skip *)
      apply clarsimp
      apply (metis framed_subresource_rel_top_same_sub_iff par_skip weak_framed_subresource_rel_def)
      done
  next
    fix a c' hl' hs'

    have safe_c1:
      \<open>c1 = Skip \<longrightarrow> sp ((=) \<times>\<^sub>R (r \<squnion> g2)\<^sup>*\<^sup>*) q1 (hl1, hs1)\<close>
      \<open>\<And>c' hl' hs'. opstep Tau ((hl1, hs1), c1) ((hl', hs'), c') \<Longrightarrow> hl1 = hl' \<and> hs1 = hs'\<close>
      \<open>\<And>c' hl' hs'. opstep Local ((hl1, hs1), c1) ((hl', hs'), c') \<Longrightarrow> g1 hs1 hs'\<close>
      \<open>\<And>c' hl' hsf hsx'.
        hs1 ## hsf \<Longrightarrow>
        opstep Local ((hl1, hs1 + hsf), c1) ((hl', hsx'), c') \<Longrightarrow>
        g1 (hs1 + hsf) hsx' \<and> (\<exists>hs' hsf'. hs' ## hsf' \<and> hsx' = hs' + hsf' \<and> g1 hs1 hs' \<and> g1 hsf hsf')\<close>
      \<open>\<And>a c' hl' hs' hlb hlb' hf.
        opstep a ((hl1, hs1), c1) ((hl', hs'), c') \<Longrightarrow>
        weak_framed_subresource_rel ((=) hf) hl1 hl' hlb hlb' \<Longrightarrow> opstep a ((hlb, hs1), c1) ((hlb', hs'), c')\<close>
      \<open>\<And>a c' hl' hs'. opstep a ((hl1, hs1), c1) ((hl', hs'), c') \<Longrightarrow> safe n c' hl' hs' (r \<squnion> g2) g1 (sp ((=) \<times>\<^sub>R (r \<squnion> g2)\<^sup>*\<^sup>*) q1)\<close>
      \<open>\<And>hs'. (r \<squnion> g2) hs1 hs' \<Longrightarrow> safe n c1 hl1 hs' (r \<squnion> g2) g1 (sp ((=) \<times>\<^sub>R (r \<squnion> g2)\<^sup>*\<^sup>*) q1)\<close>
      using Suc.prems(1)
      by (elim safe_sucE, metis)+
    have safe_c2:
      \<open>c2 = Skip \<longrightarrow> sp ((=) \<times>\<^sub>R (r \<squnion> g1)\<^sup>*\<^sup>*) q2 (hl2, hs2)\<close>
      \<open>\<And>c' hl' hs'. opstep Tau ((hl2, hs2), c2) ((hl', hs'), c') \<Longrightarrow> hl2 = hl' \<and> hs2 = hs'\<close>
      \<open>\<And>c' hl' hs'. opstep Local ((hl2, hs2), c2) ((hl', hs'), c') \<Longrightarrow> g2 hs2 hs'\<close>
      \<open>\<And>c' hl' hsf hsx'.
        hs2 ## hsf \<Longrightarrow>
        opstep Local ((hl2, hs2 + hsf), c2) ((hl', hsx'), c') \<Longrightarrow>
        g2 (hs2 + hsf) hsx' \<and> (\<exists>hs' hsf'. hs' ## hsf' \<and> hsx' = hs' + hsf' \<and> g2 hs2 hs' \<and> g2 hsf hsf')\<close>
      \<open>\<And>a c' hl' hs' hlb hlb' hf.
        opstep a ((hl2, hs2), c2) ((hl', hs'), c') \<Longrightarrow>
        weak_framed_subresource_rel ((=) hf) hl2 hl' hlb hlb' \<Longrightarrow> opstep a ((hlb, hs2), c2) ((hlb', hs'), c')\<close>
      \<open>\<And>a c' hl' hs'. opstep a ((hl2, hs2), c2) ((hl', hs'), c') \<Longrightarrow> safe n c' hl' hs' (r \<squnion> g1) g2 (sp ((=) \<times>\<^sub>R (r \<squnion> g1)\<^sup>*\<^sup>*) q2)\<close>
      \<open>\<And>hs'. (r \<squnion> g1) hs2 hs' \<Longrightarrow> safe n c2 hl2 hs' (r \<squnion> g1) g2 (sp ((=) \<times>\<^sub>R (r \<squnion> g1)\<^sup>*\<^sup>*) q2)\<close>
      using Suc.prems(2)
      by (elim safe_sucE, metis)+

    assume \<open>opstep a ((hl1 + hl2, hs1 + hs2), c1 \<parallel> c2) ((hl', hs'), c')\<close>
    then show \<open>safe n c' hl' hs' r (g1 \<squnion> g2) (sp ((=) \<times>\<^sub>R (r \<squnion> g2)\<^sup>*\<^sup>*) q1 \<^emph> sp ((=) \<times>\<^sub>R (r \<squnion> g1)\<^sup>*\<^sup>*) q2)\<close>
      using Suc.prems(3-)
      apply -
      apply (elim opstep_parE safe_sucE)
        (* c1 \<parallel> c2 \<rightarrow> c1' \<parallel> c2 *)
        apply (rename_tac c1')
        apply clarsimp
        apply (frule opstep_local_unframe_right, blast, force, blast)
        apply clarsimp
    (* Resume Here *)
      subgoal sorry
          (* c1 \<parallel> c2 \<rightarrow> c1 \<parallel> c2' *)
       apply (rename_tac c2')
       apply clarsimp
       apply (frule opstep_local_unframe_left, blast, force, blast)
       apply clarsimp
       apply (rename_tac hl2')
       apply (subgoal_tac
          \<open>\<exists>hs1' hs2'. hs1' ## hs2' \<and> hs' = hs1' + hs2' \<and>
              opstep a ((hl2, hs2), c2) ((hl2', hs2'), c2') \<and> g2 hs1 hs1'\<close>)
        prefer 2
      subgoal sorry
       apply clarsimp
        apply (rule Suc.hyps[OF safe_c1(6) safe_c2(5)])
               apply blast
             apply blast
            apply force
           apply force
      subgoal sorry
         apply (meson opstep_preserves_all_atom_comm[OF _ Suc.prems(6)]; fail)
        apply blast
       apply blast
          (* Skip \<parallel> Skip \<rightarrow> Skip *)
      apply (insert safe_c1(1) safe_c2(1))
      apply clarsimp
      apply (rule safe_parallel_skip)
          apply (rule safe_skip', force)
         apply (rule safe_skip', force)
        apply blast
       apply blast
      apply (metis Suc.prems(3))
      done
  next
    fix hs'
    assume \<open>r (hs1 + hs2) hs'\<close>
    then show \<open>safe n (c1 \<parallel> c2) (hl1 + hl2) hs' r (g1 \<squnion> g2)
        (sp ((=) \<times>\<^sub>R (r \<squnion> g2)\<^sup>*\<^sup>*) q1 \<^emph> sp ((=) \<times>\<^sub>R (r \<squnion> g1)\<^sup>*\<^sup>*) q2)\<close>
      using Suc.prems(3,4-8)
      apply -
      apply (frule iffD1[OF meta_eq_to_obj_eq[OF rel_add_preserve_def]])
      apply (drule spec2, drule spec, drule mp, assumption, drule mp, assumption)
      apply (elim conjE impE exE, blast, blast)
      apply simp
      apply (insert Suc.prems(1,2))
      apply (rule Suc.hyps)
             apply (erule safe_sucE, fast)
            apply (erule safe_sucE, fast)
           apply fastforce
          apply fastforce
         apply fastforce
        apply fastforce
       apply fastforce
      apply fastforce
      done
  qed
qed


section \<open> Soundness \<close>

text \<open> TODO: move these lemmas \<close>

lemma opstep_tau_extendD:
  \<open>opstep a s s' \<Longrightarrow>
    a = Tau \<Longrightarrow>
    all_atom_comm (\<lambda>b. \<forall>s s'. b s s' \<longrightarrow> (\<forall>sa\<ge>s. \<exists>sa'\<ge>s'. b sa sa')) (snd s) \<Longrightarrow>
    fst s ## h2 \<Longrightarrow>
    \<exists>h''\<ge>fst s'. opstep a (fst s + h2, snd s) (h'', snd s')\<close>
  by (induct rule: opstep.induct)
    (force dest: partial_le_plus)+

lemma can_compute_frame:
  \<open>can_compute s \<Longrightarrow>
    all_atom_comm (\<lambda>b. \<forall>s s'. b s s' \<longrightarrow> (\<forall>sa\<ge>s. \<exists>sa'\<ge>s'. b sa sa')) (snd s) \<Longrightarrow>
    fst s ## r \<Longrightarrow>
    can_compute (fst s + r, snd s)\<close>
  unfolding can_compute_def
  using opstep_tau_extendD
  oops

lemma soundness:
  fixes p q :: \<open>'a::perm_alg \<Rightarrow> bool\<close>
  assumes \<open>rgsat c r g p q\<close>
    and \<open>p h\<close>
  shows \<open>safe n c hl hs r g q\<close>
  using assms
proof (induct c r g p q arbitrary: n h rule: rgsat.inducts)
  case (rgsat_skip p r q g as h)
  then show ?case
    by (force intro!: safe_skip[where p=p])
next
  case (rgsat_iter c r g p' q' p i q)
  then show ?case
    using safe_iter[of p' _ _ _ q' p i]
    by force
next
  case (rgsat_seq c1 r g p1 p2 c2 p3)
  then show ?case
    using safe_seq[of n c1 h r g p2 c2 p3]
    by blast
next
  case (rgsat_ndet c1 r g1 p q1 c2 g2 q2 g q)
  then show ?case
    using safe_ndet[of n c1 hl hs r g q c2]
    by (meson safe_guarantee_mono safe_postpred_mono)
next
  case (rgsat_parallel s1 r g2 g1 p1 q1 s2 p2 q2 g p q)
  moreover obtain h1 h2
    where
      \<open>p1 h1\<close>
      \<open>p2 h2\<close>
      \<open>h = h1 + h2\<close>
      \<open>h1 ## h2\<close>
    using rgsat_parallel
    by (metis predicate1D sepconj_def)
  moreover obtain n1 n2
    where
      \<open>n = n1 + n2\<close>
      \<open>g = g1 \<squnion> g2\<close>
      \<open>safe n1 s1 h1 (r \<squnion> g2) g1 q1\<close>
      \<open>safe n2 s2 h2 (r \<squnion> g1) g2 q2\<close>
    sorry
  ultimately show ?case
    apply clarsimp
    apply (rule safe_postpred_mono, blast)
    apply (rule safe_parallel)
    sorry
next
  case (rgsat_atom p b q Something g p' f r q')
  then show ?case
    sorry
next
  case (rgsat_frame c r g p q f as)
  obtain h1 h2
    where
      \<open>h1 ## h2\<close>
      \<open>h = h1 + h2\<close>
      \<open>p h1\<close>
      \<open>f h2\<close>
    using rgsat_frame.prems
    by (clarsimp simp add: sepconj_def)
  moreover then have \<open>safe as c h1 r g q\<close>
    using rgsat_frame.prems
    apply -
    apply (rule rgsat_frame.hyps(2))
      apply blast
     apply blast
    apply blast
    done
  ultimately show ?case
    using rgsat_frame
    by (force intro!: safe_frame2 simp add: frame_pred_closed_def)
next
  case (rgsat_weaken c r' g' p' q' p q r g)
  then show ?case sorry
qed

end