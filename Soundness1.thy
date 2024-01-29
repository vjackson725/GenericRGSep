theory Soundness1
  imports RGSep
begin

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
| par_left[intro]:  \<open>opstep a (h, s) (h', s') \<Longrightarrow> opstep a (h, s \<parallel> t) (h', s' \<parallel> t)\<close>
| par_right[intro]: \<open>opstep a (h, t) (h', t') \<Longrightarrow> opstep a (h, s \<parallel> t) (h', s \<parallel> t')\<close>
| par_skip[intro!]:  \<open>opstep Tau (h, Skip \<parallel> Skip) (h, Skip)\<close>
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
    \<open>all_atom_comm (frame_pred_safe ((=) hf)) (snd s)\<close>
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
    \<open>all_atom_comm (frame_pred_safe ((=) hf)) c\<close>
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

(*
lemma opstep_strong_unframe':
  fixes s :: \<open>('a::cancel_perm_alg) \<times> 'a comm\<close>
  assumes
    \<open>s \<midarrow>a\<rightarrow> s'\<close>
    \<open>s = (h + hf, c)\<close>
    \<open>all_atom_comm (unframe_safe (rel_lift ((=) hf))) c\<close>
    \<open>all_atom_comm (\<lambda>b. \<forall>x. x ## hf \<longrightarrow> Ex (b (x + hf)) \<longrightarrow> (\<exists>y. y ## hf \<and> b (x + hf) (y + hf))) c\<close>
    \<open>h ## hf\<close>
  shows
    \<open>\<exists>h'. (h, c) \<midarrow>a\<rightarrow> (h', snd s')\<close>
  using assms
  apply -
  apply (induct arbitrary: h c hf rule: opstep.induct)
                apply fastforce
               apply fastforce
              apply fastforce
             apply fastforce
            apply fastforce
           apply fastforce
  subgoal sorry
         apply fastforce
        apply fastforce
  apply fastforce
  apply fastforce
     apply fastforce
    apply fastforce
apply fastforce
              sledgehammer
  apply (simp add: opstep_iff unframe_safeD)
  done
*)

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
  :: \<open>nat \<Rightarrow> ('s::perm_alg) comm \<Rightarrow> 's \<Rightarrow>
        ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where
  safe_nil[intro!]: \<open>safe 0 c h r g q\<close>
| safe_suc[intro]:
  \<open>\<comment> \<open> computation is frame safe (TODO: not needed with atomic actions) \<close>
    \<comment> \<open> if the command is Skip, the postcondition is established \<close>
    (c = Skip \<longrightarrow> q h) \<Longrightarrow>
    \<comment> \<open> opsteps respect the guarantee \<close>
    (\<And>a c' hx hy.
      h \<le> hx \<Longrightarrow>
      (hx, c) \<midarrow>a\<rightarrow> (hy, c') \<Longrightarrow>
      (a = Tau \<longrightarrow> hx = hy) \<and>
      (a = Local \<longrightarrow>
        (\<forall>hxs. hxs \<le> hx \<longrightarrow> change_state r hxs \<longrightarrow>
          (\<forall>hys. hys \<le> hy \<longrightarrow> change_state r hys \<longrightarrow>
            g hxs hys)))) \<Longrightarrow>
    \<comment> \<open> opsteps are safe \<close>
    (\<And>a c' h'. (h, c) \<midarrow>a\<rightarrow> (h', c') \<Longrightarrow> safe n c' h' r g q) \<Longrightarrow>
    \<comment> \<open> rely steps are safe \<close>
    (\<And>h'. (wframe r with \<top>) h h' \<Longrightarrow> safe n c h' r g q) \<Longrightarrow>
    \<comment> \<open> conclude a step can be made \<close>
    safe (Suc n) c h r g q\<close>

inductive_cases safe_zeroE[elim!]: \<open>safe 0 c s r g q\<close>
inductive_cases safe_sucE[elim]: \<open>safe (Suc n) c s r g q\<close>

subsection \<open> Proofs about safe \<close>

lemma safe_nil_iff[simp]:
  \<open>safe 0 c h r g q \<longleftrightarrow> True\<close>
  by force

lemma safe_suc_iff:
  \<open>safe (Suc n) c h r g q \<longleftrightarrow>
    (c = Skip \<longrightarrow> q h) \<and>
    (\<forall>a c' hx hy.
      h \<le> hx \<longrightarrow>
      (hx, c) \<midarrow>a\<rightarrow> (hy, c') \<longrightarrow>
      (a = Tau \<longrightarrow> hx = hy) \<and>
      (a = Local \<longrightarrow>
        (\<forall>hxs. hxs \<le> hx \<longrightarrow> change_state r hxs \<longrightarrow>
          (\<forall>hys. hys \<le> hy \<longrightarrow> change_state r hys \<longrightarrow>
            g hxs hys)))) \<and>
    (\<forall>a c' h'. (h, c) \<midarrow>a\<rightarrow> (h', c') \<longrightarrow>
      safe n c' h' r g q) \<and>
    (\<forall>h'. (wframe r with \<top>) h h' \<longrightarrow> safe n c h' r g q)\<close>
  apply (rule iffI)
   apply (erule safe_sucE; presburger)
  apply (rule safe_suc; presburger)
  done

subsubsection \<open> Monotonicity \<close>

lemma safe_postpred_monoD:
  \<open>safe n c h r g q \<Longrightarrow> q \<le> q' \<Longrightarrow> safe n c h r g q'\<close>
  apply (induct rule: safe.induct)
   apply blast
  apply (simp add: safe_suc_iff, meson predicate1D)
  done

lemmas safe_postpred_mono = safe_postpred_monoD[rotated]

lemma safe_guarantee_monoD:
  \<open>safe n c h r g q \<Longrightarrow> g \<le> g' \<Longrightarrow> safe n c h r g' q\<close>
  apply (induct rule: safe.induct)
   apply blast
  apply (simp add: safe_suc_iff, metis predicate2D)
  done

lemmas safe_guarantee_mono = safe_guarantee_monoD[rotated]

lemma safe_rely_antimonoD:
  \<open>safe n c h r g q \<Longrightarrow> r' \<le> r \<Longrightarrow> safe n c h r' g q\<close>
  apply (induct rule: safe.induct)
   apply force
  apply (simp add: safe_suc_iff)
  apply (rule conjI)
   apply (metis change_state_mono)
  apply (metis predicate2D weak_framed_rel_mono)
  done

lemmas safe_rely_antimono = safe_rely_antimonoD[rotated]

lemma safe_step_monoD:
  \<open>safe n c h r g q \<Longrightarrow> m \<le> n \<Longrightarrow> safe m c h r g q\<close>
  by (induct arbitrary: m rule: safe.inducts)
    (force simp add: le_Suc_iff0 safe_suc_iff)+

subsubsection \<open> Skip \<close>

lemma safe_skip':
  \<open>(\<lceil> q \<rceil>\<^bsub>wframe r with \<top>\<^esub>) h \<Longrightarrow> safe n Skip h r g (\<lceil> q \<rceil>\<^bsub>wframe r with \<top>\<^esub>)\<close>
  apply (induct n arbitrary: h q)
   apply force
  apply (simp add: safe_suc_iff opstep_iff wsstable_step)
  done

lemma safe_skip:
  \<open>p h \<Longrightarrow> \<lceil> p \<rceil>\<^bsub>wframe r with \<top>\<^esub> \<le> q \<Longrightarrow> safe n Skip h r g q\<close>
  by (blast intro!: safe_postpred_monoD[OF safe_skip'[where q=p]])

subsubsection \<open> Atomic \<close>

definition rel_split :: \<open>('a::multiunit_sep_alg \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'a \<Rightarrow> 'a \<times> 'a \<Rightarrow> bool)\<close> where
  \<open>rel_split S r \<equiv>
    \<lambda>(xl, xs) (yl, ys). 
      xl ## xs \<and> yl ## ys \<and>
      S xs \<and> S ys \<and>
      r (xl + xs) (yl + ys)\<close>

definition \<open>shared_restr S r \<equiv> \<lambda>x y. S x \<and> S y \<and> (\<exists>xw yw. r xw yw \<and> x \<le> xw \<and> y \<le> yw)\<close>

lemma
  \<open>\<exists>P.
    (\<forall>h. P h \<longrightarrow> (\<forall>hx. h \<le> hx \<longrightarrow> Ex (b h) \<longrightarrow> Ex (b hx))) \<and>
    (\<forall>h h'. (wframe r with \<top>) h h' \<longrightarrow> P h \<longrightarrow> P h')\<close>
  apply (simp add: wframe_with_def framed_subresource_rel_def)
  apply (simp del: all_simps(5) add: all_simps(5)[symmetric] imp_conjL imp_conjR all_conj_distrib)
  apply simp

  oops


lemma safe_atom':
  \<open>rel_liftL p \<sqinter> b \<le> rel_liftR (\<lceil> q \<rceil>\<^bsub>wframe r with \<top>\<^esub>) \<Longrightarrow>
    \<lfloor> p \<rfloor>\<^bsub>wframe r with \<top>\<^esub> \<le> pre_state b \<Longrightarrow>
    \<forall>h'. (wframe r with \<top>)\<^sup>*\<^sup>* h h' \<longrightarrow> Ex (b h') \<longrightarrow> (\<forall>hx\<ge>h'. Ex (b hx)) \<Longrightarrow>
    (\<lfloor> p \<rfloor>\<^bsub>wframe r with \<top>\<^esub>) h \<Longrightarrow>
    shared_restr (change_state r) b \<le> g \<Longrightarrow>
    safe n (Atomic b) h r g (\<lceil> q \<rceil>\<^bsub>wframe r with \<top>\<^esub>)\<close>
  apply (induct n arbitrary: h)
   apply force
  apply clarsimp
  apply (rule safe.safe_suc)
     apply force
    apply (clarsimp simp add: shared_restr_def le_fun_def, metis)
   apply (clarsimp simp add: le_fun_def, metis predicate1D safe_skip' swstable_weaker)
  apply (metis swstable_step converse_rtranclp_into_rtranclp)
  done

subsubsection \<open> Sequencing \<close>

lemma safe_seq_assoc_left:
  \<open>safe n c h r g q \<Longrightarrow>
    c = (c1 ;; c2 ;; c3) \<Longrightarrow>
    safe n ((c1 ;; c2) ;; c3) h r g q\<close>
  apply (induct arbitrary: c1 c2 c3 rule: safe.inducts)
   apply force
  apply (simp add: safe_suc_iff opstep_iff)
  apply (intro conjI impI allI)
    apply metis+
  done

lemma safe_seq_assoc_right:
  \<open>safe n c h r g q \<Longrightarrow>
    c = ((c1 ;; c2) ;; c3) \<Longrightarrow>
    safe n (c1 ;; c2 ;; c3) h r g q\<close>
  apply (induct arbitrary: c1 c2 c3 rule: safe.inducts)
   apply force
  apply (simp add: safe_suc_iff opstep_iff)
  apply (intro conjI impI allI)
    apply metis+
  done

lemma safe_seq':
  \<open>safe n c1 h r g q \<Longrightarrow>
    (\<forall>m h'. m \<le> n \<longrightarrow> q h' \<longrightarrow> safe m c2 h' r g q') \<Longrightarrow>
    safe n (c1 ;; c2) h r g q'\<close>
  apply (induct arbitrary: c2 q' rule: safe.inducts)
   apply force
  apply (rule safe_suc)
     apply blast
    apply (clarsimp simp add: opstep_iff)
    apply (elim disjE exE conjE)
     apply fastforce
    apply (clarify, presburger)
   apply (simp add: opstep_iff, erule disjE, force, force)
  apply force
  done

lemma safe_seq:
  \<open>safe n c1 h r g q \<Longrightarrow>
    (\<forall>h'. q h' \<longrightarrow> safe n c2 h' r g q') \<Longrightarrow>
    safe n (c1 ;; c2) h r g q'\<close>
  by (rule safe_seq', blast, metis safe_step_monoD)

subsection \<open> Iteration \<close>

lemma safe_iter':
  \<open>(\<forall>m h'. m \<le> n \<longrightarrow> (\<lceil> i \<rceil>\<^bsub>wframe r with \<top>\<^esub>) h' \<longrightarrow> safe m c h' r g (\<lceil> i \<rceil>\<^bsub>wframe r with \<top>\<^esub>)) \<Longrightarrow>
    (\<lceil> i \<rceil>\<^bsub>wframe r with \<top>\<^esub>) h \<Longrightarrow>
    safe n (c\<^sup>\<star>) h r g (\<lceil> i \<rceil>\<^bsub>wframe r with \<top>\<^esub>)\<close>
  apply (induct n arbitrary: i h)
   apply force
  apply (clarsimp simp add: le_Suc_eq)
  apply (rule safe_suc)
     apply blast
    apply (force simp add: opstep_iff)
    (* subgoal *)
   apply (simp add: opstep_iff)
   apply (elim disjE)
    apply (simp add: safe_skip'; fail)
   apply (clarsimp simp add: all_conj_distrib)
   apply (rule_tac q=\<open>\<lceil> i \<rceil>\<^bsub>wframe r with \<top>\<^esub>\<close> in safe_seq, blast)
   apply force
    (* done *)
  apply (force simp add: wsstable_step)
  done

lemma safe_iter:
  \<open>(\<And>h n. p' h \<Longrightarrow> safe n c h r g q') \<Longrightarrow>
    p \<le> i \<Longrightarrow>
    \<lceil> i \<rceil>\<^bsub>wframe r with \<top>\<^esub> \<le> p' \<Longrightarrow>
    q' \<le> i \<Longrightarrow>
    \<lceil> i \<rceil>\<^bsub>wframe r with \<top>\<^esub> \<le> q \<Longrightarrow>
    p h \<Longrightarrow>
    safe n (c\<^sup>\<star>) h r g q\<close>
  by (metis (full_types) predicate1D safe_iter' safe_postpred_mono wsstable_stronger)

subsubsection \<open> Nondeterminism \<close>

lemma safe_ndet:
  \<open>(\<forall>m\<le>n. safe m c1 h r g q) \<Longrightarrow>
    (\<forall>m\<le>n. safe m c2 h r g q) \<Longrightarrow>
    safe n (c1 \<^bold>+ c2) h r g q\<close>
  apply (induct n arbitrary: c1 c2 h)
   apply blast
  apply (rule safe_suc)
     apply blast
    apply (rule opstep_act_cases)
      apply blast
     apply (force simp add: opstep_iff)
    apply (clarsimp simp add: opstep_iff safe_suc_iff le_Suc_eq, metis)
   apply (clarsimp simp add: opstep_iff safe_suc_iff le_Suc_eq all_conj_distrib imp_conjR)
   apply (metis (no_types, lifting) order.refl fst_conv opstep_tau_preserves_heap safe_step_monoD)
  apply (clarsimp simp add: opstep_iff safe_suc_iff le_Suc_eq all_conj_distrib imp_conjR)
  apply (metis safe_step_monoD)
  done

subsubsection \<open> Safe Frame \<close>

(*
lemma safe_frame_left:
  fixes h1 :: \<open>'a :: cancel_perm_alg\<close>
  shows
  \<open>safe n c h2 r g q2 \<Longrightarrow>
    all_atom_comm (unframe_safe (rel_lift ((=) hf))) c \<Longrightarrow>
    q1 h1 \<Longrightarrow>
    h1 ## h2 \<Longrightarrow>
    safe n c (h1 + h2) r g (q1 \<^emph> q2)\<close>
  apply (induct rule: safe.inducts)
   apply force
  apply (rule safe_suc)
     apply (metis sepconj_def)
    apply (metis fst_conv opstep_tau_preserves_heap partial_le_part_right)
   apply clarsimp
  apply (drule opstep_unframe_left)
  apply (metis opstep_unframe_left)
  sledgehammer
  oops
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

definition
  \<open>rel_disjoint_sync r1 r2 \<equiv>
    \<forall>h1 h2 h'.
    Ex (r1 h1) \<longrightarrow>
    Ex (r2 h2) \<longrightarrow>
    (\<exists>x1 x2. x1 ## x2 \<and> (h1 + h2) = x1 + x2 \<and> (\<exists>y1 y2. y1 ## y2 \<and> h' = y1 + y2 \<and> r1 x1 y1 \<and> r2 x2 y2)) \<longrightarrow>
    (\<exists>h1' h2'. h1' ## h2' \<and> h' = h1' + h2' \<and> r1 h1 h1' \<and> r2 h2 h2')\<close>

definition rel_sepadd_sync :: \<open>('a::perm_alg \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool)\<close> (infixr \<open>\<^emph>\<^emph>\<^sub>S\<close> 70) where
  \<open>rel_sepadd_sync r1 r2 \<equiv> \<lambda>a b.
    \<exists>x1 x2. x1 ## x2 \<and> a = x1 + x2 \<and> (\<exists>y1 y2. y1 ## y2 \<and> b = y1 + y2 \<and> r1 x1 y1 \<and> r2 x2 y2)\<close>

lemma
  \<open>Ex (r1 h1) \<Longrightarrow>
    Ex (r2 h1) \<Longrightarrow>
    (r1 \<^emph>\<^emph>\<^sub>S r2) (h1 + h2) h' \<Longrightarrow>
    \<exists>h1' h2'. h1' ## h2' \<and> h' = h1' + h2' \<and> r1 h1 h1' \<and> r2 h2 h2'\<close>
  oops

lemma safe_parallel_skip:
  \<open>safe n Skip h1 (r1 \<squnion> g2) g1 (\<lceil> q1 \<rceil>\<^bsub>wframe r1 \<squnion> g2 with \<top>\<^esub>) \<Longrightarrow>
    safe n Skip h2 (r2 \<squnion> g1) g2 (\<lceil> q2 \<rceil>\<^bsub>wframe r2 \<squnion> g1 with \<top>\<^esub>) \<Longrightarrow>
    h1 ## h2 \<Longrightarrow>
    rel_add_preserve r \<Longrightarrow>
    safe n Skip (h1 + h2) (r1 \<^emph>\<^emph>\<^sub>S r2) (g1 \<squnion> g2) (\<lceil> q1 \<rceil>\<^bsub>wframe r1 \<squnion> g2 with \<top>\<^esub> \<^emph> \<lceil> q2 \<rceil>\<^bsub>wframe r2 \<squnion> g1 with \<top>\<^esub>)\<close>
  apply (induct n arbitrary: h1 h2)
   apply force
  apply (intro safe_suc)
     apply (clarsimp simp add: safe_suc_iff sepconj_def, blast)
    apply force
   apply force
  apply (clarsimp simp add: safe_suc_iff)

  apply (subst (asm)(5) wframe_with_def)
  apply (clarsimp simp add: framed_subresource_rel_def)
  oops


lemma safe_parallel:
  \<open>\<forall>m\<le>n. safe n c1 h1 (r \<squnion> g2) g1 (\<lceil> q1 \<rceil>\<^bsub>wframe r \<squnion> g2 with \<top>\<^esub>) \<Longrightarrow>
    \<forall>m\<le>n. safe n c2 h2 (r \<squnion> g1) g2 (\<lceil> q2 \<rceil>\<^bsub>wframe r \<squnion> g1 with \<top>\<^esub>) \<Longrightarrow>
    \<forall>hf. all_atom_comm (frame_pred_extends ((=) hf)) c1 \<Longrightarrow>
    \<forall>hf. all_atom_comm (frame_pred_extends ((=) hf)) c2 \<Longrightarrow>
    h1 ## h2 \<Longrightarrow>
    safe n (c1 \<parallel> c2) (h1 + h2) r (g1 \<squnion> g2) (\<lceil> q1 \<rceil>\<^bsub>wframe r \<squnion> g2 with \<top>\<^esub> \<^emph> \<lceil> q2 \<rceil>\<^bsub>wframe r \<squnion> g1 with \<top>\<^esub>)\<close>
  apply (induct n arbitrary: c1 c2 h1 h2)
   apply force
  apply (clarsimp simp add: le_Suc_eq safe_suc_iff[where r=\<open>_ \<squnion> _\<close>]
      all_conj_distrib all_ex_conjL imp_conjR)
  apply (rule safe_suc)
     apply blast
    (* subgoal *)
    apply (clarsimp simp add: opstep_iff)
    apply (intro conjI)
     apply (metis fst_conv opstep_tau_preserves_heap)
    apply clarsimp
    apply (meson change_state_mono order.trans inf_sup_ord(3) partial_le_plus partial_le_plus2;fail)
    (* done *)
   apply (clarsimp simp add: opstep_iff)
   apply (elim disjE exE conjE)
     apply clarsimp
     apply (rule safe_skip)
  oops



definition
  \<open>rel_sepadd2 r1 r2 \<equiv>
    \<lambda>x y.
      (\<exists>x1 y1 h2.
        x1 ## h2 \<and> y1 ## h2 \<and>
        x = x1 + h2 \<and> y = y1 + h2 \<and>
        Ex (r2 h2) \<and>
        r1 x1 y1) \<or>
      (\<exists>h1 x2 y2.
        h1 ## x2 \<and> h1 ## y2 \<and>
        x = h1 + x2 \<and> y = h1 + y2 \<and>
        Ex (r1 h1) \<and>
        r2 x2 y2)
\<comment> \<open> \<or>
      (\<exists>hf hf' x1 x2.
        hf ## x1 \<and>
        hf ## x2 \<and>
        x1 ## x2 \<and>
        hf' ## x1 \<and>
        hf' ## x2 \<and>
        x = hf + x1 + x2 \<and>
        (\<exists>y1.
          hf' ## y1 \<and>
          y1 ## x2 \<and>
          y = hf' + y1 + x2 \<and>
          r1 (hf + x1) (hf' + y1) \<and> Ex (r2 (hf + x2))) \<or>
        (\<exists>y2.
          hf' ## y2 \<and>
          x1 ## y2 \<and>
          y = hf' + x1 + y2 \<and>
          r2 (hf + x2) (hf' + y2) \<and> Ex (r1 (hf + x1))))
\<close>\<close>

definition
  \<open>rel_sepdisjoint2 r1 r2 \<equiv>
    \<forall>h1 h2. Ex (r1 h1) \<longrightarrow> Ex (r2 h2) \<longrightarrow> h1 ## h2 \<longrightarrow>
      (\<forall>h1x h2x. Ex (r1 h1x) \<longrightarrow> Ex (r2 h2x) \<longrightarrow> h1x ## h2x \<longrightarrow>
        h1x + h2x = h1 + h2 \<longrightarrow> h1x = h1 \<and> h2x = h2)\<close>

lemma
  \<open>rel_sepadd2 r1 r2 (h1 + h2) h' \<Longrightarrow>
    rel_sepdisjoint2 r1 r2 \<Longrightarrow>
    \<forall>h1a h2a h1b h2b.
      pre_state r1 h1a \<longrightarrow> pre_state r2 h2a \<longrightarrow>
      h1a ## h2a \<longrightarrow>
      pre_state r1 h1b \<longrightarrow> pre_state r1 h2b \<longrightarrow> 
      h1b ## h2b \<longrightarrow>
      h1a + h2a = h1b + h2b \<longrightarrow>
      h1a = h1b \<and> h2a = h2b \<Longrightarrow>
    r1 h1 h1' \<Longrightarrow>
    r2 h2 h2' \<Longrightarrow>
    h1 ## h2 \<Longrightarrow>
    h1 ## h2' \<Longrightarrow>
    h1' ## h2 \<Longrightarrow>
    (\<exists>h1''. r h1 h1'' \<and> h1'' ## h2 \<and> h' = h1'' + h2) \<or>
    (\<exists>h2''. r h2 h2'' \<and> h1 ## h2'' \<and> h' = h1 + h2'')\<close>
  apply (simp add: rel_sepadd2_def)
  apply (elim disjE exE conjE)
   apply (rule disjI1)
  oops


definition \<open>rel_changes r x \<equiv> (\<exists>y. y \<noteq> x \<and> r x y) \<or> (\<exists>y. y \<noteq> x \<and> r y x)\<close>

definition
  \<open>rel_sepdisjoint r1 r2 \<equiv>
    (\<forall>s2 x1 y1. x1 ## s2 \<longrightarrow> r1 x1 y1 \<longrightarrow> Ex (r2 s2) \<longrightarrow> y1 ## s2) \<and>
    (\<forall>s1 x2 y2. s1 ## x2 \<longrightarrow> Ex (r1 s1) \<longrightarrow> r2 x2 y2 \<longrightarrow> s1 ## y2)\<close>

definition rel_sepadd :: \<open>('a::perm_alg \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool)\<close> (infixr \<open>\<^emph>\<^emph>\<close> 70) where
  \<open>rel_sepadd r1 r2 \<equiv> \<lambda>a b.
    (\<exists>s2. Ex (r2 s2) \<and> (\<exists>x1. x1 ## s2 \<and> a = x1 + s2 \<and> (\<exists>y1. y1 ## s2 \<and> b = y1 + s2 \<and> r1 x1 y1))) \<or>
    (\<exists>s1. Ex (r1 s1) \<and> (\<exists>x2. s1 ## x2 \<and> a = s1 + x2 \<and> (\<exists>y2. s1 ## y2 \<and> b = s1 + y2 \<and> r2 x2 y2)))\<close>

lemma rel_sepaddI1:
  \<open>Ex (r2 s2) \<Longrightarrow>
    x1 ## s2 \<Longrightarrow>
    a = x1 + s2 \<Longrightarrow>
    y1 ## s2 \<Longrightarrow> b = y1 + s2 \<Longrightarrow>
    r1 x1 y1 \<Longrightarrow>
    (r1 \<^emph>\<^emph> r2) a b\<close>
  by (metis rel_sepadd_def)

lemma rel_sepaddI2:
  \<open>Ex (r1 s1) \<Longrightarrow>
    s1 ## x2 \<Longrightarrow>
    a = s1 + x2 \<Longrightarrow>
    s1 ## y2 \<Longrightarrow>
    b = s1 + y2 \<Longrightarrow>
    r2 x2 y2 \<Longrightarrow>
    (r1 \<^emph>\<^emph> r2) a b\<close>
  by (metis rel_sepadd_def)


lemma opstep_local_skip_left_par':
  \<open>opstep a s s' \<Longrightarrow> a = Local \<Longrightarrow> snd s = Skip \<parallel> c2 \<Longrightarrow> \<exists>c2'. snd s' = Skip \<parallel> c2'\<close>
  by (induct rule: opstep.inducts) force+

lemma opstep_local_skip_left_parD:
  \<open>opstep Local (h, Skip \<parallel> c2) s' \<Longrightarrow> \<exists>h' c2'. s' = (h', Skip \<parallel> c2')\<close>
  by blast


definition shared ::
  \<open>('a::perm_alg \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
    ('a \<Rightarrow> bool)\<close> where
  \<open>shared r r1 r2 \<equiv> \<lambda>x.
    \<forall>h1 h1' h2 h2' y.
      h2 ## x \<longrightarrow>
      h1 ## x \<longrightarrow>
      h1 ## h2 \<longrightarrow>
      h1' ## x \<longrightarrow>
      h2' ## x \<longrightarrow>
      h1' ## h2' \<longrightarrow>
      r (h1 + h2 + x) (h1' + h2' + y) \<longrightarrow>
      (r1 (h1 + x) (h1' + y) \<and> r2 h2 h2' \<longleftrightarrow> r1 h1 h1' \<and> r2 (h2 + x) (h2' + y))\<close>


lemma safe_parallel_splitting:
  \<open>safe n c1 h1 (r1 \<squnion> g2) g1 q1 \<Longrightarrow>
    safe n c2 h2 (r2 \<squnion> g1) g2 q2 \<Longrightarrow>
    all_atom_comm frame_rearranging c1 \<Longrightarrow>
    all_atom_comm frame_rearranging c2 \<Longrightarrow>
    all_atom_comm (\<lambda>b2. all_atom_comm (\<lambda>b1. \<forall>x. pre_change_state b1 \<sqinter> pre_change_state b2 = \<bottom>) c1) c2 \<Longrightarrow>
    h1 ## h2 \<Longrightarrow>
    pre_state g1 h1 \<Longrightarrow>
    pre_state g2 h2 \<Longrightarrow>
    rel_sepdisjoint r1 r2 \<Longrightarrow>
    rel_sepdisjoint g1 g2 \<Longrightarrow>
    safe n (c1 \<parallel> c2) (h1 + h2) (r1 \<^emph>\<^emph> r2) (g1 \<^emph>\<^emph> g2) (q1 \<^emph> q2)\<close>
  apply (induct n arbitrary: c1 c2 h1 h2)
   apply force
  apply (clarsimp simp add: le_Suc_eq safe_suc_iff[where r=\<open>_ \<squnion> _\<close>]
      all_conj_distrib all_ex_conjL imp_conjR)
  apply (rule safe_suc)
     apply (clarsimp simp add: can_compute_def opstep_iff,
      metis fst_conv opstep_frame_rearranging snd_conv)
    apply blast
   apply (clarsimp simp add: can_compute_def opstep_iff)
   apply (intro conjI)
     apply (metis fst_conv opstep_tau_preserves_heap)
    apply clarsimp
    apply (erule disjE)
     apply (clarsimp simp add: can_compute_def opstep_iff)

     apply (rule rel_sepaddI1)
           apply (force simp add: pre_state_def)
  oops


lemma safe_parallel_sharing:
  \<open>safe n c1 h1 (r \<squnion> g2) g1 q1 \<Longrightarrow>
    safe n c2 h2 (r \<squnion> g1) g2 q2 \<Longrightarrow>
    all_atom_comm frame_rearranging c1 \<Longrightarrow>
    all_atom_comm frame_rearranging c2 \<Longrightarrow>
    all_atom_comm (\<lambda>b2. all_atom_comm (\<lambda>b1. \<forall>x. pre_change_state b1 \<sqinter> pre_change_state b2 = \<bottom>) c1) c2 \<Longrightarrow>
    h1 ## h2 \<Longrightarrow>
    pre_state g1 h1 \<Longrightarrow>
    pre_state g2 h2 \<Longrightarrow>
    rel_sepdisjoint r1 r2 \<Longrightarrow>
    rel_sepdisjoint g1 g2 \<Longrightarrow>
    safe n (c1 \<parallel> c2) (h1 + h2) r (g1 \<squnion> g2) (q1 \<^emph> q2)\<close>
  apply (induct n arbitrary: c1 c2 h1 h2)
   apply force
  apply (clarsimp simp add: le_Suc_eq safe_suc_iff[where r=\<open>_ \<squnion> _\<close>]
      all_conj_distrib all_ex_conjL imp_conjR)
  apply (rule safe_suc)
     apply (clarsimp simp add: can_compute_def opstep_iff,
      metis fst_conv opstep_frame_rearranging snd_conv)
    apply blast
   apply (clarsimp simp add: can_compute_def opstep_iff)
   apply (intro conjI)
     apply (metis fst_conv opstep_tau_preserves_heap)
    apply clarsimp
    apply (erule disjE)
     apply (clarsimp simp add: can_compute_def opstep_iff)

  oops


subsubsection \<open> Frame rule \<close>

lemma safe_frame:
  \<open>safe n c h r g q \<Longrightarrow>
    all_atom_comm (frame_pred_extends f) c \<Longrightarrow>
    frame_pred_extends f r \<Longrightarrow>
    frame_pred_safe f g \<Longrightarrow>
    h ## hf \<Longrightarrow>
    f hf \<Longrightarrow>
    safe n c (h + hf) r g (q \<^emph> f)\<close>
proof (induct arbitrary: hf rule: safe.induct)
  case (safe_nil c h r g q)
  then show ?case by fast
next
  case (safe_suc h c q g n r)
(*
  obtain hf' where
    \<open>f hf'\<close>
    \<open>h' ## hf'\<close>
    \<open>opstep a (h + hf, c) (h' + hf', c')\<close>
    using safe_step opstep_frame_pred_extendsD safe_step
    by (metis fst_conv snd_conv)
  moreover then have \<open>safe n c' (h' + hf') r g (q \<^emph> f)\<close>
    using safe_step
    by (metis opstep_preserves_all_atom_comm)
  ultimately *)
  then show ?case
    apply -
    apply (rule safe.safe_suc)
    sorry
qed

(*
lemma safe_frame2:
  \<open>safe n c h r g q \<Longrightarrow>
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
  shows \<open>safe n c h r g q\<close>
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
    using safe_ndet[of n c1 h r g q c2]
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