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

inductive opstep :: \<open>act \<Rightarrow> ('h::perm_alg) \<times> 'h comm \<Rightarrow> 'h \<times> 'h comm \<Rightarrow> bool\<close> where
  seq_left[intro!]:  \<open>opstep a (h, c1) (h', c1') \<Longrightarrow> opstep a (h, c1 ;; c2) (h', c1' ;; c2)\<close>
| seq_right[intro!]: \<open>opstep Tau (h, Skip ;; c2) (h, c2)\<close>
| ndet_tau_left[intro]:  \<open>opstep Tau (h, c1) (h', c1') \<Longrightarrow> opstep Tau (h, c1 \<^bold>+ c2) (h', c1' \<^bold>+ c2)\<close>
| ndet_tau_right[intro]: \<open>opstep Tau (h, c2) (h', c2') \<Longrightarrow> opstep Tau (h, c1 \<^bold>+ c2) (h', c1 \<^bold>+ c2')\<close>
| ndet_skip_left[intro!]:  \<open>opstep Tau (h, Skip \<^bold>+ c2) (h, c2)\<close>
| ndet_skip_right[intro!]: \<open>opstep Tau (h, c1 \<^bold>+ Skip) (h, c1)\<close>
| ndet_local_left[intro]:  \<open>opstep Local (h, c1) s' \<Longrightarrow> opstep Local (h, c1 \<^bold>+ c2) s'\<close>
| ndet_local_right[intro]: \<open>opstep Local (h, c2) s' \<Longrightarrow> opstep Local (h, c1 \<^bold>+ c2) s'\<close>
| par_left[intro]:  \<open>opstep a (h, s) (h', s') \<Longrightarrow> opstep a (h, s \<parallel> t) (h', s' \<parallel> t)\<close>
| par_right[intro]: \<open>opstep a (h, t) (h', t') \<Longrightarrow> opstep a (h, s \<parallel> t) (h', s \<parallel> t')\<close>
| par_skip_left[intro!]:  \<open>opstep Tau (h, Skip \<parallel> s2) (h, s2)\<close>
| par_skip_right[intro!]: \<open>opstep Tau (h, s1 \<parallel> Skip) (h, s1)\<close>
| iter_skip[intro]: \<open>opstep Tau (h, c\<^sup>\<star>) (h, Skip)\<close>
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
    a = Tau \<and> c1 = Skip \<and> s' = (h, c2) \<or>
    a = Tau \<and> c2 = Skip \<and> s' = (h, c1) \<or>
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

lemma opstep_act_cases:
  \<open>s \<midarrow>a\<rightarrow> s' \<Longrightarrow> (a = Tau \<Longrightarrow> s \<midarrow>Tau\<rightarrow> s' \<Longrightarrow> P) \<Longrightarrow> (a = Local \<Longrightarrow> s \<midarrow>Local\<rightarrow> s' \<Longrightarrow> P) \<Longrightarrow> P\<close>
  by (metis (full_types) act.exhaust)

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
    apply (metis less_eq_comm_no_constructorsD(3) less_eq_comm_subexprsD(6))
   apply (metis less_eq_comm_no_constructorsD(3) less_eq_comm_subexprsD(5))
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
    apply (metis less_eq_comm_no_constructorsD(4) less_eq_comm_subexprsD(6))
   apply (metis less_eq_comm_no_constructorsD(4) less_eq_comm_subexprsD(5))
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


section \<open> Termination and Abort \<close>

text \<open> TODO: distinguish safe termination from abort \<close>

definition \<open>can_compute s \<equiv> \<exists>a s'. s \<midarrow>a\<rightarrow> s'\<close>

lemma can_compute_iff:
  \<open>can_compute (h, Skip) \<longleftrightarrow> False\<close>
  \<open>can_compute (h, c1 ;; c2) \<longleftrightarrow> c1 = Skip \<or> can_compute (h,c1)\<close>
  \<open>can_compute (h, c1 \<^bold>+ c2) \<longleftrightarrow>
    c1 = Skip \<or> c2 = Skip \<or> can_compute (h,c1) \<or> can_compute (h,c2)\<close>
  \<open>can_compute (h, c1 \<parallel> c2) \<longleftrightarrow>
    c1 = Skip \<or> c2 = Skip \<or> can_compute (h,c1) \<or> can_compute (h,c2)\<close>
  \<open>can_compute (h, c\<^sup>\<star>) \<longleftrightarrow> True\<close>
  \<open>can_compute (h, Atomic b) \<longleftrightarrow> (\<exists>h'. b h h')\<close>
  unfolding can_compute_def
       apply (fastforce simp add: opstep_iff)
      apply (fastforce simp add: opstep_iff)
  subgoal
    apply (clarsimp simp add: opstep_iff)
    apply (rule iffI)
     apply force
    apply (elim disjE; clarsimp)
       apply blast
      apply blast
     apply (case_tac a)
      apply metis
     apply blast
    apply (case_tac a)
     apply metis
    apply blast
    done
  subgoal
    apply (clarsimp simp add: opstep_iff)
    apply (rule iffI)
     apply force
    apply (elim disjE; clarsimp)
       apply blast
      apply blast
     apply (case_tac a)
      apply metis
     apply blast
    apply (case_tac a)
     apply metis
    apply blast
    done
   apply (fastforce simp add: opstep_iff)
  apply (fastforce simp add: opstep_iff)
  done

lemma not_skip_can_compute:
  \<open>c \<noteq> Skip \<Longrightarrow> \<exists>y. g h y \<Longrightarrow> atoms_guarantee g c \<Longrightarrow> can_compute (h, c)\<close>
  by (induct c arbitrary: h)
    (fastforce simp add: can_compute_iff)+


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

section \<open> Safe \<close>

inductive safe
  :: \<open>nat \<Rightarrow> ('s::perm_alg) comm \<Rightarrow> 's \<Rightarrow>
        ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where
  safe_nil[intro!]: \<open>safe 0 c h r g q\<close>
| safe_step[intro]:
  \<open>\<comment> \<open> the command does not fail + respects the guarantee \<close>
    (h, c) \<midarrow>a\<rightarrow> (h', c') \<Longrightarrow>
    \<comment> \<open> the command is frame safe \<close>
    (\<forall>hf. all_atom_comm (frame_pred_safe ((=) hf)) c \<longrightarrow> h ## hf \<longrightarrow> h' ## hf \<longrightarrow> (h + hf, c) \<midarrow>a\<rightarrow> (h' + hf, c')) \<Longrightarrow>
    \<comment> \<open> local steps respect the guarantee \<close>
    (a = Local \<longrightarrow> g h h') \<Longrightarrow>
    \<comment> \<open> if the result is Skip, the postcondition is established + stable \<close>
    (c' = Skip \<longrightarrow> q h') \<Longrightarrow>
    \<comment> \<open> the subsequent execution is safe \<close>
    safe n c' h' r g q \<Longrightarrow>
    safe (Suc n) c h r g q\<close>
| safe_env[intro]:
  \<open>\<comment> \<open> env steps respect the rely \<close>
    r h h' \<Longrightarrow>
    \<comment> \<open> if the command is Skip, the postcondition is established \<close>
    c = Skip \<longrightarrow> q h \<Longrightarrow>
    \<comment> \<open> the subsequent execution is safe \<close>
    safe n c h' r g q \<Longrightarrow>
    safe (Suc n) c h r g q\<close>
| safe_no_env[intro]:
  \<open>\<nexists>h'. r h h' \<Longrightarrow> q h \<Longrightarrow> safe (Suc n) c h r g q\<close>

inductive_cases safe_zeroE[elim!]: \<open>safe 0 c s r g q\<close>
inductive_cases safe_sucE[elim]: \<open>safe (Suc n) c s r g q\<close>

subsection \<open> Proofs about safe \<close>

lemma safe_nil_iff[simp]:
  \<open>safe 0 c h r g q \<longleftrightarrow> True\<close>
  by force

lemma safe_suc_iff:
  \<open>safe (Suc n) c h r g q \<longleftrightarrow>
    (\<exists>h' c' a.
      (h, c) \<midarrow>a\<rightarrow> (h', c') \<and>
      (\<forall>hf.
        all_atom_comm (frame_pred_safe ((=) hf)) c \<longrightarrow>
        h ## hf \<longrightarrow>
        h' ## hf \<longrightarrow>
        (h + hf, c) \<midarrow>a\<rightarrow> (h' + hf, c')) \<and>
      (a = Local \<longrightarrow> g h h') \<and>
      (c' = Skip \<longrightarrow> q h') \<and>
      safe n c' h' r g q) \<or>
    (\<exists>h'.
      r h h' \<and>
      (c = Skip \<longrightarrow> q h) \<and>
      safe n c h' r g q) \<or>
    ((\<nexists>h'. r h h') \<and> q h)\<close>
  apply (rule iffI)
   apply clarsimp
   apply (erule safe_sucE; blast)
  apply (elim disjE exE conjE)
    apply (rule safe_step; blast)
   apply (rule safe_env; blast)
  apply (rule safe_no_env; blast)
  done

subsubsection \<open> Monotonicity \<close>

lemma safe_postpred_monoD:
  \<open>safe n c h r g q \<Longrightarrow> q \<le> q' \<Longrightarrow> safe n c h r g q'\<close>
  by (induct rule: safe.induct) fast+

lemmas safe_postpred_mono = safe_postpred_monoD[rotated]

lemma safe_guarantee_monoD:
  \<open>safe n c h r g q \<Longrightarrow> g \<le> g' \<Longrightarrow> safe n c h r g' q\<close>
  by (induct rule: safe.induct) fast+

lemmas safe_guarantee_mono = safe_guarantee_monoD[rotated]

(* n.b. prestate condition under \<open>r \<le> r'\<close> is the same as \<open>pre_state r' = pre_state r\<close> *)
lemma safe_rely_monoD:
  \<open>safe n c h r g q \<Longrightarrow> r \<le> r' \<Longrightarrow> pre_state r' \<le> pre_state r \<Longrightarrow> safe n c h r' g q\<close>
  by (induct rule: safe.induct)
    (simp add: le_fun_def safe_suc_iff pre_state_def fun_eq_iff, blast)+

lemmas safe_rely_mono = safe_rely_monoD[rotated]

lemma safe_step_monoD:
  assumes inductive_assms:
    \<open>safe n c h r g q\<close>
    \<open>m \<le> n\<close>
  shows
    \<open>safe m c h r g q\<close>
  using inductive_assms
  by (induct arbitrary: m rule: safe.inducts)
    (auto simp add: le_Suc_iff0 safe_suc_iff)+
    (* a little slow *)

subsubsection \<open> Skip \<close>

lemma safe_skip_basic:
  \<open>(\<lceil> q \<rceil>\<^bsub>r\<^esub>) h \<Longrightarrow> safe n Skip h r g (\<lceil> q \<rceil>\<^bsub>r\<^esub>)\<close>
proof (induct n arbitrary: h q)
  case (Suc n)
  then show ?case
    apply (clarsimp simp add: safe_suc_iff opstep_iff)
    apply (frule spec, drule mp, blast)
    apply (rename_tac h')
    apply (drule_tac x=\<open>\<lceil> q \<rceil>\<^bsub>r\<^esub>\<close> and y=h' in meta_spec2, drule meta_mp)
     apply blast
    apply force
    done
qed fast

lemma safe_skip:
  \<open>p h \<Longrightarrow> \<lceil> p \<rceil>\<^bsub>r\<^esub> \<le> q \<Longrightarrow> safe n Skip h r g q\<close>
  by (blast intro!: safe_postpred_monoD[OF safe_skip_basic[where q=p]])

subsubsection \<open> Sequencing \<close>

lemma safe_seq_right:
  \<open>safe n c1 h r g q \<Longrightarrow> safe n (c1 ;; c2) h r g q\<close>
  apply (induct rule: safe.inducts)
     apply force
    apply (rule safe_step, blast, blast, blast, blast, blast, blast)
  apply blast
  done

lemma opstep_seq_assoc_left:
  \<open>opstep a s s' \<Longrightarrow> snd s = cx ;; cy ;; cz \<Longrightarrow>
    if cx = Skip
    then snd s' = cy ;; cz \<and> opstep a (fst s, (cx ;; cy) ;; cz) (fst s', cy ;; cz)
    else \<exists>cx'. snd s' = cx' ;; cy ;; cz \<and> opstep a (fst s, (cx ;; cy) ;; cz) (fst s', (cx' ;; cy) ;; cz)\<close>
  by (induct arbitrary: cx cy cz rule: opstep.inducts) fastforce+

lemma safe_seq_assoc_left:
  \<open>safe n c h r g q \<Longrightarrow>
    c = (c1 ;; c2 ;; c3) \<Longrightarrow>
    safe n ((c1 ;; c2) ;; c3) h r g q\<close>
  apply (induct arbitrary: c1 c2 c3 rule: safe.inducts)
     apply force
    apply clarsimp
    apply (frule opstep_seq_assoc_left, force)
    apply (clarsimp split: if_splits; blast)
   apply blast
   apply blast
  done

lemma safe_seq:
  \<open>safe n1 c1 h1 r g1 q1 \<Longrightarrow>
    (\<And>h. q1 h \<Longrightarrow> safe n2 c2 h r g2 q2) \<Longrightarrow>
    safe (n1 + n2) (c1 ;; c2) h r (g1 OO g2\<^sup>=\<^sup>=) q2\<close>
  apply (induct arbitrary: n2 c2 g2 q2 rule: safe.inducts)
     apply clarsimp
  oops

lemma safe_seq:
  \<open>(\<And>h n. p1 h \<Longrightarrow> safe n c1 h r g p2) \<Longrightarrow>
    (\<And>h n. p2 h \<Longrightarrow> safe n c2 h r g p3) \<Longrightarrow>
    p1 h \<Longrightarrow>
    safe n (c1 ;; c2) h r g p3\<close>
proof (induct n)
  case 0
  then show ?case by force
next
  case (Suc n)
  { fix c
    assume
      \<open>safe n c h r g p3\<close>
      \<open>c = c1 ;; c2\<close>
      \<open>\<And>h n. p1 h \<Longrightarrow> safe n c1 h r g p2\<close>
      \<open>\<And>h n. p2 h \<Longrightarrow> safe n c2 h r g p3\<close>
      \<open>p1 h\<close>
    then have \<open>safe (Suc n) (c1 ;; c2) h r g p3\<close>
      apply (induct rule: safe.inducts)
      apply clarsimp
      sorry
  }
  then show ?case
    using Suc
    by force
qed

subsubsection \<open> Nondeterminism \<close>

lemma safe_ndet_left:
  \<open>safe n c1 h r g q \<Longrightarrow> safe n (c1 \<^bold>+ c2) h r g q\<close>
  apply (induct arbitrary: rule: safe.inducts)
     apply blast
    apply (case_tac a; (simp add: opstep_iff, blast))
   apply blast
  apply blast
  done

lemma safe_ndet_right:
  \<open>safe n c2 h r g q \<Longrightarrow> safe n (c1 \<^bold>+ c2) h r g q\<close>
  apply (induct rule: safe.inducts)
     apply blast
    apply (case_tac a; (simp add: opstep_iff, blast))
   apply blast
  apply blast
  done

subsubsection \<open> Disjoint \<close>

definition \<open>disjoint_closed_rel r \<equiv>
  \<forall>x y x' y'. r x y \<longrightarrow> r x' y' \<longrightarrow> x ## x' \<longrightarrow> y ## y' \<longrightarrow> r (x + x') (y + y')\<close>

lemma safe_parallel_right:
  assumes
    \<open>safe n1 c1 h1 r1 g1 q1\<close>
    \<open>r1 = r \<squnion> g2\<close>
    \<open>h1 ## h2\<close>
    \<open>atoms_guarantee g2 c2\<close>
    \<open>tight_reflp g2\<close>
    \<open>pre_state g1 h1\<close>
    \<open>pre_state g2 h2\<close>
    \<open>frame_pred_maintains (g2 h2) g1\<close>
    \<open>frame_pred_maintains (g1 h1) g2\<close>
    \<open>frame_pred_maintains (g2 h2) r\<close>
    \<open>frame_pred_maintains ((g1 \<squnion> g2) (h1 + h2)) r\<close>
  shows
    \<open>safe n1 (c1 \<parallel> c2) (h1 + h2) r (g1 \<squnion> g2) (q1 \<^emph> q2)\<close>
  using assms
  apply (induct arbitrary: c2 h2 r g2 q2 rule: safe.inducts)
     apply force
    (* subgoal (* L1 *) *)
    apply clarsimp
    apply (rule safe_step)
  subgoal sorry
  subgoal sorry
  subgoal sorry
  subgoal sorry
  subgoal sorry
      (* done (* L1 *) *)
      (* subgoal (* L1 *) *)
   apply clarsimp
   apply (rename_tac r)
   apply (rename_tac h1 h1' c1 q1 n1 g1 c2 h2 r g2 q2)
   apply (erule disjE)
    
    apply (frule frame_pred_maintainsD[of \<open>_ h2\<close>], assumption)
      apply (rule_tac r=g2 in tight_reflpD1, blast)
      apply fast

  sorry

lemma safe_parallel:
  \<open>safe n2 s2 h2 r2 g2 q2 \<Longrightarrow>
    r2 = r \<squnion> g1 \<Longrightarrow>
    safe n1 c1 h1 r1 (r \<squnion> g2) q1 \<Longrightarrow>
    h1 ## h2 \<Longrightarrow>
    g = g1 \<squnion> g2 \<Longrightarrow>
    safe (n1 + n2) (c1 \<parallel> c2) (h1 + h2) r g (q1 \<^emph> q2)\<close>
  apply (induct arbitrary: r g1 g rule: safe.inducts)
     apply clarsimp
     apply (rename_tac h2 g2 q2 r g1)
  sorry


lemma safe_frame:
  \<open>safe n c h r g q \<Longrightarrow>
    all_atom_comm (frame_pred_extends f) c \<Longrightarrow>
    frame_pred_extends f r \<Longrightarrow>
    frame_pred_safe f g \<Longrightarrow>
    \<comment> \<open> needed for the no-env step \<close>
    frame_step_subframe f r \<Longrightarrow>
    h ## hf \<Longrightarrow>
    f hf \<Longrightarrow>
    safe n c (h + hf) r g (q \<^emph> f)\<close>
proof (induct arbitrary: hf rule: safe.induct)
  case safe_nil
  then show ?case by fast
next
  case (safe_step h c a h' c' g q n r)
  obtain hf' where
    \<open>f hf'\<close>
    \<open>h' ## hf'\<close>
    \<open>opstep a (h + hf, c) (h' + hf', c')\<close>
    using safe_step opstep_frame_pred_extendsD safe_step
    by (metis fst_conv snd_conv)
  moreover then have \<open>safe n c' (h' + hf') r g (q \<^emph> f)\<close>
    using safe_step
    by (metis opstep_preserves_all_atom_comm)
  ultimately show ?case
    using safe_step.prems safe_step.hyps(1-5)
    apply -
    apply (rule safe.safe_step)
        apply assumption
       apply (blast intro: opstep_frame)
      apply (simp add: frame_pred_safe_def; fail)
     apply (metis sepconj_def)
    apply blast
    done
next
  case (safe_env r h h' c q n g)
  then show ?case
    apply -
    apply (clarsimp simp add: frame_pred_extends_def[of f r])
    apply (drule spec2, drule mp, assumption, drule spec, drule mp, assumption)
    apply (metis safe.safe_env sepconj_def)
    done
next
  case (safe_no_env r h q n c g)
  then show ?case
    apply -
    apply (rule safe.safe_no_env)
     apply (force simp add: frame_step_subframe_def)
    apply (fastforce simp add: sepconj_def)
    done
qed

lemma safe_frame2:
  \<open>safe n c h r g q \<Longrightarrow>
    all_atom_comm (frame_pred_maintains f) c \<Longrightarrow>
    frame_pred_extends f r \<Longrightarrow>
    frame_pred_closed f g \<Longrightarrow>
    \<comment> \<open> needed for the no-env step \<close>
    frame_step_subframe f r \<Longrightarrow>
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
next
  case (safe_env r h h' c q n g)
  then show ?case
    apply -
    apply (clarsimp simp add: frame_pred_extends_def[of f r])
    apply (drule spec2, drule mp, assumption, drule spec, drule mp, assumption)
    apply (metis safe.safe_env sepconj_def)
    done
next
  case (safe_no_env r h q n c g)
  then show ?case
    apply -
    apply (rule safe.safe_no_env)
     apply (force simp add: frame_step_subframe_def)
    apply (fastforce simp add: sepconj_def)
    done
qed


section \<open> Soundness \<close>

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
    and \<open>frame_closed g\<close>
  shows \<open>safe n c h r g q\<close>
  using assms
proof (induct c r g p q arbitrary: n h rule: rgsat.inducts)
  case (rgsat_skip p r q g as h)
  then show ?case
    by (force intro!: safe_skip[where p=p])
next
  case (rgsat_iter c r g p' q' p i q)
  then show ?case
    apply clarsimp
    sorry
next
  case (rgsat_seq c1 r g p1 p2 c2 p3)
  then show ?case
    using safe_seq
    by (clarsimp, blast)
next
  case (rgsat_ndet c1 r g1 p q1 c2 g2 q2 g q)
  then show ?case
    by (metis safe_guarantee_mono safe_ndet_left safe_postpred_mono)
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
  case (rgsat_atom p b q f g p' r q')
  moreover obtain h1 h2 where A1:
    \<open>h1 ## h2\<close> \<open>h = h1 + h2\<close> \<open>p h1\<close> \<open>f h2\<close>
    using rgsat_atom
    by (simp add: sepconj_def le_fun_def, blast)
  moreover obtain h1' where A2:
    \<open>b h1 h1'\<close> \<open>q h1'\<close>
    using rgsat_atom A1
    by (force simp add: pre_state_def le_fun_def)
  moreover obtain h2' where A3:
    \<open>h1' ## h2'\<close> \<open>b (h1 + h2) (h1' + h2')\<close> \<open>f h2'\<close>
    using rgsat_atom A1 A2
     by (metis frame_pred_extends_def)
  ultimately show ?case
    apply (cases n, blast)
    apply clarsimp
    apply (rule safe.safe_step[where a=Local and c'=Skip])
        apply (simp add: opstep_iff; fail)
       apply (simp add: opstep_iff frame_pred_safe_def; fail)
      apply force
     apply (metis rev_predicate1D sepconj_iff wsstable_stronger)
    apply (rule safe_skip[of \<open>\<lceil> q \<^emph> f \<rceil>\<^bsub>r\<^esub>\<close>])
     apply (metis predicate1D sepconj_def wsstable_stronger)
    apply (metis le_disj_eq_absorb wsstable_absorb1)
    done
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
    done
  ultimately show ?case
    using rgsat_frame
    by (force intro!: safe_frame2 simp add: frame_pred_closed_def)
next
  case (rgsat_weaken c r' g' p' q' p q r g)
  then show ?case sorry
qed

end