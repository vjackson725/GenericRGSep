theory RGSep
  imports Stabilisation
begin

subsection \<open> Framed step relation \<close>

context perm_alg
begin

text \<open>
  This predicate ensures that an update between two subresources preserve the rest of the heap.
  We need this in the perm_alg case, when we don't necessarily have a unit.
\<close>

definition
  \<open>framed_subresource_rel p ha ha' h h' \<equiv>
    (\<exists>hf. p hf \<and> ha ## hf \<and> ha' ## hf \<and> h = ha + hf \<and> h' = ha' + hf)\<close>

abbreviation
  \<open>weak_framed_subresource_rel p ha ha' h h' \<equiv>
    ha = h \<and> ha' = h' \<or> framed_subresource_rel p ha ha' h h'\<close>

lemma framed_subresource_relI:
  \<open>p hf \<Longrightarrow> ha ## hf \<Longrightarrow> ha' ## hf \<Longrightarrow> h = ha + hf \<Longrightarrow> h' = ha' + hf \<Longrightarrow>
    framed_subresource_rel p ha ha' h h'\<close>
  by (force simp add: framed_subresource_rel_def)

lemma framed_subresource_rel_refl[intro!]:
  \<open>weak_framed_subresource_rel p h h' h h'\<close>
  by (simp add: framed_subresource_rel_def)

lemma framed_subresource_rel_frame_second:
  \<open>framed_subresource_rel \<top> ha ha' h h' \<Longrightarrow>
    h ## hf \<Longrightarrow>
    h' ## hf \<Longrightarrow>
    framed_subresource_rel \<top> ha ha' (h + hf) (h' + hf)\<close>
  using disjoint_add_swap2 partial_add_assoc2
  by (simp add: framed_subresource_rel_def, meson)

lemma framed_subresource_rel_frame:
  \<open>framed_subresource_rel \<top> ha ha' h h' \<Longrightarrow>
    h ## hf \<Longrightarrow>
    h' ## hf \<Longrightarrow>
    framed_subresource_rel \<top> ha ha' (h + hf) (h' + hf)\<close>
  using disjoint_add_swap2 partial_add_assoc2
  by (simp add: framed_subresource_rel_def, meson)

lemma framed_subresource_rel_sym:
  \<open>framed_subresource_rel p a b a' b' \<Longrightarrow> framed_subresource_rel p b a b' a'\<close>
  using framed_subresource_rel_def by auto

end

lemma (in multiunit_sep_alg) mu_sep_alg_compatible_framed_subresource_rel_iff:
  assumes
    \<open>compatible h h'\<close>
    \<open>p (unitof h)\<close>
  shows
  \<open>weak_framed_subresource_rel p ha ha' h h' \<longleftrightarrow> framed_subresource_rel p ha ha' h h'\<close>
  using assms
  apply (simp add: framed_subresource_rel_def)
  apply (metis compatible_then_same_unit unitof_disjoint2 unitof_is_unitR2)
  done

lemma (in sep_alg) sep_alg_framed_subresource_rel_iff:
  \<open>p 0 \<Longrightarrow>
    weak_framed_subresource_rel p ha ha' h h' \<longleftrightarrow> framed_subresource_rel p ha ha' h h'\<close>
  apply (simp add: framed_subresource_rel_def)
  apply (metis sepadd_0_right zero_disjointR)
  done

subsection \<open> Relation framing \<close>

text \<open> embellish a relation with frames \<close>

context perm_alg
begin

definition frame_with :: \<open>('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool)\<close>
  (\<open>(frame _ with _)\<close> [0,50] 50)
  where
  \<open>frame_with r p \<equiv> \<lambda>h h'. (\<exists>hs hs'. r hs hs' \<and> framed_subresource_rel p hs hs' h h')\<close>

lemma frame_with_frame_rightI:
  \<open>p h2 \<Longrightarrow> r h1 h1' \<Longrightarrow> h' = h1' + h2 \<Longrightarrow> h1 ## h2 \<Longrightarrow> h1' ## h2 \<Longrightarrow>
    (frame r with p) (h1 + h2) h'\<close>
  apply (simp add: frame_with_def framed_subresource_rel_def)
  apply blast
  done

lemma frame_with_frame_leftI:
  \<open>p h1 \<Longrightarrow> r h2 h2' \<Longrightarrow> h' = h1 + h2' \<Longrightarrow> h1 ## h2 \<Longrightarrow> h1 ## h2' \<Longrightarrow>
    (frame r with p) (h1 + h2) h'\<close>
  apply (simp add: frame_with_def framed_subresource_rel_def)
  apply (meson disjoint_sym_iff partial_add_commute)
  done

lemma framed_rel_step_wsstable:
  \<open>framed_subresource_rel f hs hs' h h' \<Longrightarrow>
    r hs hs' \<Longrightarrow>
    (\<lceil> p \<rceil>\<^bsub>frame r with f\<^esub>) h \<Longrightarrow>
    (\<lceil> p \<rceil>\<^bsub>frame r with f\<^esub>) h'\<close>
  apply (clarsimp simp add: frame_with_def wsstable_def)
  apply (rule_tac x=s in exI)
  apply clarsimp
  apply (rule rtranclp.rtrancl_into_rtrancl, assumption)
  apply (rule_tac x=hs in exI, rule_tac x=hs' in exI)
  apply clarsimp
  done

lemma framed_rel_step_swstable:
  \<open>framed_subresource_rel f hs hs' h h' \<Longrightarrow>
    r hs hs' \<Longrightarrow>
    (\<lfloor> p \<rfloor>\<^bsub>frame r with f\<^esub>) h \<Longrightarrow>
    (\<lfloor> p \<rfloor>\<^bsub>frame r with f\<^esub>) h'\<close>
  apply (clarsimp simp add: frame_with_def swstable_def)
  apply (subgoal_tac \<open>(\<lambda>h h'. \<exists>hs hs'. r hs hs' \<and> framed_subresource_rel f hs hs' h h')\<^sup>*\<^sup>* h s'\<close>)
   apply force
  apply (rule converse_rtranclp_into_rtranclp; blast)
  done


subsection \<open> Weak relation framing \<close>

definition wframe_with :: \<open>('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool)\<close>
  (\<open>(wframe _ with _)\<close> [0,50] 50)
  where
  \<open>wframe_with r p \<equiv> \<lambda>h h'. \<exists>hs hs'. r hs hs' \<and> weak_framed_subresource_rel p hs hs' h h'\<close>

lemma wframe_with_fullI:
  \<open>r h h' \<Longrightarrow> (wframe r with p) h h'\<close>
  by (force simp add: wframe_with_def)

lemma wframe_with_frame_rightI:
  \<open>p h2 \<Longrightarrow> r h1 h1' \<Longrightarrow> h' = h1' + h2 \<Longrightarrow> h1 ## h2 \<Longrightarrow> h1' ## h2 \<Longrightarrow>
    (wframe r with p) (h1 + h2) h'\<close>
  apply (simp add: wframe_with_def framed_subresource_rel_def)
  apply blast
  done

lemma weak_framed_rel_mono:
  \<open>r1 \<le> r2 \<Longrightarrow> (wframe r1 with f) \<le> (wframe r2 with f)\<close>
  by (force simp add: wframe_with_def)

lemma weak_framed_frame_right:
  \<open>x ## z \<Longrightarrow> y ## z \<Longrightarrow> (wframe r with \<top>) x y \<Longrightarrow> (wframe r with \<top>) (x + z) (y + z)\<close>
  apply (clarsimp simp add: wframe_with_def)
  apply (meson framed_subresource_relI framed_subresource_rel_frame_second top1I)
  done

lemma weak_framed_frame_left:
  \<open>z ## x \<Longrightarrow> z ## y \<Longrightarrow> (wframe r with \<top>) x y \<Longrightarrow> (wframe r with \<top>) (z + x) (z + y)\<close>
  by (metis disjoint_sym partial_add_commute weak_framed_frame_right)


lemma wframe_with_frame_leftI:
  \<open>p h1 \<Longrightarrow> r h2 h2' \<Longrightarrow> h' = h1 + h2' \<Longrightarrow> h1 ## h2 \<Longrightarrow> h1 ## h2' \<Longrightarrow>
    (wframe r with p) (h1 + h2) h'\<close>
  apply (simp add: wframe_with_def framed_subresource_rel_def)
  apply (meson disjoint_sym_iff partial_add_commute)
  done

lemma weak_framed_rel_step_wsstable:
  \<open>weak_framed_subresource_rel f hs hs' h h' \<Longrightarrow>
    r hs hs' \<Longrightarrow>
    (\<lceil> p \<rceil>\<^bsub>wframe r with f\<^esub>) h \<Longrightarrow>
    (\<lceil> p \<rceil>\<^bsub>wframe r with f\<^esub>) h'\<close>
  apply (clarsimp simp add: wframe_with_def wsstable_def)
  apply (rule_tac x=s in exI)
  apply clarsimp
  apply (rule rtranclp.rtrancl_into_rtrancl, assumption)
  apply (rule_tac x=hs in exI, rule_tac x=hs' in exI)
  apply clarsimp
  done

lemma weak_framed_rel_step_swstable:
  \<open>weak_framed_subresource_rel f hs hs' h h' \<Longrightarrow>
    r hs hs' \<Longrightarrow>
    (\<lfloor> p \<rfloor>\<^bsub>wframe r with f\<^esub>) h \<Longrightarrow>
    (\<lfloor> p \<rfloor>\<^bsub>wframe r with f\<^esub>) h'\<close>
  apply (clarsimp simp add: wframe_with_def swstable_def)
  apply (subgoal_tac \<open>(\<lambda>h h'. \<exists>hs hs'. r hs hs' \<and> weak_framed_subresource_rel f hs hs' h h')\<^sup>*\<^sup>* h s'\<close>)
   apply force
  apply (rule converse_rtranclp_into_rtranclp; force)
  done


definition
  \<open>framing_coherent f r \<equiv>
    \<forall>hx1 hf1.
      f hf1 \<longrightarrow>
      Ex (r hx1) \<longrightarrow>
      hx1 ## hf1 \<longrightarrow> \<comment> \<open> for all compatible start state-1 and frame-1 \<close>
      (\<forall>hx2 hy2 hf2.
        f hf2 \<longrightarrow>
        r hx2 hy2 \<longrightarrow>
        hx2 ## hf2 \<longrightarrow> \<comment> \<open> for all compatible start state-2 and frame-2 \<close>
        hx1 + hf1 = hx2 + hf2 \<longrightarrow> \<comment> \<open> if they add to the same thing \<close>
        (\<exists>hy1. r hx1 hy1 \<and> hy1 ## hf1 \<and> hy2 + hf2 = hy1 + hf1))
           \<comment> \<open> then there exists an hy1 that adds with frame-1 to hy2 + hf2 \<close>
  \<close>

lemma frame_coherent_rel_with_frame_right_iff:
  \<open>framing_coherent f r \<Longrightarrow>
    f hf1 \<Longrightarrow>
    r hx1 y \<Longrightarrow>
    hx1 ## hf1 \<Longrightarrow>
    (frame r with f) (hx1 + hf1) h' \<longleftrightarrow> (\<exists>hy1'. r hx1 hy1' \<and> hy1' ## hf1 \<and> h' = hy1' + hf1)\<close>
  by (simp add: framing_coherent_def frame_with_def framed_subresource_rel_def, blast)

lemma frame_coherent_rel_with_frame_left_iff:
  \<open>framing_coherent f r \<Longrightarrow>
    f hf1 \<Longrightarrow>
    r hx1 y \<Longrightarrow>
    hx1 ## hf1 \<Longrightarrow>
    (frame r with f) (hf1 + hx1) h' \<longleftrightarrow> (\<exists>hy1'. r hx1 hy1' \<and> hy1' ## hf1 \<and> h' = hf1 + hy1')\<close>
  apply (simp add: framing_coherent_def frame_with_def framed_subresource_rel_def)
  apply (metis partial_add_commute) (* slow *)
  done

end


section \<open> frame consistency predicates \<close>

subsection \<open> Frame maintains \<close>

definition
  \<open>frame_pred_maintains f r \<equiv>
    \<forall>x y z. r x y \<longrightarrow> f z \<longrightarrow> x ## z \<longrightarrow> (y ## z \<and> r (x+z) (y+z))\<close>

lemma frame_pred_maintainsD:
  \<open>frame_pred_maintains f b \<Longrightarrow>
    b h1 h2 \<Longrightarrow>
    f hf \<Longrightarrow>
    h1 ## hf \<Longrightarrow>
    h2 ## hf \<and> b (h1 + hf) (h2 + hf)\<close>
  by (simp add: frame_pred_maintains_def)

lemma frame_pred_maintains:
  \<open>frame_pred_maintains f b \<Longrightarrow>
    b h1 h2 \<Longrightarrow>
    f hf \<Longrightarrow>
    h1 ## hf \<Longrightarrow>
    b (h1 + hf) (h2 + hf)\<close>
  by (simp add: frame_pred_maintains_def)

lemma frame_pred_maintains2:
  \<open>frame_pred_maintains f b \<Longrightarrow> b h1 h2 \<Longrightarrow> f hf \<Longrightarrow> h1 ## hf \<Longrightarrow> h2 ## hf\<close>
  by (simp add: frame_pred_maintains_def)

lemma frame_pred_maintains_antimono':
  \<open>q \<le> p \<Longrightarrow> frame_pred_maintains p \<le> frame_pred_maintains q\<close>
  by (fastforce simp add: frame_pred_maintains_def)

lemma frame_pred_maintains_antimono:
  \<open>q \<le> p \<Longrightarrow> frame_pred_maintains p r \<Longrightarrow> frame_pred_maintains q r\<close>
  using frame_pred_maintains_antimono' by auto

lemmas frame_pred_maintains_antimonoD = frame_pred_maintains_antimono[rotated]

lemma frame_pred_maintains_relconjI:
  \<open>frame_pred_maintains p r1 \<Longrightarrow> frame_pred_maintains p r2 \<Longrightarrow> frame_pred_maintains p (r1 \<sqinter> r2)\<close>
  by (force simp add: frame_pred_maintains_def)

lemma frame_pred_maintains_reldisjI:
  \<open>frame_pred_maintains p r1 \<Longrightarrow> frame_pred_maintains p r2 \<Longrightarrow> frame_pred_maintains p (r1 \<squnion> r2)\<close>
  by (simp add: frame_pred_maintains_def)

subsection \<open> Frame extends \<close>

text \<open> more powerful maintains \<close>

definition \<open>frame_pred_extends f b \<equiv>
  \<forall>h1 h2 hf1.
    b h1 h2 \<longrightarrow> h1 ## hf1 \<longrightarrow> f hf1 \<longrightarrow>
      (\<exists>hf2. h2 ## hf2 \<and> f hf2 \<and> b (h1 + hf1) (h2 + hf2))\<close>

lemma frame_pred_extendsD:
  \<open>frame_pred_extends f b \<Longrightarrow>
    b h1 h2 \<Longrightarrow>
    f hf1 \<Longrightarrow>
    h1 ## hf1 \<Longrightarrow>
    \<exists>hf2. h2 ## hf2 \<and> f hf2 \<and> b (h1 + hf1) (h2 + hf2)\<close>
  by (simp add: frame_pred_extends_def)

lemma frame_pred_maintains_implies_extends:
  \<open>frame_pred_maintains f \<le> frame_pred_extends f\<close>
  unfolding frame_pred_maintains_def frame_pred_extends_def
  by auto

lemma frame_equals_maintain_eq_extends:
  \<open>frame_pred_maintains ((=) h) = frame_pred_extends ((=) h)\<close>
  unfolding frame_pred_maintains_def frame_pred_extends_def
  by presburger


subsection \<open> Frame closed \<close>

definition
  \<open>frame_pred_closed p r \<equiv>
    \<forall>h h'. r h h' \<longrightarrow> (\<forall>hf. p hf \<longrightarrow> h ## hf \<longrightarrow> h' ## hf \<longrightarrow> r (h + hf) (h' + hf))\<close>

abbreviation \<open>frame_closed \<equiv> frame_pred_closed (\<lambda>_. True)\<close>

lemma frame_pred_closedD:
  \<open>frame_pred_closed f b \<Longrightarrow>
    b h1 h2 \<Longrightarrow>
    f hf \<Longrightarrow>
    h1 ## hf \<Longrightarrow>
    h2 ## hf \<Longrightarrow>
    b (h1 + hf) (h2 + hf)\<close>
  by (simp add: frame_pred_closed_def)

lemma frame_pred_closed_antimono':
  \<open>q \<le> p \<Longrightarrow> frame_pred_closed p \<le> frame_pred_closed q\<close>
  by (force simp add: frame_pred_closed_def)

lemma frame_pred_closed_antimono:
  \<open>q \<le> p \<Longrightarrow> frame_pred_closed p r \<Longrightarrow> frame_pred_closed q r\<close>
  using frame_pred_closed_antimono' by auto

lemmas frame_pred_closed_antimonoD = frame_pred_closed_antimono[rotated]

lemma frame_pred_closed_disjI:
  \<open>frame_pred_closed p r1 \<Longrightarrow> frame_pred_closed p r2 \<Longrightarrow>
    frame_pred_closed p (r1 \<squnion> r2)\<close>
  by (simp add: frame_pred_closed_def all_conj_distrib)

lemma frame_pred_maintains_implies_closed:
  \<open>frame_pred_maintains p \<le> frame_pred_closed p\<close>
  unfolding frame_pred_maintains_def frame_pred_closed_def le_fun_def
  by force


subsection \<open> Frame pred safe \<close>

text \<open> more powerful frame_closed \<close>

definition
  \<open>frame_pred_safe f \<equiv>
    \<lambda>r. \<forall>x x' z z'. r x x' \<longrightarrow> f z \<longrightarrow> x ## z \<longrightarrow> f z' \<longrightarrow> x' ## z' \<longrightarrow> r (x+z) (x'+z')\<close>

lemma frame_pred_extends_eq_heap_implies_safe:
  \<open>frame_pred_extends ((=) hf) \<le> frame_pred_safe ((=) hf)\<close>
  unfolding frame_pred_extends_def frame_pred_safe_def le_fun_def
  by force

lemma frame_pred_safe_implies_closed:
  \<open>frame_pred_safe p f \<le> frame_pred_closed p f\<close>
  unfolding frame_pred_safe_def frame_pred_closed_def
  by auto

lemma frame_equals_safe_eq_closed:
  \<open>frame_pred_safe ((=) h) = frame_pred_closed ((=) h)\<close>
  unfolding frame_pred_safe_def frame_pred_closed_def
  by presburger


subsection \<open> Frame Step \<close>

definition
  \<open>frame_step_subframe f r \<equiv>
    \<forall>hf. f hf \<longrightarrow> (\<forall>x yf. x ## hf \<longrightarrow> r (x + hf) yf \<longrightarrow> (\<exists>y. r x y))\<close>


section \<open> Language Definition \<close>

subsection \<open> Commands \<close>

datatype 'h comm =
  Skip
  | Seq \<open>'h comm\<close> \<open>'h comm\<close> (infixr \<open>;;\<close> 75)
  | Par \<open>'h comm\<close> \<open>'h comm\<close> (infixr \<open>\<parallel>\<close> 65)
  | Ndet \<open>'h comm\<close> \<open>'h comm\<close> (infixr \<open>\<^bold>+\<close> 65)
  | Iter \<open>'h comm\<close> (\<open>_\<^sup>\<star>\<close> [80] 80)
  | Atomic \<open>'h \<Rightarrow> 'h \<Rightarrow> bool\<close>


paragraph \<open> Commands have a subexpression order \<close>
instantiation comm :: (type) order
begin

primrec less_eq_comm :: \<open>'a comm \<Rightarrow> 'a comm \<Rightarrow> bool\<close> where
  \<open>less_eq_comm c Skip = (c = Skip)\<close>
| \<open>less_eq_comm c (c1' ;; c2') = (c = c1' ;; c2' \<or> less_eq_comm c c1' \<or> less_eq_comm c c2')\<close>
| \<open>less_eq_comm c (c1' \<parallel> c2') = (c = c1' \<parallel> c2' \<or> less_eq_comm c c1' \<or> less_eq_comm c c2')\<close>
| \<open>less_eq_comm c (c1' \<^bold>+ c2') = (c = c1' \<^bold>+ c2' \<or> less_eq_comm c c1' \<or> less_eq_comm c c2')\<close>
| \<open>less_eq_comm c (c'\<^sup>\<star>) = (c = c'\<^sup>\<star> \<or> less_eq_comm c c')\<close>
| \<open>less_eq_comm c (Atomic b) = (c = Atomic b)\<close>

definition less_comm :: \<open>'a comm \<Rightarrow> 'a comm \<Rightarrow> bool\<close> where
  \<open>less_comm x y \<equiv> x \<noteq> y \<and> x \<le> y\<close>

lemma less_comm_simps[simp]:
  \<open>c < Skip \<longleftrightarrow> False\<close>
  \<open>c < c1' ;; c2' \<longleftrightarrow> c \<noteq> c1' ;; c2' \<and> (c \<le> c1' \<or> c \<le> c2')\<close>
  \<open>c < c1' \<parallel> c2' \<longleftrightarrow> c \<noteq> c1' \<parallel> c2' \<and> (c \<le> c1' \<or> c \<le> c2')\<close>
  \<open>c < c1' \<^bold>+ c2' \<longleftrightarrow> c \<noteq> c1' \<^bold>+ c2' \<and> (c \<le> c1' \<or> c \<le> c2')\<close>
  \<open>c < c'\<^sup>\<star> \<longleftrightarrow> c \<noteq> c'\<^sup>\<star> \<and> c \<le> c'\<close>
  \<open>c < Atomic b \<longleftrightarrow> False\<close>
  by (force simp add: less_comm_def)+

lemma less_eq_comm_refl: \<open>(x::'a comm) \<le> x\<close>
  by (induct x) force+

lemma less_eq_comm_trans: \<open>(x::'a comm) \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z\<close>
  by (induct z arbitrary: x y) force+

lemma less_eq_comm_subexprsD:
  \<open>(c1 ;; c2) \<le> c \<Longrightarrow> c1 \<le> c\<close>
  \<open>(c1 ;; c2) \<le> c \<Longrightarrow> c2 \<le> c\<close>
  \<open>(c1 \<^bold>+ c2) \<le> c \<Longrightarrow> c1 \<le> c\<close>
  \<open>(c1 \<^bold>+ c2) \<le> c \<Longrightarrow> c2 \<le> c\<close>
  \<open>(c1 \<parallel> c2) \<le> c \<Longrightarrow> c1 \<le> c\<close>
  \<open>(c1 \<parallel> c2) \<le> c \<Longrightarrow> c2 \<le> c\<close>
  \<open>(cb\<^sup>\<star>) \<le> c \<Longrightarrow> cb \<le> c\<close>
  by (meson less_eq_comm.simps less_eq_comm_refl less_eq_comm_trans; fail)+

lemma less_eq_comm_antisym: \<open>(x::'a comm) \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y\<close>
  by (induct y arbitrary: x)
    (metis less_eq_comm.simps less_eq_comm_subexprsD)+

instance
  by standard
    (force intro: less_eq_comm_refl less_eq_comm_trans less_eq_comm_antisym
      simp add: less_comm_def)+

end

lemma less_eq_comm_no_constructorsD:
  \<open>(c1 ;; c2) \<le> c \<Longrightarrow> c \<le> c1 \<Longrightarrow> False\<close>
  \<open>(c1 ;; c2) \<le> c \<Longrightarrow> c \<le> c2 \<Longrightarrow> False\<close>
  \<open>(c1 \<^bold>+ c2) \<le> c \<Longrightarrow> c \<le> c1 \<Longrightarrow> False\<close>
  \<open>(c1 \<^bold>+ c2) \<le> c \<Longrightarrow> c \<le> c2 \<Longrightarrow> False\<close>
  \<open>(c1 \<parallel> c2) \<le> c \<Longrightarrow> c \<le> c1 \<Longrightarrow> False\<close>
  \<open>(c1 \<parallel> c2) \<le> c \<Longrightarrow> c \<le> c2 \<Longrightarrow> False\<close>
  \<open>(cb\<^sup>\<star>) \<le> c \<Longrightarrow> c \<le> cb \<Longrightarrow> False\<close>
  by (fastforce dest: order.antisym)+


paragraph \<open> Predicate to ensure atomic actions have a given property \<close>

inductive all_atom_comm :: \<open>(('h \<Rightarrow> 'h \<Rightarrow> bool) \<Rightarrow> bool) \<Rightarrow> 'h comm \<Rightarrow> bool\<close> where
  skip[iff]: \<open>all_atom_comm p Skip\<close>
| seq[intro!]: \<open>all_atom_comm p c1 \<Longrightarrow> all_atom_comm p c2 \<Longrightarrow> all_atom_comm p (c1 ;; c2)\<close>
| par[intro!]: \<open>all_atom_comm p c1 \<Longrightarrow> all_atom_comm p c2 \<Longrightarrow> all_atom_comm p (c1 \<parallel> c2)\<close>
| ndet[intro!]: \<open>all_atom_comm p c1 \<Longrightarrow> all_atom_comm p c2 \<Longrightarrow> all_atom_comm p (c1 \<^bold>+ c2)\<close>
| iter[intro!]: \<open>all_atom_comm p c \<Longrightarrow> all_atom_comm p (c\<^sup>\<star>)\<close>
| atom[intro!]: \<open>p b \<Longrightarrow> all_atom_comm p (Atomic b)\<close>

inductive_cases all_atom_comm_doneE[elim!]: \<open>all_atom_comm p Skip\<close>
inductive_cases all_atom_comm_seqE[elim!]: \<open>all_atom_comm p (c1 ;; c2)\<close>
inductive_cases all_atom_comm_ndetE[elim!]: \<open>all_atom_comm p (c1 \<^bold>+ c2)\<close>
inductive_cases all_atom_comm_parE[elim!]: \<open>all_atom_comm p (c1 \<parallel> c2)\<close>
inductive_cases all_atom_comm_iterE[elim!]: \<open>all_atom_comm p (c\<^sup>\<star>)\<close>
inductive_cases all_atom_comm_atomE[elim!]: \<open>all_atom_comm p (Atomic b)\<close>

lemma all_atom_comm_simps[simp]:
  \<open>all_atom_comm p Skip \<longleftrightarrow> True\<close>
  \<open>all_atom_comm p (c1 ;; c2) \<longleftrightarrow> all_atom_comm p c1 \<and> all_atom_comm p c2\<close>
  \<open>all_atom_comm p (c1 \<^bold>+ c2) \<longleftrightarrow> all_atom_comm p c1 \<and> all_atom_comm p c2\<close>
  \<open>all_atom_comm p (c1 \<parallel> c2) \<longleftrightarrow> all_atom_comm p c1 \<and> all_atom_comm p c2\<close>
  \<open>all_atom_comm p (c\<^sup>\<star>) \<longleftrightarrow> all_atom_comm p c\<close>
  \<open>all_atom_comm p (Atomic b) \<longleftrightarrow> p b\<close>
  by fastforce+

lemma all_atom_comm_pred_mono:
  \<open>p \<le> q \<Longrightarrow> all_atom_comm p c \<Longrightarrow> all_atom_comm q c\<close>
  by (induct c) force+

lemma all_atom_comm_pred_mono':
  \<open>p \<le> q \<Longrightarrow> all_atom_comm p \<le> all_atom_comm q\<close>
  using all_atom_comm_pred_mono by auto

lemmas all_atom_comm_pred_monoD = all_atom_comm_pred_mono[rotated]

lemma all_atom_comm_conj_eq:
  \<open>all_atom_comm (p \<sqinter> q) c \<longleftrightarrow> all_atom_comm p c \<and> all_atom_comm q c\<close>
  by (induct c) force+

abbreviation \<open>atoms_subrel_guarantee g \<equiv> all_atom_comm (\<lambda>b. b \<le> g)\<close>
abbreviation \<open>atoms_preserve_guarantee g \<equiv> all_atom_comm (\<lambda>b. \<forall>s. Ex (g s) \<longrightarrow> Ex (b s))\<close>
abbreviation \<open>atoms_guarantee g c \<equiv> atoms_subrel_guarantee g c \<and> atoms_preserve_guarantee g c\<close>

abbreviation \<open>atoms_frame_closed \<equiv> all_atom_comm frame_closed\<close>



section \<open> Rely-Guarantee Separation Logic \<close>

inductive rgsat
  :: \<open>('h::perm_alg) comm \<Rightarrow> ('h \<Rightarrow> 'h \<Rightarrow> bool) \<Rightarrow> ('h \<Rightarrow> 'h \<Rightarrow> bool) \<Rightarrow> ('h \<Rightarrow> bool) \<Rightarrow> ('h \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where
  rgsat_skip:
  \<open>\<lceil> p \<rceil>\<^bsub>r\<^esub> \<le> q \<Longrightarrow> rgsat Skip r g p q\<close>
| rgsat_iter:
  \<open>rgsat c r g p' q' \<Longrightarrow>
      p \<le> i \<Longrightarrow> \<lceil> i \<rceil>\<^bsub>r\<^esub> \<le> p' \<Longrightarrow> q' \<le> i \<Longrightarrow> \<lceil> i \<rceil>\<^bsub>r\<^esub> \<le> q \<Longrightarrow>
      rgsat (c\<^sup>\<star>) r g p q\<close>
| rgsat_seq:
  \<open>rgsat c1 r g p1 p2 \<Longrightarrow>
    rgsat c2 r g p2 p3 \<Longrightarrow>
    rgsat (c1 ;; c2) r g p1 p3\<close>
| rgsat_ndet:
  \<open>rgsat c1 r g1 p q1 \<Longrightarrow>
    rgsat c2 r g2 p q2 \<Longrightarrow>
    frame_closed g1 \<Longrightarrow>
    frame_closed g2 \<Longrightarrow>
    g1 \<le> g \<Longrightarrow> g2 \<le> g \<Longrightarrow>
    q1 \<le> q \<Longrightarrow> q2 \<le> q \<Longrightarrow>
    rgsat (c1 \<^bold>+ c2) r g p q\<close>
| rgsat_parallel:
  \<open>rgsat s1 (r \<squnion> g2) g1 p1 q1 \<Longrightarrow>
    rgsat s2 (r \<squnion> g1) g2 p2 q2 \<Longrightarrow>
    g1 \<le> g \<Longrightarrow> g2 \<le> g \<Longrightarrow>
    p \<le> p1 \<^emph> p2 \<Longrightarrow>
    q1 \<^emph> q2 \<le> q \<Longrightarrow>
    rgsat (s1 \<parallel> s2) r g p q\<close>
| rgsat_atom:
  \<open>rel_liftL p \<sqinter> b \<le> rel_liftR q \<Longrightarrow>
    p \<le> pre_state b \<Longrightarrow>
    (\<forall>h h'. b h h' \<longrightarrow> (\<forall>hf. h ## hf \<longrightarrow> (\<exists>hx'. b (h + hf) hx'))) \<Longrightarrow>
    Something \<Longrightarrow>
    b \<le> g \<Longrightarrow>
    p' \<le> p \<^emph> f \<Longrightarrow>
    \<lceil> q \<^emph> f \<rceil>\<^bsub>r\<^esub> \<le> q' \<Longrightarrow>
    rgsat (Atomic b) r g p' q'\<close>
| rgsat_frame:
  \<open>rgsat c r g p q \<Longrightarrow>
    all_atom_comm (frame_pred_maintains f) c \<Longrightarrow>
    frame_pred_extends f r \<Longrightarrow>
    frame_step_subframe f r \<Longrightarrow>
    rgsat c r g (p \<^emph> f) (q \<^emph> f)\<close>
| rgsat_weaken:
  \<open>rgsat c r' g' p' q' \<Longrightarrow>
    p \<le> p' \<Longrightarrow> q' \<le> q \<Longrightarrow> r \<le> r' \<Longrightarrow> g' \<le> g \<Longrightarrow>
    rgsat c r g p q\<close>
inductive_cases rgsep_doneE[elim]: \<open>rgsat Skip r g p q\<close>
inductive_cases rgsep_iterE[elim]: \<open>rgsat (c\<^sup>\<star>) r g p q\<close>
inductive_cases rgsep_parE[elim]: \<open>rgsat (s1 \<parallel> s2) r g p q\<close>
inductive_cases rgsep_atomE[elim]: \<open>rgsat (Atomic c) r g p q\<close>

lemma rgsat_iter':
  \<open>rgsat c r g (\<lceil> i \<rceil>\<^bsub>r\<^esub>) i \<Longrightarrow> rgsat (c\<^sup>\<star>) r g i (\<lceil> i \<rceil>\<^bsub>r\<^esub>)\<close>
  using rgsat_iter[OF _ order.refl order.refl order.refl order.refl]
  by blast

lemma frame_conj_helper:
  fixes p1 :: \<open>'a::cancel_perm_alg \<Rightarrow> bool\<close>
  assumes precise_f: \<open>\<And>h h'. (\<lceil> f \<rceil>\<^bsub>r1\<^esub>) h \<Longrightarrow> (\<lceil> f \<rceil>\<^bsub>r2\<^esub>) h' \<Longrightarrow> h' = h\<close>
  shows \<open>p1 \<^emph> \<lceil> f \<rceil>\<^bsub>r1\<^esub> \<sqinter> p2 \<^emph> \<lceil> f \<rceil>\<^bsub>r2\<^esub> \<le> (p1 \<sqinter> p2) \<^emph> \<lceil> f \<rceil>\<^bsub>r1 \<squnion> r2\<^esub>\<close>
  apply (clarsimp simp add: sepconj_def)
  apply (rename_tac h1a h1b h2a h2b)
  apply (frule(1) precise_f)
  apply simp
  apply (metis precise_f predicate1D wsstable_def wsstable_stronger)
  done

lemma backwards_frame:
  \<open>rgsat c r g p q \<Longrightarrow> rel_add_preserve (r\<^sup>*\<^sup>*) \<Longrightarrow> rgsat c r g (p \<^emph> \<lfloor> f \<rfloor>\<^bsub>r \<squnion> g\<^esub>) (q \<^emph> f)\<close>
  oops

lemma backwards_done:
  \<open>rgsat Skip r g (\<lfloor> p \<rfloor>\<^bsub>r\<^esub>) p\<close>
  by (rule rgsat_weaken[OF rgsat_skip _ _ order.refl order.refl, where p'=\<open>\<lfloor> p \<rfloor>\<^bsub>r\<^esub>\<close> and q'=p])
    (clarsimp simp add: wsstable_def swstable_def le_fun_def)+

end