theory RGLogic
  imports SepAlgInstances
begin

section \<open> rely/guarantee helpers \<close>

abbreviation \<open>sswa r \<equiv> sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*)\<close>
abbreviation \<open>wssa r \<equiv> wlp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*)\<close>

lemma sp_rely_step:
  \<open>r y y' \<Longrightarrow>
    sp ((=) \<times>\<^sub>R rx) p (x, y) \<Longrightarrow>
    sp ((=) \<times>\<^sub>R (rx OO r)) p (x, y')\<close>
  by (force simp add: sp_def)

lemma sswa_step:
  \<open>r y y' \<Longrightarrow>
    sswa r p (x, y) \<Longrightarrow>
    sswa r p (x, y')\<close>
  by (simp add: sp_def, meson rtranclp.rtrancl_into_rtrancl)

lemmas sswa_stepD = sswa_step[rotated]

lemma wlp_rely_step_rtranclp:
  \<open>r y y' \<Longrightarrow>
    wssa r p (x, y) \<Longrightarrow>
    wssa r p (x, y')\<close>
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

definition
  \<open>weak_framed_subresource_rel p ha ha' h h' \<equiv>
    ha = h \<and> ha' = h' \<or> framed_subresource_rel p ha ha' h h'\<close>

lemma framed_subresource_relI:
  \<open>p hf \<Longrightarrow> ha ## hf \<Longrightarrow> ha' ## hf \<Longrightarrow> h = ha + hf \<Longrightarrow> h' = ha' + hf \<Longrightarrow>
    framed_subresource_rel p ha ha' h h'\<close>
  by (force simp add: framed_subresource_rel_def)

lemma framed_subresource_rel_refl[intro!]:
  \<open>weak_framed_subresource_rel p h h' h h'\<close>
  by (simp add: weak_framed_subresource_rel_def)

lemma framed_subresource_rel_impl_weak[intro]:
  \<open>framed_subresource_rel p hx hx' h h' \<Longrightarrow> weak_framed_subresource_rel p hx hx' h h'\<close>
  using weak_framed_subresource_rel_def by force

lemma framed_subresource_rel_frame_second:
  \<open>framed_subresource_rel \<top> ha ha' h h' \<Longrightarrow>
    h ## hf \<Longrightarrow>
    h' ## hf \<Longrightarrow>
    framed_subresource_rel \<top> ha ha' (h + hf) (h' + hf)\<close>
  using disjoint_add_swap_lr partial_add_assoc2
  by (simp add: framed_subresource_rel_def, meson)

lemma framed_subresource_rel_frame:
  \<open>framed_subresource_rel \<top> ha ha' h h' \<Longrightarrow>
    h ## hf \<Longrightarrow>
    h' ## hf \<Longrightarrow>
    framed_subresource_rel \<top> ha ha' (h + hf) (h' + hf)\<close>
  using disjoint_add_swap_lr partial_add_assoc2
  by (simp add: framed_subresource_rel_def, meson)

lemma framed_subresource_rel_sym:
  \<open>framed_subresource_rel p a b a' b' \<Longrightarrow> framed_subresource_rel p b a b' a'\<close>
  using framed_subresource_rel_def by auto

lemma framed_subresource_le_firstD[dest]:
  \<open>framed_subresource_rel f ha ha' h h' \<Longrightarrow> ha \<le> h\<close>
  using framed_subresource_rel_def by auto

lemma framed_subresource_le_secondD[dest]:
  \<open>framed_subresource_rel f ha ha' h h' \<Longrightarrow> ha' \<le> h'\<close>
  using framed_subresource_rel_def by auto

lemma wframed_subresource_le_firstD[dest]:
  \<open>weak_framed_subresource_rel f ha ha' h h' \<Longrightarrow> ha \<le> h\<close>
  using weak_framed_subresource_rel_def by auto

lemma wframed_subresource_le_secondD[dest]:
  \<open>weak_framed_subresource_rel f ha ha' h h' \<Longrightarrow> ha' \<le> h'\<close>
  using weak_framed_subresource_rel_def by auto

lemma framed_subresource_rel_top_same_sub_iff[simp]:
  \<open>framed_subresource_rel f a a b b' \<longleftrightarrow> b = b' \<and> (\<exists>xf. a ## xf \<and> b = a + xf \<and> f xf)\<close>
  by (force simp add: framed_subresource_rel_def le_iff_sepadd_weak)

definition \<open>framecl r \<equiv> (\<lambda>a b. (\<exists>x y. r x y \<and> framed_subresource_rel \<top> x y a b))\<close>

lemma framecl_frame_closed:
  \<open>(x ## hf) \<Longrightarrow> (y ## hf) \<Longrightarrow> b x y \<Longrightarrow> framecl b (x + hf) (y + hf)\<close>
  by (force simp add: framecl_def framed_subresource_rel_def)

end

context multiunit_sep_alg
begin

lemma mu_sep_alg_compatible_framed_subresource_rel_iff:
  assumes
    \<open>compatible h h'\<close>
    \<open>p (unitof h)\<close>
  shows
  \<open>weak_framed_subresource_rel p ha ha' h h' \<longleftrightarrow> framed_subresource_rel p ha ha' h h'\<close>
  using assms
  apply (simp add: weak_framed_subresource_rel_def framed_subresource_rel_def)
  apply (metis compatible_then_same_unit unitof_disjoint2 unitof_is_unitR2)
  done

end

lemma (in sep_alg) sep_alg_framed_subresource_rel_iff:
  \<open>p 0 \<Longrightarrow>
    weak_framed_subresource_rel p ha ha' h h' \<longleftrightarrow> framed_subresource_rel p ha ha' h h'\<close>
  apply (simp add: weak_framed_subresource_rel_def framed_subresource_rel_def)
  apply (metis sepadd_0_right zero_disjointR)
  done


section \<open> Language Definition \<close>

subsection \<open> Commands \<close>

datatype 'a comm =
  Skip
  | Seq \<open>'a comm\<close> \<open>'a comm\<close> (infixr \<open>;;\<close> 75)
  | Par \<open>'a comm\<close> \<open>'a comm\<close> (infixr \<open>\<parallel>\<close> 65)
  | Indet \<open>'a comm\<close> \<open>'a comm\<close> (infixr \<open>\<^bold>+\<close> 65)
  | Endet \<open>'a comm\<close> \<open>'a comm\<close> (infixr \<open>\<box>\<close> 65)
  | Atomic \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
  | Iter \<open>'a comm\<close> (\<open>DO (_) OD\<close> [0] 999)
\<comment> \<open> loops are represented by (least) fixed points. Fixed point variables are done in de Brijn
style. \<close>
  | Fix \<open>'a comm\<close> (\<open>\<mu>\<close>)
  | FixVar nat

subsection \<open> substitution \<close>

primrec map_fixvar :: \<open>(nat \<Rightarrow> nat) \<Rightarrow> 'a comm \<Rightarrow> 'a comm\<close> where
  \<open>map_fixvar f Skip = Skip\<close>
| \<open>map_fixvar f (c1 ;; c2) = map_fixvar f c1 ;; map_fixvar f c2\<close>
| \<open>map_fixvar f (c1 \<parallel> c2) = map_fixvar f c1 \<parallel> map_fixvar f c2\<close>
| \<open>map_fixvar f (c1 \<^bold>+ c2) = map_fixvar f c1 \<^bold>+ map_fixvar f c2\<close>
| \<open>map_fixvar f (c1 \<box> c2) = map_fixvar f c1 \<box> map_fixvar f c2\<close>
| \<open>map_fixvar f (DO c OD) = DO (map_fixvar f c) OD\<close>
| \<open>map_fixvar f (\<mu> c) = \<mu> (map_fixvar (case_nat 0 (Suc \<circ> f)) c)\<close>
| \<open>map_fixvar f (FixVar x) = FixVar (f x)\<close>
| \<open>map_fixvar f (Atomic b) = Atomic b\<close>


lemma map_fixvar_size[simp]:
  \<open>size (map_fixvar f c) = size c\<close>
  by (induct c arbitrary: f) force+

lemma map_fixvar_comp:
  \<open>map_fixvar f (map_fixvar g c) = map_fixvar (f \<circ> g) c\<close>
  by (induct c arbitrary: f g)
    (force intro: arg_cong2[where f=map_fixvar, OF _ refl] simp add: comp_def split: nat.splits)+

lemma map_fixvar_rev_iff:
  \<open>map_fixvar f c = c1' ;; c2' \<longleftrightarrow>
    (\<exists>c1 c2. c = c1 ;; c2 \<and> c1' = map_fixvar f c1 \<and> c2' = map_fixvar f c2)\<close>
  \<open>map_fixvar f c = c1' \<parallel> c2' \<longleftrightarrow>
      (\<exists>c1 c2. c = c1 \<parallel> c2 \<and> c1' = map_fixvar f c1 \<and> c2' = map_fixvar f c2)\<close>
  \<open>map_fixvar f c = c1' \<^bold>+ c2' \<longleftrightarrow>
      (\<exists>c1 c2. c = c1 \<^bold>+ c2 \<and> c1' = map_fixvar f c1 \<and> c2' = map_fixvar f c2)\<close>
  \<open>map_fixvar f c = c1' \<box> c2' \<longleftrightarrow>
      (\<exists>c1 c2. c = c1 \<box> c2 \<and> c1' = map_fixvar f c1 \<and> c2' = map_fixvar f c2)\<close>
  \<open>map_fixvar f c = DO c' OD \<longleftrightarrow>
      (\<exists>ca. c = DO ca OD \<and> c' = map_fixvar f ca)\<close>
  \<open>map_fixvar f c = \<mu> c' \<longleftrightarrow>
      (\<exists>ca. c = \<mu> ca \<and> c' = map_fixvar (case_nat 0 (Suc \<circ> f)) ca)\<close>
  \<open>map_fixvar f c = Skip \<longleftrightarrow> c = Skip\<close>
  \<open>map_fixvar f c = FixVar y \<longleftrightarrow> (\<exists>x. c = FixVar x \<and> f x = y)\<close>
  \<open>map_fixvar f c = Atomic b \<longleftrightarrow> c = Atomic b\<close>
         apply ((induct c; simp), metis)
         apply ((induct c; simp), metis)
        apply ((induct c; simp), metis)
       apply ((induct c; simp), metis)
      apply ((induct c; simp), metis)
     apply ((induct c; simp), blast)
    apply (induct c; simp; fail)+
  done

lemmas map_fixvar_sym_rev_iff = map_fixvar_rev_iff[THEN trans[OF eq_commute]]

lemma map_fixvar_inj_inject:
  \<open>inj f \<Longrightarrow> (map_fixvar f c1 = map_fixvar f c2) = (c1 = c2)\<close>
proof (induct c1 arbitrary: c2 f)
  case (Fix c1)
  moreover have \<open>inj (case_nat 0 (Suc \<circ> f))\<close>
    using Fix.prems
    apply (clarsimp simp add: inj_def)
    apply (case_tac x; case_tac y; simp)
    done
  ultimately show ?case
    by (force simp add: map_fixvar_sym_rev_iff)
next
  case (FixVar x)
  then show ?case
    by (metis injD map_fixvar_rev_iff(8))
qed (force simp add: map_fixvar_sym_rev_iff)+


primrec fixvar_subst :: \<open>'a comm \<Rightarrow> nat \<Rightarrow> 'a comm \<Rightarrow> 'a comm\<close> (\<open>_[_ \<leftarrow> _]\<close> [1000, 0, 0] 1000) where
  \<open>Skip[_ \<leftarrow> _] = Skip\<close>
| \<open>(c1 ;; c2)[x \<leftarrow> c'] = (c1[x \<leftarrow> c'] ;; c2[x \<leftarrow> c'])\<close>
| \<open>(c1 \<parallel> c2)[x \<leftarrow> c'] = (c1[x \<leftarrow> c'] \<parallel> c2[x \<leftarrow> c'])\<close>
| \<open>(c1 \<^bold>+ c2)[x \<leftarrow> c'] = (c1[x \<leftarrow> c'] \<^bold>+ c2[x \<leftarrow> c'])\<close>
| \<open>(c1 \<box> c2)[x \<leftarrow> c'] = (c1[x \<leftarrow> c'] \<box> c2[x \<leftarrow> c'])\<close>
| \<open>(DO c OD)[x \<leftarrow> c'] = (DO c[x \<leftarrow> c'] OD)\<close>
| \<open>(\<mu> c)[x \<leftarrow> c'] = \<mu> (c[Suc x \<leftarrow> c'])\<close>
| \<open>(FixVar y)[x \<leftarrow> c'] = (if x = y then c' else FixVar y)\<close>
| \<open>(Atomic b)[_ \<leftarrow> _] = Atomic b\<close>

lemma fixvar_subst_rev_iff:
  \<open>c[x \<leftarrow> cx] = Skip \<longleftrightarrow> c = Skip \<or> c = FixVar x \<and> cx = Skip\<close>
  \<open>c[x \<leftarrow> cx] = c1' ;; c2' \<longleftrightarrow>
    (\<exists>c1 c2. c = c1 ;; c2 \<and> c1' = c1[x \<leftarrow> cx] \<and> c2' = c2[x \<leftarrow> cx]) \<or>
    c = FixVar x \<and> cx = c1' ;; c2'\<close>
  \<open>c[x \<leftarrow> cx] = c1' \<parallel> c2' \<longleftrightarrow>
      (\<exists>c1 c2. c = c1 \<parallel> c2 \<and> c1' = c1[x \<leftarrow> cx] \<and> c2' = c2[x \<leftarrow> cx]) \<or>
      c = FixVar x \<and> cx = c1' \<parallel> c2'\<close>
  \<open>c[x \<leftarrow> cx] = c1' \<^bold>+ c2' \<longleftrightarrow>
      (\<exists>c1 c2. c = c1 \<^bold>+ c2 \<and> c1' = c1[x \<leftarrow> cx] \<and> c2' = c2[x \<leftarrow> cx]) \<or>
      c = FixVar x \<and> cx = c1' \<^bold>+ c2'\<close>
  \<open>c[x \<leftarrow> cx] = c1' \<box> c2' \<longleftrightarrow>
      (\<exists>c1 c2. c = c1 \<box> c2 \<and> c1' = c1[x \<leftarrow> cx] \<and> c2' = c2[x \<leftarrow> cx]) \<or>
      c = FixVar x \<and> cx = c1' \<box> c2'\<close>
  \<open>c[x \<leftarrow> cx] = DO c' OD \<longleftrightarrow>
      (\<exists>ca. c = DO ca OD \<and> c' = ca[x \<leftarrow> cx]) \<or>
      c = FixVar x \<and> cx = DO c' OD\<close>
  \<open>c[x \<leftarrow> cx] = \<mu> c' \<longleftrightarrow>
      (\<exists>ca. c = \<mu> ca \<and> c' = ca[Suc x \<leftarrow> cx]) \<or>
      c = FixVar x \<and> cx = \<mu> c'\<close>
  \<open>c[x \<leftarrow> cx] = FixVar y \<longleftrightarrow> c = FixVar x \<and> cx = FixVar y \<or> x \<noteq> y \<and> c = FixVar y\<close>
  \<open>c[x \<leftarrow> cx] = Atomic b \<longleftrightarrow> c = Atomic b \<or> c = FixVar x \<and> cx = Atomic b\<close>
          apply (induct c; simp; fail)
         apply ((induct c; simp), metis)+
  apply (induct c; simp; fail)
  done

lemma fixvar_subst_over_map_avoid:
  \<open>\<forall>y. f y \<noteq> x \<Longrightarrow> (map_fixvar f c)[x \<leftarrow> cx] = map_fixvar f c\<close>
  apply (induct c arbitrary: x f)
        apply (simp; fail)+
   apply (drule_tac x=\<open>Suc x\<close> in meta_spec, drule_tac x=\<open>case_nat 0 (Suc \<circ> f)\<close> in meta_spec,
      clarsimp split: nat.splits)
  apply force
  done

subsection \<open> subexpression order \<close>

(*
instantiation comm :: (type) order
begin

fun less_eq_comm :: \<open>'a comm \<Rightarrow> 'a comm \<Rightarrow> bool\<close> where
  \<open>(c \<le> Skip) = (c = Skip)\<close>
| \<open>(c \<le> c1' ;; c2') = (c = c1' ;; c2' \<or> c \<le> c1' \<or> c \<le> c2')\<close>
| \<open>(c \<le> c1' \<parallel> c2') = (c = c1' \<parallel> c2' \<or> c \<le> c1' \<or> c \<le> c2')\<close>
| \<open>(c \<le> c1' \<^bold>+ c2') = (c = c1' \<^bold>+ c2' \<or> c \<le> c1' \<or> c \<le> c2')\<close>
| \<open>(c \<le> \<mu> c') = (c = \<mu> c' \<or> map_fixvar Suc c \<le> c')\<close>
| \<open>(c \<le> FixVar x) = (c = FixVar x)\<close>
| \<open>(c \<le> Atomic b) = (c = Atomic b)\<close>

definition less_comm :: \<open>'a comm \<Rightarrow> 'a comm \<Rightarrow> bool\<close> where
  \<open>less_comm x y \<equiv> x \<noteq> y \<and> x \<le> y\<close>

lemma less_comm_simps[simp]:
  \<open>c < Skip \<longleftrightarrow> False\<close>
  \<open>c < c1' ;; c2' \<longleftrightarrow> c \<noteq> c1' ;; c2' \<and> (c \<le> c1' \<or> c \<le> c2')\<close>
  \<open>c < c1' \<parallel> c2' \<longleftrightarrow> c \<noteq> c1' \<parallel> c2' \<and> (c \<le> c1' \<or> c \<le> c2')\<close>
  \<open>c < c1' \<^bold>+ c2' \<longleftrightarrow> c \<noteq> c1' \<^bold>+ c2' \<and> (c \<le> c1' \<or> c \<le> c2')\<close>
  \<comment> \<open>c < \<mu> c' \<longleftrightarrow> c \<noteq> \<mu> c' \<or> map_fixvar Suc c \<le> c'\<close>
  \<open>c < FixVar x \<longleftrightarrow> False\<close>
  \<open>c < Atomic b \<longleftrightarrow> False\<close>
  by (force simp add: less_comm_def)+

lemma less_eq_comm_refl: \<open>(x::'a comm) \<le> x\<close>
  by (induct x) force+

lemma less_eq_comm_map_fixvar_inj_mono:
  \<open>(x::'a comm) \<le> y \<Longrightarrow> inj f \<Longrightarrow> map_fixvar f x \<le> map_fixvar f y\<close>
  apply (induct y arbitrary: x f)
        apply force+
   apply clarsimp
   apply (erule disjE, force)
   apply (simp add: map_fixvar_comp comp_def if_distrib[of Suc])
   apply (case_tac x)
  oops

lemma less_eq_comm_trans: \<open>(x::'a comm) \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z\<close>
  apply (induct z arbitrary: x y) 
        apply force+
   apply clarsimp
   apply (erule disjE, force)
  oops

lemma less_eq_comm_subexprsD:
  \<open>(c1 ;; c2) \<le> c \<Longrightarrow> c1 \<le> c\<close>
  \<open>(c1 ;; c2) \<le> c \<Longrightarrow> c2 \<le> c\<close>
  \<open>(c1 \<^bold>+ c2) \<le> c \<Longrightarrow> c1 \<le> c\<close>
  \<open>(c1 \<^bold>+ c2) \<le> c \<Longrightarrow> c2 \<le> c\<close>
  \<open>(c1 \<parallel> c2) \<le> c \<Longrightarrow> c1 \<le> c\<close>
  \<open>(c1 \<parallel> c2) \<le> c \<Longrightarrow> c2 \<le> c\<close>
  \<open>(\<mu> cb) \<le> c \<Longrightarrow> cb \<le> c\<close>
  (* by (meson less_eq_comm.simps less_eq_comm_refl less_eq_comm_trans; fail)+ *)
  oops

lemma less_eq_comm_antisym: \<open>(x::'a comm) \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y\<close>
  apply (induct y arbitrary: x)
        apply (simp; fail)+
(*
       apply (metis RGLogic.less_eq_comm_subexprsD(1,2) less_eq_comm.simps(2))
      apply (metis RGLogic.less_eq_comm_subexprsD(5,6) less_eq_comm.simps(3))
     apply (metis RGLogic.less_eq_comm_subexprsD(3,4) less_eq_comm.simps(4))
    apply (simp; fail)
   apply (metis RGLogic.less_eq_comm_subexprsD(7) less_eq_comm.simps(5))
  apply (simp; fail)
  done
*)
  oops

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
  \<open>(\<mu> cb) \<le> c \<Longrightarrow> c \<le> cb \<Longrightarrow> False\<close>
  by (fastforce dest: order.antisym)+

lemma subst_not_subexpr_iff:
  \<open>\<not> c[x \<leftarrow> cx] \<le> c \<longleftrightarrow> FixVar x \<le> c\<close>
  apply (induct c)
        apply force
       apply clarsimp
*)


subsection \<open> Map atoms \<close>

fun map_comm :: \<open>('b \<Rightarrow> 'a) \<Rightarrow> 'a comm \<Rightarrow> 'b comm\<close> where
  \<open>map_comm f Skip = Skip\<close>
| \<open>map_comm f (a ;; b) = map_comm f a ;; map_comm f b\<close>
| \<open>map_comm f (a \<parallel> b) = map_comm f a \<parallel> map_comm f b\<close>
| \<open>map_comm f (a \<^bold>+ b) = map_comm f a \<^bold>+ map_comm f b\<close>
| \<open>map_comm f (a \<box> b) = map_comm f a \<box> map_comm f b\<close>
| \<open>map_comm f (Atomic b) = Atomic (\<lambda>x y. b (f x) (f y))\<close>
| \<open>map_comm f (DO a OD) = DO map_comm f a OD\<close>
| \<open>map_comm f (\<mu> c) = \<mu> (map_comm f c)\<close>
| \<open>map_comm f (FixVar x) = FixVar x\<close>

lemma map_comm_rev_iff:
  \<open>map_comm f c = Skip \<longleftrightarrow> c = Skip\<close>
  \<open>map_comm f c = c1' ;; c2' \<longleftrightarrow>
    (\<exists>c1 c2. c = c1 ;; c2 \<and> c1' = map_comm f c1 \<and> c2' = map_comm f c2)\<close>
  \<open>map_comm f c = c1' \<parallel> c2' \<longleftrightarrow>
      (\<exists>c1 c2. c = c1 \<parallel> c2 \<and> c1' = map_comm f c1 \<and> c2' = map_comm f c2)\<close>
  \<open>map_comm f c = c1' \<^bold>+ c2' \<longleftrightarrow>
      (\<exists>c1 c2. c = c1 \<^bold>+ c2 \<and> c1' = map_comm f c1 \<and> c2' = map_comm f c2)\<close>
  \<open>map_comm f c = c1' \<box> c2' \<longleftrightarrow>
      (\<exists>c1 c2. c = c1 \<box> c2 \<and> c1' = map_comm f c1 \<and> c2' = map_comm f c2)\<close>
  \<open>map_comm f c = DO c' OD \<longleftrightarrow>
      (\<exists>ca. c = DO ca OD \<and> c' = map_comm f ca)\<close>
  \<open>map_comm f c = \<mu> c' \<longleftrightarrow>
      (\<exists>ca. c = \<mu> ca \<and> c' = map_comm f ca)\<close>
  \<open>map_comm f c = FixVar x \<longleftrightarrow> c = FixVar x\<close>
  \<open>map_comm f c = Atomic b \<longleftrightarrow> (\<exists>b'. c = Atomic b' \<and> b = (\<lambda>x y. b' (f x) (f y)))\<close>
  by (induct c; simp; argo)+

lemmas map_comm_rev_iff2 = map_comm_rev_iff[THEN trans[OF eq_commute]]

subsection \<open> All atom commands predicate \<close>

text \<open> Predicate to ensure atomic actions have a given property \<close>

inductive all_atom_comm :: \<open>(('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool) \<Rightarrow> 'a comm \<Rightarrow> bool\<close> where
  skip[iff]: \<open>all_atom_comm p Skip\<close>
| seq[intro!]: \<open>all_atom_comm p c1 \<Longrightarrow> all_atom_comm p c2 \<Longrightarrow> all_atom_comm p (c1 ;; c2)\<close>
| par[intro!]: \<open>all_atom_comm p c1 \<Longrightarrow> all_atom_comm p c2 \<Longrightarrow> all_atom_comm p (c1 \<parallel> c2)\<close>
| indet[intro!]: \<open>all_atom_comm p c1 \<Longrightarrow> all_atom_comm p c2 \<Longrightarrow> all_atom_comm p (c1 \<^bold>+ c2)\<close>
| endet[intro!]: \<open>all_atom_comm p c1 \<Longrightarrow> all_atom_comm p c2 \<Longrightarrow> all_atom_comm p (c1 \<box> c2)\<close>
| iter[intro!]: \<open>all_atom_comm p c \<Longrightarrow> all_atom_comm p (DO c OD)\<close>
| fixpt[intro!]: \<open>all_atom_comm p c \<Longrightarrow> all_atom_comm p (\<mu> c)\<close>
| fixvar[iff]: \<open>all_atom_comm p (FixVar x)\<close>
| atom[intro!]: \<open>p b \<Longrightarrow> all_atom_comm p (Atomic b)\<close>

inductive_cases all_atom_comm_seqE[elim!]: \<open>all_atom_comm p (c1 ;; c2)\<close>
inductive_cases all_atom_comm_indetE[elim!]: \<open>all_atom_comm p (c1 \<^bold>+ c2)\<close>
inductive_cases all_atom_comm_endetE[elim!]: \<open>all_atom_comm p (c1 \<box> c2)\<close>
inductive_cases all_atom_comm_parE[elim!]: \<open>all_atom_comm p (c1 \<parallel> c2)\<close>
inductive_cases all_atom_comm_iterE[elim!]: \<open>all_atom_comm p (DO c OD)\<close>
inductive_cases all_atom_comm_fixptE[elim!]: \<open>all_atom_comm p (\<mu> c)\<close>
inductive_cases all_atom_comm_fixvarE[elim!]: \<open>all_atom_comm p (FixVar x)\<close>
inductive_cases all_atom_comm_atomE[elim!]: \<open>all_atom_comm p (Atomic b)\<close>

lemma all_atom_comm_simps[simp]:
  \<open>all_atom_comm p (c1 ;; c2) \<longleftrightarrow> all_atom_comm p c1 \<and> all_atom_comm p c2\<close>
  \<open>all_atom_comm p (c1 \<^bold>+ c2) \<longleftrightarrow> all_atom_comm p c1 \<and> all_atom_comm p c2\<close>
  \<open>all_atom_comm p (c1 \<box> c2) \<longleftrightarrow> all_atom_comm p c1 \<and> all_atom_comm p c2\<close>
  \<open>all_atom_comm p (c1 \<parallel> c2) \<longleftrightarrow> all_atom_comm p c1 \<and> all_atom_comm p c2\<close>
  \<open>all_atom_comm p (DO c OD) \<longleftrightarrow> all_atom_comm p c\<close>
  \<open>all_atom_comm p (\<mu> c) \<longleftrightarrow> all_atom_comm p c\<close>
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

lemma all_atom_comm_pconj_eq[simp]:
  \<open>all_atom_comm (\<lambda>x. p x \<and> q x) c \<longleftrightarrow> all_atom_comm p c \<and> all_atom_comm q c\<close>
  by (induct c) force+

lemma all_atom_comm_top_eq[simp]:
  \<open>all_atom_comm \<top> c\<close>
  by (induct c) force+

lemma all_atom_comm_pTrue_eq[simp]:
  \<open>all_atom_comm (\<lambda>x. True) c\<close>
  by (induct c) force+

lemma all_atom_comm_subst[simp]:
  \<open>all_atom_comm p c' \<Longrightarrow> all_atom_comm p (c[x \<leftarrow> c']) \<longleftrightarrow> all_atom_comm p c\<close>
  by (induct c arbitrary: x) force+

lemma all_atom_comm_subst_strong:
  \<open>all_atom_comm p c' - all_atom_comm p c \<Longrightarrow> all_atom_comm p (c[x \<leftarrow> c']) \<longleftrightarrow> all_atom_comm p c\<close>
  by (induct c arbitrary: x) force+

abbreviation \<open>atoms_subrel_of r \<equiv> all_atom_comm (\<lambda>b. b \<le> r)\<close>


section \<open> Rely-Guarantee Separation Logic \<close>

inductive rgsat ::
  \<open>('l::perm_alg \<times> 's::perm_alg) comm \<Rightarrow>
    ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
    ('l \<times> 's \<Rightarrow> bool) \<Rightarrow> ('l \<times> 's \<Rightarrow> bool) \<Rightarrow>
    bool\<close>
  where
  rgsat_skip:
  \<open>sswa r p \<le> q \<Longrightarrow> rgsat Skip r g p q\<close>
| rgsat_iter:
  \<open>rgsat c r g (sswa r i) (sswa r i) \<Longrightarrow>
    p \<le> i \<Longrightarrow> sswa r i \<le> q \<Longrightarrow>
    rgsat (Iter c) r g p q\<close>
| rgsat_seq:
  \<open>rgsat c1 r g p1 p2 \<Longrightarrow>
    rgsat c2 r g p2 p3 \<Longrightarrow>
    rgsat (c1 ;; c2) r g p1 p3\<close>
| rgsat_indet:
  \<open>rgsat c1 r g1 p q1 \<Longrightarrow>
    rgsat c2 r g2 p q2 \<Longrightarrow>
    g1 \<le> g \<Longrightarrow> g2 \<le> g \<Longrightarrow>
    q1 \<le> q \<Longrightarrow> q2 \<le> q \<Longrightarrow>
    rgsat (c1 \<^bold>+ c2) r g p q\<close>
| rgsat_endet:
  \<open>rgsat c1 r g1 p q1 \<Longrightarrow>
    rgsat c2 r g2 p q2 \<Longrightarrow>
    g1 \<le> g \<Longrightarrow> g2 \<le> g \<Longrightarrow>
    q1 \<le> q \<Longrightarrow> q2 \<le> q \<Longrightarrow>
    rgsat (c1 \<box> c2) r g p q\<close>
| rgsat_parallel:
  \<open>rgsat s1 (r \<squnion> g2) g1 p1 q1 \<Longrightarrow>
    rgsat s2 (r \<squnion> g1) g2 p2 q2 \<Longrightarrow>
    g1 \<le> g \<Longrightarrow> g2 \<le> g \<Longrightarrow>
    sswa (r \<squnion> g2) q1 \<le> q1' \<Longrightarrow>
    sswa (r \<squnion> g1) q2 \<le> q2' \<Longrightarrow>
    rgsat (s1 \<parallel> s2) r g (p1 \<^emph>\<and> p2) (q1' \<^emph>\<and> q2')\<close>
| rgsat_atom:
  \<open>sp b (wlp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) p) \<le> sswa r q \<Longrightarrow>
    \<forall>f. sp b (wssa r (p \<^emph>\<and> f)) \<le> sswa r (q \<^emph>\<and> f) \<Longrightarrow>
    b \<le> \<top> \<times>\<^sub>R g \<Longrightarrow>
    p' \<le> wssa r p \<Longrightarrow>
    sswa r q \<le> q' \<Longrightarrow>
    rgsat (Atomic b) r g p' q'\<close>
| rgsat_frame:
  \<open>rgsat c r g p q \<Longrightarrow>
    sswa (r \<squnion> g) f \<le> f' \<Longrightarrow>
    rgsat c r g (p \<^emph>\<and> f) (q \<^emph>\<and> f')\<close>
| rgsat_weaken:
  \<open>rgsat c r' g' p' q' \<Longrightarrow>
    p \<le> p' \<Longrightarrow> q' \<le> q \<Longrightarrow> r \<le> r' \<Longrightarrow> g' \<le> g \<Longrightarrow>
    rgsat c r g p q\<close>
| rgsat_disj:
  \<open>rgsat c r g p1 q1 \<Longrightarrow>
    rgsat c r g p2 q2 \<Longrightarrow>
    rgsat c r g (p1 \<squnion> p2) (q1 \<squnion> q2)\<close>
| rgsat_conj:
  \<open>rgsat c r g p1 q1 \<Longrightarrow>
    rgsat c r g p2 q2 \<Longrightarrow>
    \<forall>a b c::'l. a ## c \<longrightarrow> b ## c \<longrightarrow> a + c = b + c \<longrightarrow> a = b \<Longrightarrow>
    rgsat c r g (p1 \<sqinter> p2) (q1 \<sqinter> q2)\<close>

inductive_cases rgsep_doneE[elim]: \<open>rgsat Skip r g p q\<close>
inductive_cases rgsep_iterE[elim]: \<open>rgsat (DO c OD) r g p q\<close>
\<comment> \<open> inductive_cases rgsep_fixptE[elim]: \<open>rgsat (\<mu> c) r g p q\<close> \<close>
inductive_cases rgsep_parE[elim]: \<open>rgsat (s1 \<parallel> s2) r g p q\<close>
inductive_cases rgsep_atomE[elim]: \<open>rgsat (Atomic c) r g p q\<close>

lemma backwards_done:
  \<open>rgsat Skip r g (wlp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) p) p\<close>
  by (rule rgsat_weaken[OF rgsat_skip _ _ order.refl order.refl,
        where p'=\<open>wlp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) p\<close> and q'=p])
    (clarsimp simp add: sp_def wlp_def le_fun_def)+

end