theory Experimental
  imports Soundness
begin


definition perm_alg_homomorphism :: \<open>('a :: perm_alg \<Rightarrow> 'b :: perm_alg) \<Rightarrow> bool\<close> where
  \<open>perm_alg_homomorphism f \<equiv>
    (\<forall>x y. x ## y \<longrightarrow> f x ## f y) \<and>
    (\<forall>x y. x ## y \<longrightarrow> f (x + y) = f x + f y)\<close>

definition sep_alg_homomorphism :: \<open>('a :: sep_alg \<Rightarrow> 'b :: sep_alg) \<Rightarrow> bool\<close> where
  \<open>sep_alg_homomorphism f \<equiv>
    (\<forall>x y. x ## y \<longrightarrow> f x ## f y) \<and>
    (\<forall>x y. x ## y \<longrightarrow> f (x + y) = f x + f y) \<and>
    (\<forall>x. f (unitof x) = unitof (f x)) \<and>
    (f 0 = 0)\<close>


lemma perm_alg_homomorphism_mono:
  \<open>perm_alg_homomorphism f \<Longrightarrow> x \<preceq> y \<Longrightarrow> f x \<preceq> f y\<close>
  by (clarsimp simp add: less_eq_sepadd_def' perm_alg_homomorphism_def, metis)

lemma perm_alg_homomorphism_tuple:
  \<open>perm_alg_homomorphism f \<Longrightarrow>
    perm_alg_homomorphism g \<Longrightarrow>
    perm_alg_homomorphism (map_prod f g)\<close>
  by (clarsimp simp add: perm_alg_homomorphism_def)

definition
  \<open>split_preserving_morphism (f :: ('a::perm_alg \<Rightarrow> 'b::perm_alg)) \<equiv>
    \<forall>x y' z'. y' ## z' \<longrightarrow> f x = y' + z' \<longrightarrow> (\<exists>y z. x = y + z \<and> y ## z \<and> y' = f y \<and> z' = f z)\<close>

lemma function_rel_subsetD:
  \<open>(\<lambda>x y. r (f x) (f y))\<^sup>*\<^sup>* x y \<Longrightarrow> (\<lambda>x y. r\<^sup>*\<^sup>* (f x) (f y)) x y\<close>
  by (induct rule: rtranclp_induct) force+

lemma function_rel_subset:
  \<open>(\<lambda>x y. r (f x) (f y))\<^sup>*\<^sup>* \<le> (\<lambda>x y. r\<^sup>*\<^sup>* (f x) (f y))\<close>
  by (simp add: function_rel_subsetD predicate2I)

lemma helper:
  \<open>sswa (\<lambda>a b. r (fs a) (fs b)) (i \<circ> map_prod fl fs) \<le> (\<lambda>a. sswa r i (map_prod fl fs a))\<close>
  apply (clarsimp simp add: sp_def fun_eq_iff)
  apply (rename_tac a y x)
  apply (rule_tac x=\<open>fs x\<close> in exI)
  apply (rule conjI)
   apply (simp add: function_rel_subsetD; fail)
  apply blast
  done

definition rel_precomp :: \<open>('a \<Rightarrow> 'a \<Rightarrow> 'z) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> 'z)\<close> (infixl \<open>\<circ>\<^sub>R\<close> 55) where
  \<open>r \<circ>\<^sub>R f \<equiv> \<lambda>x y. r (f x) (f y)\<close>

lemma rel_precomp_sup_eq:
  \<open>(r1 \<squnion> r2) \<circ>\<^sub>R f = (r1 \<circ>\<^sub>R f) \<squnion> (r2 \<circ>\<^sub>R f)\<close>
  by (fastforce simp add: rel_precomp_def)

lemma helper_rewrite:
  \<open>\<forall>x y. (\<lambda>x y. r (fs x) (fs y))\<^sup>*\<^sup>* = (\<lambda>x y. r\<^sup>*\<^sup>* (fs x) (fs y)) \<Longrightarrow>
    range fs = UNIV \<Longrightarrow>
    sswa r p \<circ> map_prod fl fs = sswa (r \<circ>\<^sub>R fs) (p \<circ> map_prod fl fs)\<close>
  apply (clarsimp simp add: sp_def comp_def rel_precomp_def fun_eq_iff)
  apply (rule iffI)
   apply (metis surjD)
  apply blast
  done

lemma rel_precomp_mono:
  \<open>r \<le> r' \<Longrightarrow> r \<circ>\<^sub>R fs \<le> r' \<circ>\<^sub>R fs\<close>
  by (simp add: le_fun_def rel_precomp_def)

lemma sepconj_conj_map_prod_impl1:
  \<open>perm_alg_homomorphism fl \<Longrightarrow>
    ((q1' \<circ> map_prod fl fs) \<^emph>\<and> (q2' \<circ> map_prod fl fs)) x \<Longrightarrow>
    (q1' \<^emph>\<and> q2') (map_prod fl fs x)\<close>
  apply (clarsimp simp add: sepconj_conj_def perm_alg_homomorphism_def)
  apply blast
  done

lemma
  \<open>perm_alg_homomorphism (f :: ('a::perm_alg \<Rightarrow> 'b::perm_alg)) \<Longrightarrow>
    \<forall>x. f x ## f x \<longrightarrow> x ## x \<Longrightarrow>
    \<forall>x. sepadd_unit (f x) \<longrightarrow> sepadd_unit x \<Longrightarrow>
    \<forall>x y. (x ## y \<longrightarrow> pa x y = Some (x + (y::'a))) \<and> (\<not>x ## y \<longrightarrow> pa x y = None) \<Longrightarrow>
    \<forall>x y. (x ## y \<longrightarrow> pb x y = Some (x + (y::'b))) \<and> (\<not>x ## y \<longrightarrow> pb x y = None) \<Longrightarrow>
    \<forall>x y' z'. y' ## z' \<longrightarrow> f x = y' + z' \<longrightarrow> (\<exists>y z. x = y + z \<and> y ## z \<and> y' = f y \<and> z' = f z)\<close>
  apply (clarsimp simp add: sep_alg_homomorphism_def)
  oops

lemma sepconj_conj_map_prod_eq:
  \<open>perm_alg_homomorphism fl \<Longrightarrow>
    split_preserving_morphism fl \<Longrightarrow>
    (q1' \<^emph>\<and> q2') (map_prod fl fs a) = ((q1' \<circ> map_prod fl fs) \<^emph>\<and> (q2' \<circ> map_prod fl fs)) a\<close>
  apply (cases a)
  apply (clarsimp simp add: sepconj_conj_def perm_alg_homomorphism_def
      split_preserving_morphism_def)
  apply (rule iffI, blast, metis)
  done


lemma semilattice_sup_helper1:
  fixes ra :: \<open>'a :: semilattice_sup\<close>
  shows
  \<open>rb1 \<le> rb \<Longrightarrow>
    rb2 \<le> rb \<Longrightarrow>
    ra \<le> rab' \<Longrightarrow>
    rb2 \<le> rab' \<Longrightarrow>
    rab' \<le> ra \<squnion> rb2 \<squnion> rb1 \<Longrightarrow>
    rab' \<le> ra \<squnion> rb\<close>
  by (metis sup.absorb_iff2 sup_assoc)

lemma rgsat_preserved_under_homomorphism:
  fixes p :: \<open>'a::perm_alg \<times> 'b::perm_alg \<Rightarrow> bool\<close>
    and q :: \<open>'a \<times> 'b \<Rightarrow> bool\<close>
    and fl :: \<open>'c::perm_alg \<Rightarrow> 'a\<close>
    and fs :: \<open>'d::perm_alg \<Rightarrow> 'b\<close>
  shows
  \<open>rgsat c r g p q \<Longrightarrow>
    perm_alg_homomorphism fl \<Longrightarrow>
    perm_alg_homomorphism fs \<Longrightarrow>
    split_preserving_morphism fl \<Longrightarrow>
    (\<And>p rx. r \<le> rx \<Longrightarrow> rx \<le> r \<squnion> g \<Longrightarrow>
        sswa rx p \<circ> map_prod fl fs = sswa (rx \<circ>\<^sub>R fs) (p \<circ> map_prod fl fs)) \<Longrightarrow>
    c' = map_comm (map_prod fl fs) c \<Longrightarrow>
    p' = (p \<circ> map_prod fl fs) \<Longrightarrow>
    q' = (q \<circ> map_prod fl fs) \<Longrightarrow>
    r' = r \<circ>\<^sub>R fs \<Longrightarrow>
    g' = g \<circ>\<^sub>R fs \<Longrightarrow>
    rgsat c' r' g' p' q'\<close>
proof (induct arbitrary: c' p' q' r' g' rule: rgsat.inducts)
  case (rgsat_skip r p q g)
  then show ?case
    apply (clarsimp simp add: map_comm_rev_iff2)
    apply (rule rgsat.rgsat_skip)
    apply (clarsimp simp add: le_fun_def sp_def imp_ex_conjL rel_precomp_def)
    apply (frule function_rel_subsetD)
    apply blast
    done
next
  case (rgsat_iter c r g i p q)
  show ?case
    using rgsat_iter.prems rgsat_iter.hyps(1,3-)
    apply (clarsimp simp add: map_comm_rev_iff2 simp del: sup_apply)
    apply (rule rgsat.rgsat_iter[where i=\<open>i \<circ> map_prod fl fs\<close>])
      apply (rule rgsat_iter.hyps(2); simp add: comp_def sp_comp_rel del: sup_apply; fail)
     apply fastforce
    apply (drule meta_spec[of _ r])
    apply (clarsimp simp add: le_fun_def comp_def)
    apply (metis map_prod_simp)
    done
next
  case (rgsat_seq c1 r g p1 p2 c2 p3)
  show ?case
    using rgsat_seq.prems
    apply (clarsimp simp add: map_comm_rev_iff2)
    apply (rule rgsat.rgsat_seq)
     apply (rule rgsat_seq.hyps(2); force simp add: comp_def sp_comp_rel)
    apply (rule rgsat_seq.hyps(4); simp add: comp_def sp_comp_rel; fail)
    done
next
  case (rgsat_indet c1 r g1 p q1 c2 g2 q2 g q)
  show ?case
    using rgsat_indet.prems rgsat_indet.hyps(5-)
    apply (clarsimp simp add: map_comm_rev_iff2 simp del: sup_apply)
    apply (rule rgsat.rgsat_indet)
         apply (rule rgsat_indet.hyps(2); simp add: comp_def sp_comp_rel del: sup_apply)
         apply (drule_tac x=rx in meta_spec)
         apply (simp del: sup_apply, blast)
        apply (rule rgsat_indet.hyps(4); simp add: comp_def sp_comp_rel)
        apply (drule_tac x=rx in meta_spec)
        apply (simp del: sup_apply, blast)
       apply (metis rel_precomp_mono)
      apply (metis rel_precomp_mono)
     apply (simp add: le_fun_def)
    apply (simp add: le_fun_def)
    done
next
  case (rgsat_endet c1 r g1 p q1 c2 g2 q2 g q)
  show ?case
    using rgsat_endet.prems rgsat_endet.hyps(5-)
    apply (clarsimp simp add: map_comm_rev_iff2)
    apply (rule rgsat.rgsat_endet)
         apply (rule rgsat_endet.hyps(2); simp add: comp_def sp_comp_rel)
         apply (drule_tac x=rx in meta_spec)
         apply (simp del: sup_apply, blast)
        apply (rule rgsat_endet.hyps(4); simp add: comp_def sp_comp_rel)
        apply (drule_tac x=rx in meta_spec)
        apply (simp del: sup_apply, blast)
       apply (metis rel_precomp_mono)
      apply (metis rel_precomp_mono)
     apply (simp add: le_fun_def)
    apply (simp add: le_fun_def)
    done
next
  case (rgsat_parallel s1 r g2 g1 p1 q1 s2 p2 q2 g q1' q2')
  show ?case
    using rgsat_parallel.prems rgsat_parallel.hyps(5-)
    apply (clarsimp simp add: map_comm_rev_iff2 sepconj_conj_map_prod_eq simp del: sup_apply)
    apply (rule rgsat.rgsat_parallel[of
          _ \<open>r \<circ>\<^sub>R fs\<close> \<open>g2 \<circ>\<^sub>R fs\<close> \<open>g1 \<circ>\<^sub>R fs\<close> \<open>p1 \<circ> map_prod fl fs\<close> \<open>q1 \<circ> map_prod fl fs\<close>
          _ \<open>p2 \<circ> map_prod fl fs\<close> \<open>q2 \<circ> map_prod fl fs\<close>])
         apply (rule rgsat_parallel.hyps(2); (simp del: sup_apply)?) (* 6 \<rightarrow> 7 *)
          apply (metis semilattice_sup_helper1)
         apply (metis rel_precomp_sup_eq)
        apply (rule rgsat_parallel.hyps(4); (simp del: sup_apply)?) (* 6 \<rightarrow> 7 *)
         apply (metis semilattice_sup_helper1)
        apply (metis rel_precomp_sup_eq)
       apply (simp add: rel_precomp_mono; fail)
      apply (simp add: rel_precomp_mono; fail)
     apply (drule_tac x=\<open>r \<squnion> g2\<close> and y=q1 in meta_spec2)
     apply (clarsimp simp add: rel_precomp_sup_eq[symmetric] le_supI2 comp_def simp del: sup_apply)
     apply (clarsimp simp add: le_fun_def)
     apply (metis map_prod_simp)
    apply (drule_tac x=\<open>r \<squnion> g1\<close> and y=q2 in meta_spec2)
    apply (clarsimp simp add: rel_precomp_sup_eq[symmetric] le_supI2 comp_def simp del: sup_apply)
    apply (clarsimp simp add: le_fun_def)
    apply (metis map_prod_simp)
    done
next
  case (rgsat_atom b r p q g p' q')
  then show ?case
    apply (clarsimp simp add: map_comm_rev_iff2 sepconj_conj_map_prod_eq)
    apply (rule rgsat.rgsat_atom)
        apply blast
    sorry
next
  case (rgsat_frame c r g p q f f')
  then show ?case sorry
next
  case (rgsat_weaken c rx gx px qx p q r g)
  show ?case
    using rgsat_weaken.prems rgsat_weaken.hyps(3-)
    apply -
    apply (rule rgsat.rgsat_weaken[of _
          \<open>rx \<circ>\<^sub>R fs\<close> \<open>gx \<circ>\<^sub>R fs\<close> \<open>px \<circ> map_prod fl fs\<close> \<open>qx \<circ> map_prod fl fs\<close>])
        apply (rule rgsat_weaken.hyps(2); simp)
    oops


lemma rgsat_preserved_under_homomorphism2:
  fixes p :: \<open>'a::perm_alg \<times> 'b::perm_alg \<Rightarrow> bool\<close>
    and q :: \<open>'a \<times> 'b \<Rightarrow> bool\<close>
    and fl :: \<open>'c::perm_alg \<Rightarrow> 'a\<close>
    and fs :: \<open>'d::perm_alg \<Rightarrow> 'b\<close>
  shows
  \<open>rgsat c' r' g' p' q' \<Longrightarrow>
    perm_alg_homomorphism fl \<Longrightarrow>
    perm_alg_homomorphism fs \<Longrightarrow>
    (\<And>p. sswa r p \<circ> map_prod fl fs = sswa (r \<circ>\<^sub>R fs) (p \<circ> map_prod fl fs)) \<Longrightarrow>
    surj fl \<Longrightarrow>
    surj fs \<Longrightarrow>
    c' = map_comm (map_prod fl fs) c \<Longrightarrow>
    p' = (p \<circ> map_prod fl fs) \<Longrightarrow>
    q' = (q \<circ> map_prod fl fs) \<Longrightarrow>
    r' = r \<circ>\<^sub>R fs \<Longrightarrow>
    g' = g \<circ>\<^sub>R fs \<Longrightarrow>
    rgsat c r g p q\<close>
  oops


class appel_perm_alg = ord +
  fixes J :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
  assumes join_eq: \<open>J a b z1 \<Longrightarrow> J a b z2 \<Longrightarrow> z1 = z2\<close>
  assumes join_assoc: \<open>J a b d \<Longrightarrow> J d c e \<Longrightarrow> \<exists>f. J b c f \<and> J a f e\<close>
  assumes join_comm: \<open>J a b c \<Longrightarrow> J b a c\<close>
  assumes join_positivity: \<open>J a c1 b \<Longrightarrow> J b c2 a \<Longrightarrow> a = b\<close>
begin

lemma ex_pseudo_unit:
  \<open>\<forall>a. \<exists>u. J a u a\<close>
  nitpick
  oops

lemma related_pseudo_units_identical_failure:
  \<open>J u1 a a \<Longrightarrow> J u2 a a \<Longrightarrow> u1 = u2\<close>
  nitpick
  oops

lemma related_units_identical_failure:
  \<open>(\<forall>a z. J u1 a z \<longrightarrow> z = a) \<Longrightarrow> (\<forall>a z. J u2 a z \<longrightarrow> z = a) \<Longrightarrow>
    J u1 a a \<Longrightarrow> J u2 a a \<Longrightarrow> u1 = u2\<close>
  by (metis join_assoc join_comm)

definition
  \<open>disjoint2 a b \<equiv> Ex (J a b)\<close>

definition
  \<open>plus2 a b \<equiv> (THE c. J a b c)\<close>

lemma plus2_eq[simp]:
  \<open>J a b x \<Longrightarrow> plus2 a b = x\<close>
  by (metis plus2_def the_equality join_eq)

lemma plus2_eq2[simp]:
  \<open>J b a x \<Longrightarrow> plus2 a b = x\<close>
  using join_comm plus2_eq by blast

lemma partial_add_commute:
  \<open>disjoint2 a b \<Longrightarrow> plus2 a b = plus2 b a\<close>
  by (clarsimp simp add: disjoint2_def)

lemma join_assoc2:
  \<open>J a b ab \<Longrightarrow> J b c bc \<Longrightarrow> J ab c abc \<Longrightarrow> J a bc abc\<close>
  using join_assoc join_eq by blast

lemma partial_add_assoc:
  \<open>disjoint2 a b \<Longrightarrow> disjoint2 b c \<Longrightarrow> disjoint2 a c \<Longrightarrow>
    plus2 (plus2 a b) c = plus2 a (plus2 b c)\<close>
  apply (clarsimp simp add: disjoint2_def)
  apply (simp add: plus2_def)
  apply (meson join_assoc2 join_comm)
  done

lemma disjoint_sym: \<open>disjoint2 a b \<Longrightarrow> disjoint2 b a\<close>
  using disjoint2_def join_comm by blast

lemma disjoint_add_rightL: \<open>disjoint2 b c \<Longrightarrow> disjoint2 a (plus2 b c) \<Longrightarrow> disjoint2 a b\<close>
  apply (clarsimp simp add: disjoint2_def)
  apply (metis join_assoc join_comm)
  done

lemma disjoint_add_right_commute:
  \<open>disjoint2 b c \<Longrightarrow> disjoint2 a (plus2 b c) \<Longrightarrow> disjoint2 b (plus2 a c)\<close>
  apply (clarsimp simp add: disjoint2_def)
  apply (frule join_assoc, rule join_comm, assumption)
  apply force
  done

end


class dockins_multi_sep_alg = ord +
  fixes J :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
  assumes join_eq: \<open>J a b z1 \<Longrightarrow> J a b z2 \<Longrightarrow> z1 = z2\<close>
  assumes join_cancel: \<open>J x1 y z \<Longrightarrow> J x2 y z \<Longrightarrow> x1 = x2\<close>
  assumes join_comm: \<open>J x y z \<Longrightarrow> J y x z\<close>
  assumes join_assoc: \<open>J x y xy \<Longrightarrow> J xy z xyz \<Longrightarrow> \<exists>yz. J y z yz \<and> J x yz xyz\<close>
  assumes join_multiunits: \<open>\<exists>u. J x u x\<close>
begin

definition
  \<open>join_dup_positivity (aty :: 'a itself) \<equiv>
    \<forall>a b c::'a. J a b c \<longrightarrow> J c c c \<longrightarrow> J a a a\<close>

lemma join_assoc2:
  \<open>J b c bc \<Longrightarrow> J a bc abc \<Longrightarrow> \<exists>ab. J a b ab \<and> J ab c abc\<close>
  by (meson join_assoc join_comm)

lemma dup_add_then_eq:
  \<open>J u u u \<Longrightarrow> J a u b \<Longrightarrow> b = a\<close>
  using join_assoc2 join_cancel join_eq by blast

lemma positivity:
  assumes
    \<open>join_dup_positivity TYPE('a)\<close>
    \<open>J a a' b\<close>
    \<open>J b b' a\<close>
  shows \<open>a = b\<close>
proof -
  obtain w where l1: \<open>J a' b' w\<close> \<open>J a w a\<close>
    using assms join_assoc by blast
  moreover have l3: \<open>J w w w \<close>
    using l1 join_assoc join_cancel join_comm by blast
  ultimately show ?thesis
    using assms dup_add_then_eq join_dup_positivity_def
    by blast
qed


lemma positivity_implies_join_dup_positivity:
  assumes \<open>\<And>a b a' b'. J a a' b \<Longrightarrow> J b b' a \<Longrightarrow> a = b\<close>
  shows \<open>join_dup_positivity TYPE('a)\<close>
  unfolding join_dup_positivity_def
proof clarify
  fix a b c
  assume assms2:
    \<open>J a b c\<close>
    \<open>J c c c\<close>
  then show \<open>J a a a\<close>
    using assms join_assoc2 join_cancel
    by blast
qed


lemma join_strong_dup_positivity:
  assumes
    \<open>join_dup_positivity TYPE('a)\<close>
    \<open>J a b c\<close>
    \<open>J c c c\<close>
  shows
    \<open>a = c\<close>
proof -
  obtain ac where l1: \<open>J a c ac\<close>
    using assms join_assoc2 join_comm by blast
  moreover obtain bc where l2: \<open>J b c bc\<close>
    using assms join_assoc2 join_comm by blast
  moreover have l3: \<open>ac = c\<close>
    using assms l1 dup_add_then_eq local.join_comm positivity
    by blast
  moreover have l4: \<open>bc = c\<close>
    using assms l1 l2 l3
    by (metis join_cancel join_comm join_eq)
  ultimately show \<open>a = c\<close>
    using assms join_cancel by blast
qed

end


class pre_semi_sep_alg = disjoint + plus +
  (* ordered partial commutative monoid *)
  assumes partial_add_assoc: \<open>a ## b \<Longrightarrow> b ## c \<Longrightarrow> a ## c \<Longrightarrow> (a + b) + c = a + (b + c)\<close>
  assumes partial_add_commute: \<open>a ## b \<Longrightarrow> a + b = b + a\<close>
  (* separation laws *)
  assumes disjoint_sym: \<open>a ## b \<Longrightarrow> b ## a\<close>
  assumes disjoint_add_rightL: \<open>b ## c \<Longrightarrow> a ## b + c \<Longrightarrow> a ## b\<close>
  assumes disjoint_add_right_commute: \<open>b ## c \<Longrightarrow> a ## b + c \<Longrightarrow> b ## a + c\<close>
  assumes unit_sub_closure:
    \<open>a ## b \<Longrightarrow> a + b ## c \<Longrightarrow> b ## b \<Longrightarrow> c ## c \<Longrightarrow> a + (b + c) = a \<Longrightarrow> a + b = a\<close>
(* assumes dup_sub_closure: \<open>a ## b \<Longrightarrow> a + b = c \<Longrightarrow> c ## c \<Longrightarrow> c + c = c \<Longrightarrow> a + a = a\<close> *)
begin

lemma positive_impl_unit_sub_closure:
  \<open>(\<And>a b c1 c2. a ## c1 \<Longrightarrow> a + c1 = b \<Longrightarrow> b ## c2 \<Longrightarrow> b + c2 = a \<Longrightarrow> a = b) \<Longrightarrow>
    (\<And>a b c. a ## b \<Longrightarrow> a + b ## c \<Longrightarrow> b ## b \<Longrightarrow> c ## c \<Longrightarrow> a + (b + c) = a \<Longrightarrow> a + b = a)\<close>
  by (metis disjoint_add_rightL disjoint_sym partial_add_assoc partial_add_commute)

lemma unit_sub_closure_impl_positive:
  \<open>(\<And>a b c. a ## b \<Longrightarrow> a + b ## c \<Longrightarrow> b ## b \<Longrightarrow> c ## c \<Longrightarrow> a + (b + c) = a \<Longrightarrow> a + b = a) \<Longrightarrow>
    (\<And>a b c1 c2. a ## c1 \<Longrightarrow> a + c1 = b \<Longrightarrow> b ## c2 \<Longrightarrow> b + c2 = a \<Longrightarrow> a = b)\<close>
  by (metis disjoint_add_rightL disjoint_sym partial_add_assoc partial_add_commute)

lemma \<open>a ## c1 \<Longrightarrow> a + c1 = b \<Longrightarrow> b ## c2 \<Longrightarrow> b + c2 = a \<Longrightarrow> a = b\<close>
  by (metis disjoint_add_rightL disjoint_sym partial_add_assoc partial_add_commute unit_sub_closure)

definition subadd :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (infix \<open>\<prec>\<^sub>+\<close> 50) where
  \<open>a \<prec>\<^sub>+ b \<equiv> a \<noteq> b \<and> (\<exists>c. a ## c \<and> a + c = b)\<close>

definition subaddeq :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (infix \<open>\<preceq>\<^sub>+\<close> 50) where
  \<open>a \<preceq>\<^sub>+ b \<equiv> a = b \<or> (\<exists>c. a ## c \<and> a + c = b)\<close>

lemma subadd_order:
  \<open>class.order (\<preceq>\<^sub>+) (\<prec>\<^sub>+)\<close>
  apply (unfold subadd_def subaddeq_def)
  apply standard
     apply (rule iffI conjI impI; elim conjE exE disjE)
       apply clarsimp
       apply (rule conjI, force)
       apply clarsimp
       apply (metis disjoint_add_rightL disjoint_sym partial_add_assoc partial_add_commute unit_sub_closure)
      apply blast
     apply blast
    apply blast
   apply clarsimp
   apply (elim disjE)
      apply blast
     apply blast
    apply blast
   apply clarsimp
   apply (metis disjoint_add_rightL disjoint_add_right_commute disjoint_sym partial_add_assoc
      partial_add_commute)
  apply (metis disjoint_add_rightL disjoint_sym partial_add_assoc partial_add_commute unit_sub_closure)
  done

definition \<open>sepadd_unit2 u \<equiv> u ## u \<and> (\<forall>a. u ## a \<longrightarrow> a + u = a)\<close>

lemma \<open>sepadd_unit2 u \<Longrightarrow> u \<preceq>\<^sub>+ a \<Longrightarrow> a ## b \<Longrightarrow> u \<preceq>\<^sub>+ a + b\<close>
  unfolding sepadd_unit2_def subaddeq_def
  by (metis disjoint_add_right_commute disjoint_sym partial_add_commute)

lemma \<open>sepadd_unit2 u \<Longrightarrow> u \<preceq>\<^sub>+ a \<Longrightarrow> a ## b \<Longrightarrow> u \<preceq>\<^sub>+ b\<close>
  unfolding sepadd_unit2_def subaddeq_def
  by (metis disjoint_add_rightL disjoint_sym partial_add_commute)

lemma \<open>sepadd_unit2 u \<Longrightarrow> u \<preceq>\<^sub>+ a \<Longrightarrow> a ## b \<Longrightarrow> u \<preceq>\<^sub>+ a + b\<close>
  unfolding sepadd_unit2_def subaddeq_def
  by (metis disjoint_add_right_commute disjoint_sym partial_add_commute)

lemma \<open>sepadd_unit2 u \<Longrightarrow> u \<preceq>\<^sub>+ a \<Longrightarrow> a ## b \<Longrightarrow> u \<preceq>\<^sub>+ b\<close>
  unfolding sepadd_unit2_def subaddeq_def
  by (metis disjoint_add_rightL disjoint_sym partial_add_commute)

lemma 
    \<open>\<forall>u a. a \<preceq>\<^sub>+ u \<longrightarrow> sepadd_unit2 u \<longrightarrow> sepadd_unit2 a\<close>
   by (clarsimp simp add: sepadd_unit2_def subaddeq_def,
      metis unit_sub_closure disjoint_add_rightL disjoint_sym partial_add_commute)

lemma \<open>sepadd_unit2 u \<Longrightarrow> a ## b \<Longrightarrow> a + b = u \<Longrightarrow> sepadd_unit2 a\<close>
  unfolding sepadd_unit2_def subaddeq_def
  by (metis disjoint_add_rightL disjoint_sym partial_add_commute unit_sub_closure[of _ a b])


definition \<open>is_sepdup a \<equiv> a ## a \<and> a + a = a\<close>

lemma \<open>sepadd_unit2 u \<Longrightarrow> is_sepdup u\<close>
  by (simp add: is_sepdup_def sepadd_unit2_def)

lemma sepdup_antimono_iff_positivity:
  \<open>(\<forall>a b. a \<preceq>\<^sub>+ b \<longrightarrow> is_sepdup b \<longrightarrow> is_sepdup a) \<longleftrightarrow>
    (\<forall>a b c. a ## b \<longrightarrow> a + b = c \<longrightarrow> c ## c \<longrightarrow> c + c = c \<longrightarrow> a + a = a)\<close>
  apply (rule iffI)
   apply (meson is_sepdup_def subaddeq_def; fail)
  apply (simp add: is_sepdup_def subaddeq_def, clarify)
  apply (meson disjoint_add_rightL disjoint_sym)
  done
  

lemma \<open>a \<preceq>\<^sub>+ b \<Longrightarrow> is_sepdup b \<Longrightarrow> is_sepdup a\<close>
  nitpick
  oops

end

context order
begin

definition covered_by :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (infix \<open>\<prec>\<^sub>c\<close> 50) where
  \<open>x \<prec>\<^sub>c y \<equiv> x < y \<and> (\<forall>z. x \<le> z \<longrightarrow> z < y \<longrightarrow> z = x)\<close>

end

context perm_alg
begin

text \<open> addition irreducible; cf. join/meet irreducible \<close>
definition sepadd_irr :: \<open>'a \<Rightarrow> bool\<close> where
  \<open>sepadd_irr x \<equiv> (\<not> sepadd_unit x) \<and> (\<forall>a b. a < x \<longrightarrow> b < x \<longrightarrow> a ## b \<longrightarrow> a + b < x)\<close>

definition \<open>foundation a \<equiv> {j. j \<le> a \<and> sepadd_irr j}\<close>

end

section \<open> Labelled Permission algebra \<close>

text \<open>
  This subclass is supposed to be the algebraic version of a heap.
  It introduces an order which must be compatible with, but can be more coarse than,
  the subresource relation. The equivalence classes induced by this order represent
  resources with the same set of labels.

  We want labels to form a distributive lattice, to take advantage of
  Birkhoff's representation theorem.
  TODO,sorry: The law \<open>labels_strong_distrib_law\<close> probably does this, but I need to check.
\<close>

class labelled_perm_alg = perm_alg +
  fixes labels_leq :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (infix \<open>\<le>\<^sub>l\<close> 50)
    and labels_less :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (infix \<open><\<^sub>l\<close> 50)
  assumes labels_leq_less_preorder:
    \<open>preordering labels_leq labels_less\<close>
  assumes labels_less_embeds: \<open>\<And>a b. a < b \<Longrightarrow> a <\<^sub>l b\<close>
  assumes labels_leq_upper_bound:
    \<open>\<And>a b c. a ## b \<Longrightarrow> a \<le>\<^sub>l c \<Longrightarrow> b \<le>\<^sub>l c \<Longrightarrow> a + b \<le>\<^sub>l c\<close>
  assumes labels_strong_distrib_law:
    \<open>\<And>a b c.
      a ## b \<Longrightarrow> a ## c \<Longrightarrow> inf_exists b c \<Longrightarrow> inf_exists (a + b) (a + c) \<Longrightarrow>
        glb (a + b) (a + c) \<le>\<^sub>l a + glb b c\<close>
begin

lemma labels_leq_embeds:
  \<open>a \<le> b \<Longrightarrow> a \<le>\<^sub>l b\<close>
  using labels_leq_less_preorder labels_less_embeds
  by (metis order.order_iff_strict preordering.axioms(1) partial_preordering.refl
      preordering.strict_implies_order)

lemma labels_leq_add:
  \<open>a ## b \<Longrightarrow> a \<le>\<^sub>l (a + b)\<close>
  by (simp add: labels_leq_embeds)

definition labels_eq :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (infix \<open>=\<^sub>l\<close> 50) where
  \<open>labels_eq a b \<equiv> a \<le>\<^sub>l b \<and> b \<le>\<^sub>l a\<close>

lemma labels_eq_equivp: \<open>equivp (=\<^sub>l)\<close>
  unfolding labels_eq_def
  using labels_leq_less_preorder
  by (force intro: equivpI reflpI sympI transpI dest: preordering_refl preordering_trans)

lemma disjoint_units_have_same_labels:
  assumes
    \<open>a ## b\<close>
    \<open>sepadd_unit a\<close>
    \<open>sepadd_unit b\<close>
  shows
    \<open>a =\<^sub>l b\<close>
  using assms
  by (metis labels_eq_def labels_leq_add disjoint_sym sepadd_unit_def)

lemma same_labels_as_unit_is_unit:
  assumes
    \<open>a ## b\<close>
    \<open>sepadd_unit a\<close>
    \<open>a =\<^sub>l b\<close>
  shows
    \<open>sepadd_unit b\<close>
  using assms
  by (metis labels_eq_def order.order_iff_strict labels_leq_less_preorder labels_less_embeds
      partial_le_plus sepadd_unit_def preordering.strict_iff_not)

subsection  \<open> Label overlap \<close>

definition \<open>label_overlap a b \<equiv> \<exists>c. c \<le>\<^sub>l a \<and> c \<le>\<^sub>l b \<and> \<not> sepadd_unit c\<close>

lemma label_overlap_refl:
  \<open>\<not> sepadd_unit a \<Longrightarrow> label_overlap a a\<close>
  using label_overlap_def labels_leq_embeds by blast

lemma label_overlap_sym:
  \<open>label_overlap a b \<Longrightarrow> label_overlap b a\<close>
  using label_overlap_def by blast

lemma same_labels_implies_label_overlap:
  \<open>a =\<^sub>l b \<Longrightarrow> \<not> sepadd_unit a \<Longrightarrow> \<not> sepadd_unit b \<Longrightarrow> label_overlap a b\<close>
  using label_overlap_def labels_eq_def labels_leq_embeds by blast

end

class halving_labelled_perm_alg = halving_perm_alg + labelled_perm_alg
begin

lemma half_subseteq_labels: \<open>half a \<le>\<^sub>l a\<close>
  by (metis half_additive_split half_self_disjoint labels_leq_embeds partial_le_plus2)

lemma half_superseteq_labels: \<open>a \<le>\<^sub>l half a\<close>
  by (metis half_additive_split half_self_disjoint labels_leq_upper_bound labels_leq_embeds
      order.refl)

lemma half_has_same_labels: \<open>half a =\<^sub>l a\<close>
  by (simp add: half_subseteq_labels half_superseteq_labels labels_eq_def)

end



context sep_alg
begin

lemma sepadd_irr_eq:
  \<open>sepadd_irr x \<longleftrightarrow> x \<noteq> 0 \<and> (\<forall>a b. a < x \<longrightarrow> b < x \<longrightarrow> a ## b \<longrightarrow> a + b < x)\<close>
  unfolding sepadd_irr_def
  using zero_only_unit by presburger

lemma sepadd_irr_eq2:
  \<open>sepadd_irr x \<longleftrightarrow> x \<noteq> 0 \<and> (\<forall>a b. a ## b \<longrightarrow> x = a + b \<longrightarrow> x = a \<or> x = b)\<close>
  unfolding sepadd_irr_eq
  apply (rule iffI)
   apply (metis order.not_eq_order_implies_strict order.irrefl partial_le_plus partial_le_plus2)
  apply (metis less_iff_sepadd nless_le sepadd_left_mono)
  done

end


lemma (in distrib_sep_alg) sepadd_irr_distrib_eq:
  shows \<open>sepadd_irr x \<longleftrightarrow> x \<noteq> 0 \<and> (\<forall>a b. a ## b \<longrightarrow> x \<le> a + b \<longrightarrow> x \<le> a \<or> x \<le> b)\<close>
  unfolding sepadd_irr_eq
  apply (rule iffI)
   apply (simp add: inf.order_iff inf_add_distrib1, metis disjoint_add_rightL disjoint_preservation
      le_iff_sepadd order.strict_implies_not_eq inf.cobounded1 inf.cobounded2 neq_le_trans)
  apply (force simp add: order.strict_iff_not inf.absorb_iff2 inf_add_distrib1)
  done

class big_sep_alg = distrib_sep_alg + cancel_perm_alg
begin

lemma False
  nitpick
  oops

(*
definition
  \<open>good_prog b \<equiv>
      (\<forall>j. sepadd_irr j \<longrightarrow>
        ((\<exists>x y. b x y \<and> j \<le> x \<and> \<not> j \<le> y) \<longrightarrow> (\<forall>x' y'. b x' y' \<longrightarrow> j \<le> x' \<and> \<not> j \<le> y')) \<and>
        ((\<exists>x y. b x y \<and> \<not> j \<le> x \<and> j \<le> y) \<longrightarrow> (\<forall>x' y'. b x' y' \<longrightarrow> \<not> j \<le> x' \<and> j \<le> y'))
      ) \<and> frame_closed b\<close>

definition
  \<open>rgsep_rely S \<equiv> (\<lambda>a b. \<exists>x y. (x, y) \<in> S \<and> framed_subresource_rel \<top> x y a b)\<^sup>*\<^sup>*\<close>

definition
  \<open>good_rely b \<equiv>
      (\<forall>j. sepadd_irr j \<longrightarrow>
        ((\<exists>x y. b x y \<and> j \<le> x \<and> \<not> j \<le> y) \<longrightarrow> (\<forall>x' y'. b x' y' \<longrightarrow> j \<le> x' \<and> \<not> j \<le> y')) \<and>
        ((\<exists>x y. b x y \<and> \<not> j \<le> x \<and> j \<le> y) \<longrightarrow> (\<forall>x' y'. b x' y' \<longrightarrow> \<not> j \<le> x' \<and> j \<le> y'))
      ) \<and>
      (\<forall>x y f. b x y \<longrightarrow> x ## f \<longrightarrow> y ## f \<longrightarrow> b (x + f) (y + f))\<close>

lemma wsstable_sepconj_semidistrib_backwards:
  \<open>r = rgsep_rely S \<Longrightarrow>
    S = {a} \<Longrightarrow>
    deterministic (r - (=)) \<Longrightarrow>
    Ex1 P \<Longrightarrow> Ex1 Q \<Longrightarrow>
    X = \<lceil> P \<^emph> Q \<rceil>\<^bsub>r\<^esub> \<Longrightarrow>
    Y = \<lceil> P \<rceil>\<^bsub>r\<^esub> \<Longrightarrow>
    Z = \<lceil> Q \<rceil>\<^bsub>r\<^esub> \<Longrightarrow>
    X \<le> Y \<^emph> Z\<close>
  nitpick
  oops

end

lemma (in perm_alg) wsstable_semidistrib_disjoint_pre_state_strong:
  \<open>\<forall>a. (P \<^emph> Q) a \<longrightarrow> changedom r\<^sup>*\<^sup>* a \<longrightarrow> sepadd_unit a \<Longrightarrow>
    changes r\<^sup>*\<^sup>* \<sqinter> rel_liftL (P \<^emph> Q) \<le> compatible \<Longrightarrow>
    \<lceil> P \<^emph> Q \<rceil>\<^bsub>r\<^esub> \<le> \<lceil> P \<rceil>\<^bsub>r\<^esub> \<^emph> \<lceil> Q \<rceil>\<^bsub>r\<^esub>\<close>
  apply (clarsimp simp add: changedom_def rel_liftL_def)
  apply (clarsimp simp add: wsstable_def sepconj_def pre_state_def le_fun_def
      fun_eq_iff imp_ex imp_conjL simp del: all_simps(5))
  apply (drule spec2, drule mp, assumption, drule mp, assumption, drule mp, assumption)
  apply (drule spec, drule mp, assumption)
  apply (case_tac \<open>x = h1 + h2\<close>, blast)
  apply clarsimp
  apply (frule(2) disjoint_units_identical)
  apply (clarsimp simp add: sepadd_unit_left)
  apply (metis compatible_to_unit_is_unit_right compatible_unit_disjoint sepadd_unit_idem_add
      sepadd_unit_selfsep rtranclp.rtrancl_refl)
(*
  apply (rule_tac x=x in exI)
  apply (rule_tac x=h2 in exI)
  apply (rule conjI)
   apply (metis compatible_unit_disjoint)
  apply (rule conjI)
   apply (metis compatible_to_unit_is_unit_right)
  apply force
*)
  done

lemma (in perm_alg) wsstable_semidistrib_no_pre_state:
  \<open>\<forall>h1. (P \<^emph> Q) h1 \<longrightarrow> pre_state r h1 \<longrightarrow> False \<Longrightarrow>
    \<lceil> P \<^emph> Q \<rceil>\<^bsub>r\<^esub> \<le> \<lceil> P \<rceil>\<^bsub>r\<^esub> \<^emph> \<lceil> Q \<rceil>\<^bsub>r\<^esub>\<close>
  apply (insert wsstable_semidistrib_disjoint_pre_state_strong[of P Q r])
  apply (drule meta_mp)
   apply (metis changes_def converse_rtranclpE pre_state_def)
  apply (drule meta_mp)
   apply (clarsimp simp add: rel_liftL_def changes_def pre_state_def)
   apply (metis converse_rtranclpE)
  apply assumption
  done

lemma (in inf_sep_alg) wsstable_semidistrib_disjoint_pre_state:
  \<open>\<forall>h1 h2. (P \<^emph> Q) h1 \<longrightarrow> changedom r h2 \<longrightarrow> h1 \<sqinter> h2 = 0 \<Longrightarrow>
    \<lceil> P \<^emph> Q \<rceil>\<^bsub>r\<^esub> \<le> \<lceil> P \<rceil>\<^bsub>r\<^esub> \<^emph> \<lceil> Q \<rceil>\<^bsub>r\<^esub>\<close>
  apply (insert wsstable_semidistrib_disjoint_pre_state_strong[of P Q r])
  apply (drule meta_mp)
   apply (metis changedom_rtranclp sepinf_idem zero_only_unit)
  apply (drule meta_mp)
   apply (force simp add: rel_liftL_def changes_def pre_state_def all_compatible)
  apply assumption
  done

lemma (in inf_perm_alg) wsstable_semidistrib_disjoint_pre_state_strong2:
  \<open>\<forall>h1 h2. (P \<^emph> Q) h1 \<longrightarrow> changedom r h2 \<longrightarrow> compatible h1 h2 \<longrightarrow> sepadd_unit (h1 \<sqinter> h2) \<Longrightarrow>
    changes r\<^sup>*\<^sup>* \<sqinter> rel_liftL (P \<^emph> Q) \<le> compatible \<Longrightarrow>
    \<lceil> P \<^emph> Q \<rceil>\<^bsub>r\<^esub> \<le> \<lceil> P \<rceil>\<^bsub>r\<^esub> \<^emph> \<lceil> Q \<rceil>\<^bsub>r\<^esub>\<close>
  apply (insert wsstable_semidistrib_disjoint_pre_state_strong[of P Q r])
  apply (metis changedom_rtranclp compatible_refl sepinf_idem)
  done
*)

(* The situation that we want to prove is
   { pa \<^emph> pb \<^emph> pc              }
   { pa \<^emph> pb  }         \<parallel> { pc }
    skip                \<parallel>
    { sp c\<^sup>\<star> (pa \<^emph> pb) } \<parallel>
     a       \<parallel>  b       \<parallel>  c
    { qa   } \<parallel> { qb   } \<parallel> { qc }
    { qa \<^emph> qb \<^emph> qc             }
*)
lemma (in perm_alg) wsstable_semidistrib_realistic:
  \<open>r = c\<^sup>*\<^sup>* \<Longrightarrow>
    \<forall>r\<in>{a,b,c}.
      (\<forall>x. \<not> r x x) \<and>
      (\<forall>x y z. r x y \<longrightarrow> r y z \<longrightarrow> \<not> r x z) \<and>
      frame_closed r \<and>
      Ex (pre_state r) \<and>
      deterministic r \<Longrightarrow>
    Ex1 pa \<Longrightarrow>
    Ex1 pb \<Longrightarrow>
    Ex1 pc \<Longrightarrow>
    \<comment> \<open> stability \<close>
    sp ((a \<squnion> b)\<^sup>*\<^sup>*) pc = pc \<Longrightarrow>
    sp ((a \<squnion> c)\<^sup>*\<^sup>*) pb' = pb' \<Longrightarrow>
    sp ((b \<squnion> c)\<^sup>*\<^sup>*) pa' = pa' \<Longrightarrow>
    sp ((a \<squnion> c)\<^sup>*\<^sup>*) pb = pb \<Longrightarrow>
    sp ((b \<squnion> c)\<^sup>*\<^sup>*) pa = pa \<Longrightarrow>
    sp (c\<^sup>*\<^sup>*) (pa \<^emph> pb) = pa' \<^emph> pb' \<Longrightarrow>
    \<comment> \<open> the goal \<close>
    pa' \<^emph> pb' \<^emph> pc \<le> sp (c\<^sup>*\<^sup>*) pa \<^emph> sp (c\<^sup>*\<^sup>*) pb \<^emph> pc\<close>
  nitpick
  oops

(*
class finite_sep_alg = distrib_sep_alg +
  assumes finite_univ: \<open>finite (UNIV :: 'a set)\<close>
  fixes \<II> :: \<open>'a set\<close>
  assumes \<open>\<II> = Collect sepadd_irr\<close>
begin

lemma \<open>sepadd_irr a \<Longrightarrow> sepadd_irr b \<Longrightarrow> a \<noteq> b \<Longrightarrow> a \<le> c \<Longrightarrow> b \<le> c \<Longrightarrow> a ## b\<close>
  apply (clarsimp simp add: sepadd_irr_distrib_eq)
  by (metis disjoint_preservation disjoint_sym dual_order.antisym le_iff_sepadd)

end
*)


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
  done

lemma refinement_atomic_condition1:
  \<open>b' \<le> b \<Longrightarrow> sp b (wlp J P) s \<le> Q \<Longrightarrow> sp b' (wlp J P) s \<le> Q\<close>
  using sp_rel_mono
  by auto

lemma refinement_atomic_condition2:
  \<open>b' \<le> b \<Longrightarrow> unframe_prop f b \<Longrightarrow> unframe_prop f b'\<close>
  oops


end