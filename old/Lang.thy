theory Lang
  imports SepLogic
begin

section \<open> Concurrent Separation Logic Language \<close>

(* Based on
    Precision and the Conjunction Rule in Concurrent Separation Logic
    Alexey Gotsman, Josh Berdine, Byron Cook
*)


subsection \<open> State \<close>

datatype 'v varenv = VarEnv (the_varenv: \<open>'v \<rightharpoonup> nat\<close>)
datatype heap = Heap (the_heap: \<open>nat \<rightharpoonup> nat\<close>)
datatype resources = Resources (the_resources: \<open>nat set\<close>)

definition \<open>remove_res j r \<equiv> case r of Resources R \<Rightarrow> Resources (R - {j})\<close>
definition \<open>insert_res j r \<equiv> case r of Resources R \<Rightarrow> Resources (insert j R)\<close>

lemma resources_the_of_remove[simp]:
  \<open>the_resources (remove_res r R) = the_resources R - {r}\<close>
  by (simp add: remove_res_def split: resources.splits)

lemma resources_the_of_insert[simp]:
  \<open>the_resources (insert_res r R) = insert r (the_resources R)\<close>
  by (simp add: insert_res_def split: resources.splits)


lemma VarEnv_always_ex: \<open>\<exists>v'. v = VarEnv v'\<close>
  by (meson varenv.exhaust_sel)
lemma Heap_always_ex: \<open>\<exists>h'. h = Heap h'\<close>
  by (meson heap.exhaust_sel)
lemma Resources_always_ex: \<open>\<exists>r'. r = Resources r'\<close>
  by (meson resources.exhaust_sel)


lemma the_varenv_eq_iff:
  \<open>the_varenv a = b \<longleftrightarrow> a = VarEnv b\<close>
  by fastforce
lemma the_heap_eq_iff:
  \<open>the_heap a = b \<longleftrightarrow> a = Heap b\<close>
  by fastforce
lemma the_resources_eq_iff:
  \<open>the_resources a = b \<longleftrightarrow> a = Resources b\<close>
  by fastforce

lemma the_varenv_inject:
  \<open>the_varenv a = the_varenv b \<longleftrightarrow> a = b\<close>
  by (metis varenv.exhaust_sel)
lemma the_heap_inject:
  \<open>the_heap a = the_heap b \<longleftrightarrow> a = b\<close>
  by (metis heap.exhaust_sel)
lemma the_resources_inject:
  \<open>the_resources a = the_resources b \<longleftrightarrow> a = b\<close>
  by (metis resources.exhaust_sel)

type_synonym 'v state = \<open>'v varenv \<times> heap \<times> resources\<close>



subsubsection \<open>Seplogic Instances\<close>

instantiation varenv :: (type) seplogic
begin
  definition
    \<open>disjoint_varenv a b \<equiv> dom (the_varenv a) \<inter> dom (the_varenv b) = {}\<close>
  definition
    \<open>bot_varenv \<equiv> VarEnv Map.empty\<close>
  definition
    \<open>zero_varenv \<equiv> VarEnv Map.empty\<close>
  definition
    \<open>plus_varenv a b \<equiv> VarEnv (the_varenv a ++ the_varenv b)\<close>
  definition
    \<open>less_eq_varenv a b \<equiv> the_varenv a \<subseteq>\<^sub>m the_varenv b\<close>
  definition
    \<open>less_varenv a b \<equiv> the_varenv a \<subseteq>\<^sub>m the_varenv b \<and> \<not> the_varenv b \<subseteq>\<^sub>m the_varenv a\<close>

instance
proof
  fix a b c :: \<open>'a varenv\<close>

  show \<open>(a < b) = (a \<le> b \<and> \<not> b \<le> a)\<close>
    by (simp add: less_varenv_def less_eq_varenv_def)
  show \<open>a \<le> a\<close>
    by (simp add: less_eq_varenv_def)
  show \<open>a \<le> b \<Longrightarrow> b \<le> c \<Longrightarrow> a \<le> c\<close>
    by (force intro: map_le_trans simp add: less_eq_varenv_def)
  show \<open>a \<le> b \<Longrightarrow> b \<le> a \<Longrightarrow> a = b\<close>
    by (simp add: varenv.expand less_eq_varenv_def prod_eq_iff map_le_antisym)
  show \<open>a \<currency> b \<Longrightarrow> b \<currency> c \<Longrightarrow> a \<currency> c \<Longrightarrow> a + b + c = a + (b + c)\<close>
    by (simp add: plus_varenv_def)
  show \<open>a \<currency> b \<Longrightarrow> a + b = b + a\<close>
    by (metis disjoint_varenv_def plus_varenv_def map_add_comm)
  show \<open>bot \<le> a\<close>
    by (clarsimp simp add: bot_varenv_def less_eq_varenv_def)
  show \<open>a \<currency> a \<Longrightarrow> a = 0\<close>
    by (simp add: disjoint_varenv_def zero_varenv_def the_varenv_eq_iff)
  show \<open>a \<currency> b = b \<currency> a\<close>
    by (force simp add: disjoint_varenv_def)
  show \<open>0 \<currency> a\<close>
    by (simp add: disjoint_varenv_def zero_varenv_def)

  have \<open>a \<le> b \<Longrightarrow>
    a \<currency> VarEnv (the_varenv b |` (- dom (the_varenv a))) \<and>
    b = a + VarEnv (the_varenv b |` (- dom (the_varenv a)))\<close>
    unfolding less_eq_varenv_def disjoint_varenv_def plus_varenv_def
    by (simp add: the_varenv_eq_iff[symmetric] map_le_split)
  then show \<open>(a \<le> b) = (\<exists>c. a \<currency> c \<and> b = a + c)\<close>
    unfolding less_eq_varenv_def disjoint_varenv_def plus_varenv_def
    by (fastforce simp add: map_add_comm)

  show \<open>0 + a = a\<close>
    by (simp add: plus_varenv_def zero_varenv_def)
  show \<open>a \<currency> (b + c) = (a \<currency> b \<and> a \<currency> c)\<close>
    by (force simp add: disjoint_varenv_def plus_varenv_def Int_Un_distrib)
qed
end

instantiation heap :: seplogic
begin
  definition
    \<open>disjoint_heap a b \<equiv> dom (the_heap a) \<inter> dom (the_heap b) = {}\<close>
  definition
    \<open>bot_heap \<equiv> Heap Map.empty\<close>
  definition
    \<open>zero_heap \<equiv> Heap Map.empty\<close>
  definition
    \<open>plus_heap a b \<equiv> Heap (the_heap a ++ the_heap b)\<close>
  definition
    \<open>less_eq_heap a b \<equiv> the_heap a \<subseteq>\<^sub>m the_heap b\<close>
  definition
    \<open>less_heap a b \<equiv> the_heap a \<subseteq>\<^sub>m the_heap b \<and> \<not> the_heap b \<subseteq>\<^sub>m the_heap a\<close>

instance
proof
  fix a b c :: heap

  show \<open>(a < b) = (a \<le> b \<and> \<not> b \<le> a)\<close>
    by (simp add: less_heap_def less_eq_heap_def)
  show \<open>a \<le> a\<close>
    by (simp add: less_eq_heap_def)
  show \<open>a \<le> b \<Longrightarrow> b \<le> c \<Longrightarrow> a \<le> c\<close>
    by (force intro: map_le_trans simp add: less_eq_heap_def)
  show \<open>a \<le> b \<Longrightarrow> b \<le> a \<Longrightarrow> a = b\<close>
    by (simp add: heap.expand less_eq_heap_def prod_eq_iff map_le_antisym)
  show \<open>a \<currency> b \<Longrightarrow> b \<currency> c \<Longrightarrow> a \<currency> c \<Longrightarrow> a + b + c = a + (b + c)\<close>
    by (simp add: plus_heap_def)
  show \<open>a \<currency> b \<Longrightarrow> a + b = b + a\<close>
    by (metis disjoint_heap_def plus_heap_def map_add_comm)
  show \<open>bot \<le> a\<close>
    by (clarsimp simp add: bot_heap_def less_eq_heap_def)
  show \<open>a \<currency> a \<Longrightarrow> a = 0\<close>
    by (simp add: disjoint_heap_def zero_heap_def the_heap_eq_iff)
  show \<open>a \<currency> b = b \<currency> a\<close>
    by (force simp add: disjoint_heap_def)
  show \<open>0 \<currency> a\<close>
    by (simp add: disjoint_heap_def zero_heap_def)

  have \<open>a \<le> b \<Longrightarrow>
    a \<currency> Heap (the_heap b |` (- dom (the_heap a))) \<and>
    b = a + Heap (the_heap b |` (- dom (the_heap a)))\<close>
    unfolding less_eq_heap_def disjoint_heap_def plus_heap_def
    by (simp add: the_heap_eq_iff[symmetric] map_le_split)
  then show \<open>(a \<le> b) = (\<exists>c. a \<currency> c \<and> b = a + c)\<close>
    unfolding less_eq_heap_def disjoint_heap_def plus_heap_def
    by (fastforce simp add: map_add_comm)

  show \<open>0 + a = a\<close>
    by (simp add: plus_heap_def zero_heap_def)
  show \<open>a \<currency> (b + c) = (a \<currency> b \<and> a \<currency> c)\<close>
    by (force simp add: disjoint_heap_def plus_heap_def Int_Un_distrib)
qed
end

instantiation resources :: seplogic
begin
  definition
    \<open>disjoint_resources a b \<equiv> the_resources a \<inter> the_resources b = {}\<close>
  definition
    \<open>bot_resources \<equiv> Resources {}\<close>
  definition
    \<open>zero_resources \<equiv> Resources {}\<close>
  definition
    \<open>plus_resources a b \<equiv> Resources (the_resources a \<union> the_resources b)\<close>
  definition
    \<open>less_eq_resources a b \<equiv> the_resources a \<subseteq> the_resources b\<close>
  definition
    \<open>less_resources a b \<equiv> the_resources a \<subseteq> the_resources b \<and> \<not> the_resources b \<subseteq> the_resources a\<close>

instance
proof
  fix a b c :: resources

  show \<open>(a < b) = (a \<le> b \<and> \<not> b \<le> a)\<close>
    by (simp add: less_resources_def less_eq_resources_def)
  show \<open>a \<le> a\<close>
    by (simp add: less_eq_resources_def)
  show \<open>a \<le> b \<Longrightarrow> b \<le> c \<Longrightarrow> a \<le> c\<close>
    by (force simp add: less_eq_resources_def)
  show \<open>a \<le> b \<Longrightarrow> b \<le> a \<Longrightarrow> a = b\<close>
    by (simp add: less_eq_resources_def resources.expand)
  show \<open>a \<currency> b \<Longrightarrow> b \<currency> c \<Longrightarrow> a \<currency> c \<Longrightarrow> a + b + c = a + (b + c)\<close>
    by (force simp add: disjoint_resources_def plus_resources_def)
  show \<open>a \<currency> b \<Longrightarrow> a + b = b + a\<close>
    by (force simp add: disjoint_resources_def plus_resources_def)
  show \<open>bot \<le> a\<close>
    by (clarsimp simp add: bot_resources_def less_eq_resources_def)
  show \<open>a \<currency> a \<Longrightarrow> a = 0\<close>
    by (simp add: disjoint_resources_def zero_resources_def the_resources_eq_iff)
  show \<open>a \<currency> b = b \<currency> a\<close>
    by (force simp add: disjoint_resources_def)
  show \<open>0 \<currency> a\<close>
    by (simp add: disjoint_resources_def zero_resources_def)
  show \<open>(a \<le> b) = (\<exists>c. a \<currency> c \<and> b = a + c)\<close>
    apply (simp add: less_eq_resources_def disjoint_resources_def plus_resources_def)
    apply (rule iffI)
     apply (metis Diff_disjoint Diff_partition the_resources_eq_iff)
    apply force
    done
  show \<open>0 + a = a\<close>
    by (simp add: plus_resources_def zero_resources_def)
  show \<open>a \<currency> (b + c) = (a \<currency> b \<and> a \<currency> c)\<close>
    by (force simp add: disjoint_resources_def plus_resources_def Int_Un_distrib)
qed

end

instantiation prod :: (seplogic,seplogic) seplogic
begin
  definition
    \<open>disjoint_prod a b \<equiv> fst a \<currency> fst b \<and> snd a \<currency> snd b\<close>
  declare disjoint_prod_def[simp]
  definition
    \<open>less_eq_prod a b \<equiv> fst a \<le> fst b \<and> snd a \<le> snd b\<close>
  declare less_eq_prod_def[simp]
  definition
    \<open>less_prod a b \<equiv> fst a \<le> fst b \<and> snd a \<le> snd b \<and> \<not> (fst b \<le> fst a \<and> snd b \<le> snd a)\<close>
  declare less_prod_def[simp]
  definition
    \<open>zero_prod \<equiv> (0, 0)\<close>
  declare zero_prod_def[simp]
  definition
    \<open>bot_prod \<equiv> (bot, bot)\<close>
  declare bot_prod_def[simp]
  definition
    \<open>plus_prod a b \<equiv> (fst a + fst b, snd a + snd b)\<close>
  declare plus_prod_def[simp]

instance
proof
  fix a b c :: \<open>('a, 'b) prod\<close>
  show \<open>a \<currency> b \<Longrightarrow> b \<currency> c \<Longrightarrow> a \<currency> c \<Longrightarrow> a + b + c = a + (b + c)\<close>
    by (clarsimp simp add: partial_add_assoc)
  show \<open>a \<currency> b \<Longrightarrow> a + b = b + a\<close>
    by (metis disjoint_prod_def plus_prod_def partial_add_commute)
  show \<open>0 + a = a\<close>
    by simp
  show \<open>(a < b) = (a \<le> b \<and> \<not> b \<le> a)\<close>
    by simp
  show \<open>a \<le> a\<close>
    by simp
  show \<open>a \<le> b \<Longrightarrow> b \<le> c \<Longrightarrow> a \<le> c\<close>
    by force
  show \<open>a \<le> b \<Longrightarrow> b \<le> a \<Longrightarrow> a = b\<close>
    by (clarsimp simp add: prod_eq_iff)
  show \<open>bot \<le> a\<close>
    by simp
  show \<open>a \<currency> a \<Longrightarrow> a = 0\<close>
    by (metis (mono_tags) disjoint_refl_only_zero disjoint_prod_def prod.exhaust_sel zero_prod_def)
  show \<open>a \<currency> b = b \<currency> a\<close>
    by (simp add: disjoint_symm)
  show \<open>0 \<currency> a\<close>
    by simp
  show \<open>(a \<le> b) = (\<exists>c. a \<currency> c \<and> b = a + c)\<close>
    by (force simp add: le_iff_sepadd prod_eq_iff)
  show \<open>a \<currency> (b + c) = (a \<currency> b \<and> a \<currency> c)\<close>
    by force
qed

end

subsubsection \<open>Right Cancellative Seplogic Instances\<close>

instantiation varenv :: (type) right_cancel_seplogic
begin

instance
proof
  fix a b c :: \<open>'a varenv\<close>
  show \<open>a \<currency> c \<Longrightarrow> b \<currency> c \<Longrightarrow> (a + c = b + c) = (a = b)\<close>
    unfolding disjoint_varenv_def plus_varenv_def
    by (metis map_disjoint_dom_cancel_right varenv.expand varenv.inject)
qed

end

instantiation heap :: right_cancel_seplogic
begin

instance
proof
  fix a b c :: heap
  show \<open>a \<currency> c \<Longrightarrow> b \<currency> c \<Longrightarrow> (a + c = b + c) = (a = b)\<close>
    unfolding disjoint_heap_def plus_heap_def
    by (metis heap.expand heap.inject inf_commute map_disjoint_dom_cancel_right)
qed

end

instantiation resources :: right_cancel_seplogic
begin

instance
proof
  fix a b c :: resources
  show \<open>a \<currency> c \<Longrightarrow> b \<currency> c \<Longrightarrow> (a + c = b + c) = (a = b)\<close>
    unfolding disjoint_resources_def plus_resources_def
    by (metis Int_Un_distrib Un_Int_eq(3) inf_commute resources.expand resources.inject)
qed

end

instantiation prod :: (right_cancel_seplogic,right_cancel_seplogic) right_cancel_seplogic
begin

instance
proof
  fix a b c :: \<open>'a \<times> 'b\<close>
  show \<open>a \<currency> c \<Longrightarrow> b \<currency> c \<Longrightarrow> (a + c = b + c) = (a = b)\<close>
    by (simp add: partial_right_cancel prod_eq_iff)
qed

end


subsection \<open> Syntax \<close>

datatype 'v iexpr =
  IEVar 'v
  | IELit nat
  | IEAdd \<open>'v iexpr\<close> \<open>'v iexpr\<close>

datatype 'v bexpr =
  IBEq \<open>'v iexpr\<close> \<open>'v iexpr\<close>
  | IBNeg \<open>'v bexpr\<close>

datatype 'v ram_comm =
  CSkip
  | CAssign 'v \<open>'v iexpr\<close>
  | CHeapR 'v \<open>'v iexpr\<close>
  | CHeapW \<open>'v iexpr\<close> \<open>'v iexpr\<close>
  | CHeapNew 'v
  | CHeapDel \<open>'v iexpr\<close>
  | CAssume \<open>'v bexpr\<close>

datatype 'v comm =
  CRam \<open>'v ram_comm\<close>
  | CSeq \<open>'v comm\<close> \<open>'v comm\<close> (infixr \<open>;;\<close> 84)
  | CNDet \<open>'v comm\<close> \<open>'v comm\<close> (infixr \<open>\<box>\<close> 86)
  | CLoop \<open>'v comm\<close> (\<open>(_)\<^sup>\<star>\<close> 88)
  | CAcquire nat
  | CRelease nat

type_synonym 'v prog = \<open>'v comm list\<close>


fun denot_iexpr :: \<open>'v iexpr \<Rightarrow> (('v \<rightharpoonup> nat) \<rightharpoonup> nat)\<close> (\<open>\<lbrakk>_\<rbrakk>\<^sub>I _\<close> [60,200] 60) where
  \<open>\<lbrakk> IEVar x \<rbrakk>\<^sub>I \<sigma> = \<sigma> x\<close>
| \<open>\<lbrakk> IELit k \<rbrakk>\<^sub>I \<sigma> = Some k\<close>
| \<open>\<lbrakk> IEAdd a b \<rbrakk>\<^sub>I \<sigma> = 
    (case (\<lbrakk>a\<rbrakk>\<^sub>I \<sigma>, \<lbrakk>b\<rbrakk>\<^sub>I \<sigma>) of
      (Some a, Some b) \<Rightarrow> Some (a + b)
    | _ \<Rightarrow> None
    )
  \<close>

fun ivars :: \<open>'v iexpr \<Rightarrow> 'v set\<close> where
  \<open>ivars (IEVar x) = {x}\<close>
| \<open>ivars (IELit k) = {}\<close>
| \<open>ivars (IEAdd a b) = ivars a \<union> ivars b\<close>

lemma iexpr_success_iff_goodvars:
  \<open>(\<exists>a. \<lbrakk>e\<rbrakk>\<^sub>I v = Some a) \<longleftrightarrow> ivars e \<subseteq> dom v\<close>
  by (induct e)
    (force split: option.splits)+

lemma goodvars_imp_iexpr_success:
  \<open>ivars e \<subseteq> dom v \<Longrightarrow> \<exists>a. \<lbrakk>e\<rbrakk>\<^sub>I v = Some a\<close>
  by (simp add: iexpr_success_iff_goodvars)

lemma iexpr_success_imp_goodvars:
  \<open>\<lbrakk>e\<rbrakk>\<^sub>I v = Some a \<Longrightarrow> ivars e \<subseteq> dom v\<close>
  by (metis iexpr_success_iff_goodvars)
  

lemma iexpr_failure_iff_missingvars:
  \<open>\<lbrakk>e\<rbrakk>\<^sub>I v = None \<longleftrightarrow> ivars e - dom v \<noteq> {}\<close>
  by (induct e)
    (force split: option.splits)+


fun denot_bexpr :: \<open>'v bexpr \<Rightarrow> (('v \<rightharpoonup> nat) \<rightharpoonup> bool)\<close> (\<open>\<lbrakk>_\<rbrakk>\<^sub>B _\<close> [60,200] 60) where
  \<open>\<lbrakk> IBEq a b \<rbrakk>\<^sub>B \<sigma> =
    (case (\<lbrakk>a\<rbrakk>\<^sub>I \<sigma>, \<lbrakk>b\<rbrakk>\<^sub>I \<sigma>) of
      (Some a, Some b) \<Rightarrow> Some (a = b)
    | _ \<Rightarrow> None
    )
  \<close>
| \<open>\<lbrakk> IBNeg b \<rbrakk>\<^sub>B \<sigma> = map_option HOL.Not (\<lbrakk> b \<rbrakk>\<^sub>B \<sigma>)\<close>

fun bvars :: \<open>'v bexpr \<Rightarrow> 'v set\<close> where
  \<open>bvars (IBEq a b) = ivars a \<union> ivars b\<close>
| \<open>bvars (IBNeg b) = bvars b\<close>

lemma bexpr_success_imp_goodvars:
  \<open>\<lbrakk>e\<rbrakk>\<^sub>B v = Some a \<Longrightarrow> bvars e \<subseteq> dom v\<close>
  by (induct e arbitrary: a)
    (force dest: iexpr_success_imp_goodvars split: option.splits)+


inductive opsem_ram_comm :: \<open>'v state \<Rightarrow> 'v ram_comm \<Rightarrow> 'v state option \<Rightarrow> bool\<close> (\<open>_, _ \<leadsto> _\<close> [60,60,60] 60) where
  \<open>s, CSkip \<leadsto> Some s\<close>

| \<open>s x \<noteq> None \<Longrightarrow> \<lbrakk>e\<rbrakk>\<^sub>I s = Some v \<Longrightarrow> (VarEnv s, h, r), CAssign x e \<leadsto> Some (VarEnv (s(x \<mapsto> v)), h, r)\<close>
| \<open>s x = None \<Longrightarrow> (VarEnv s, h, r), CAssign x e \<leadsto> None\<close>
| \<open>s x \<noteq> None \<Longrightarrow> \<lbrakk>e\<rbrakk>\<^sub>I s = None \<Longrightarrow> (VarEnv s, h, r), CAssign x e \<leadsto> None\<close>

| \<open>s x \<noteq> None \<Longrightarrow> \<lbrakk>ep\<rbrakk>\<^sub>I s = Some p \<Longrightarrow> the_heap h p = Some val \<Longrightarrow> (VarEnv s, h, r), CHeapR x ep \<leadsto> Some (VarEnv (s(x \<mapsto> val)), h, r)\<close>
| \<open>s x = None \<Longrightarrow> (VarEnv s, h, r), CHeapR x ep \<leadsto> None\<close>
| \<open>s x \<noteq> None \<Longrightarrow> \<lbrakk>ep\<rbrakk>\<^sub>I s = None   \<Longrightarrow> (VarEnv s, h, r), CHeapR x ep \<leadsto> None\<close>
| \<open>s x \<noteq> None \<Longrightarrow> \<lbrakk>ep\<rbrakk>\<^sub>I s = Some p \<Longrightarrow> the_heap h p = None \<Longrightarrow> (VarEnv s, h, r), CHeapR x ep \<leadsto> None\<close>

| \<open>\<lbrakk>ep\<rbrakk>\<^sub>I s = Some p \<Longrightarrow> h p \<noteq> None \<Longrightarrow> \<lbrakk>e\<rbrakk>\<^sub>I s = Some val \<Longrightarrow> (VarEnv s, Heap h, r), CHeapW ep e \<leadsto> Some (VarEnv s, Heap (h(p \<mapsto> val)), r)\<close>
| \<open>\<lbrakk>ep\<rbrakk>\<^sub>I s = Some p \<Longrightarrow> h p \<noteq> None \<Longrightarrow> \<lbrakk>e\<rbrakk>\<^sub>I s = None \<Longrightarrow> (VarEnv s, Heap h, r), CHeapW ep e \<leadsto> None\<close>
| \<open>\<lbrakk>ep\<rbrakk>\<^sub>I s = Some p \<Longrightarrow> h p = None \<Longrightarrow> (VarEnv s, Heap h, r), CHeapW ep e \<leadsto> None\<close>
| \<open>\<lbrakk>ep\<rbrakk>\<^sub>I s = None   \<Longrightarrow> (VarEnv s, h, r), CHeapW ep e \<leadsto> None\<close>

| \<open>s x \<noteq> None \<Longrightarrow> h p = None \<Longrightarrow> (VarEnv s, Heap h, r), CHeapNew x \<leadsto> Some (VarEnv (s(x \<mapsto> p)), Heap (h(p \<mapsto> undefined)), r)\<close>
| \<open>s x = None \<Longrightarrow> (VarEnv s, Heap h, r), CHeapNew x \<leadsto> None\<close>
| \<open>s x \<noteq> None \<Longrightarrow> h p \<noteq> None \<Longrightarrow> (VarEnv s, Heap h, r), CHeapNew x \<leadsto> None\<close>

| \<open>\<lbrakk>e\<rbrakk>\<^sub>I s = Some p \<Longrightarrow> h p \<noteq> None \<Longrightarrow> (VarEnv s, Heap h, r), CHeapDel e \<leadsto> Some (VarEnv s, Heap (h(p := None)), r)\<close>
| \<open>\<lbrakk>e\<rbrakk>\<^sub>I s = Some p \<Longrightarrow> h p = None \<Longrightarrow> (VarEnv s, Heap h, r), CHeapDel e \<leadsto> None\<close>
| \<open>\<lbrakk>e\<rbrakk>\<^sub>I s = None \<Longrightarrow> (VarEnv s, Heap h, r), CHeapDel e \<leadsto> None\<close>

| \<open>\<lbrakk>b\<rbrakk>\<^sub>B s = Some True \<Longrightarrow> (VarEnv s, h, r), CAssume b \<leadsto> Some (VarEnv s, h, r)\<close>

inductive_cases opsem_ram_comm_CSkipE[elim!]: \<open>s, CSkip \<leadsto> s'\<close>
inductive_cases opsem_ram_comm_CAssignE[elim!]: \<open>s, CAssign x e \<leadsto> s'\<close>
inductive_cases opsem_ram_comm_CHeapRE[elim]: \<open>s, CHeapR x e \<leadsto> s'\<close>
inductive_cases opsem_ram_comm_CHeapWE[elim!]: \<open>s, CHeapW ep e \<leadsto> s'\<close>
inductive_cases opsem_ram_comm_CHeapNewE[elim]: \<open>s, CHeapNew x \<leadsto> s'\<close>
inductive_cases opsem_ram_comm_CHeapDelE[elim]: \<open>s, CHeapDel e \<leadsto> s'\<close>
inductive_cases opsem_ram_comm_CAssumeE[elim!]: \<open>s, CAssume b \<leadsto> s'\<close>

lemma opsem_ram_comm_simps:
  \<open>s, CSkip \<leadsto> os' \<longleftrightarrow> os' = Some s\<close>
  \<open>s, CAssign x e \<leadsto> os' \<longleftrightarrow>
    (\<exists>v h r vx. s = (VarEnv v, h, r) \<and>
      (if v x = None
      then os' = None
      else case \<lbrakk>e\<rbrakk>\<^sub>I v of
        None \<Rightarrow> os' = None
      | Some vx \<Rightarrow> os' = Some (VarEnv (v(x \<mapsto> vx)), h, r)))\<close> (is ?CAssign)
  \<open>s, CHeapR x ep \<leadsto> os' \<longleftrightarrow>
    (\<exists>v h r. s = (VarEnv v, h, r) \<and>
    (if v x = None
    then os' = None
    else case \<lbrakk>ep\<rbrakk>\<^sub>I v of
      Some p \<Rightarrow> (case the_heap h p of
        Some val \<Rightarrow> os' = Some (VarEnv (v(x \<mapsto> val)), h, r)
      | None \<Rightarrow> os' = None)
    | None \<Rightarrow> os' = None))\<close> (is ?CHeapR)
  \<open>s, CHeapW ep e \<leadsto> os' \<longleftrightarrow>
    (\<exists>v h r. s = (VarEnv v, Heap h, r) \<and>
    (case \<lbrakk>ep\<rbrakk>\<^sub>I v of
      Some p \<Rightarrow>
        if h p = None
        then os' = None
        else (case  \<lbrakk>e\<rbrakk>\<^sub>I v of
            Some val \<Rightarrow> os' = Some (VarEnv v, Heap (h(p \<mapsto> val)), r)
          | None \<Rightarrow> os' = None)
    | None \<Rightarrow> os' = None))\<close> (is ?CHeapW)
  \<open>s, CHeapNew x \<leadsto> os' \<longleftrightarrow>
    (\<exists>v h r p. s = (VarEnv v, Heap h, r) \<and>
      (if v x = None
       then os' = None
       else (case h p of
          Some _ \<Rightarrow> os' = None
        | None \<Rightarrow> os' = Some (VarEnv (v(x \<mapsto> p)), Heap (h(p \<mapsto> undefined)), r))))\<close> (is ?CHeapNew)
  \<open>s, CHeapDel e \<leadsto> os' \<longleftrightarrow>
    (\<exists>v h r. s = (VarEnv v, Heap h, r) \<and>
    (case \<lbrakk>e\<rbrakk>\<^sub>I v of
      Some p \<Rightarrow> (case h p of
          Some _ \<Rightarrow> os' = Some (VarEnv v, Heap (h(p := None)), r)
        | None \<Rightarrow> os' = None
        )
    | None \<Rightarrow> os' = None))\<close>
  \<open>s, CAssume b \<leadsto> os' \<longleftrightarrow>
    (\<exists>v h r. s = (VarEnv v, h, r) \<and> \<lbrakk>b\<rbrakk>\<^sub>B v = Some True \<and> os' = Some (VarEnv v, h, r))\<close> (is ?CAssume)
proof -
  show \<open>s, CSkip \<leadsto> os' = (os' = Some s)\<close>
    by (simp add: opsem_ram_comm.simps split: option.splits)
  show \<open>?CAssign\<close>
    by (simp add: opsem_ram_comm.simps split: option.splits, fastforce)
  show \<open>?CHeapR\<close>
    apply (simp add: opsem_ram_comm.simps option.case_eq_if)
    apply (rule_tac iffI)
     apply (safe; force)
    apply (safe; fastforce)
    done
  show \<open>?CHeapW\<close>
    apply (simp add: opsem_ram_comm.simps split: option.splits)
    apply (fastforce simp add: the_heap_eq_iff[symmetric])
    done
  show \<open>?CHeapNew\<close>
    by (force simp add: opsem_ram_comm.simps split: option.splits)
  show \<open>s, CHeapDel e \<leadsto> os' =
    (\<exists>v h r.
        s = (VarEnv v, Heap h, r) \<and>
        (case \<lbrakk>e\<rbrakk>\<^sub>I v of None \<Rightarrow> os' = None
         | Some p \<Rightarrow>
            (case h p of None \<Rightarrow> os' = None
            | Some x \<Rightarrow> os' = Some (VarEnv v, Heap (h(p := None)), r))))\<close>
    apply (clarsimp simp add: opsem_ram_comm.simps split: option.splits)
    apply (case_tac s, rename_tac v h r, case_tac v, case_tac h, case_tac r)
    apply clarsimp
    apply (rule iffI)
     apply (metis (no_types, hide_lams) not_None_eq option.inject)
    apply (metis not_Some_eq)
    done
  show \<open>?CAssume\<close>
    by (force simp add: opsem_ram_comm.simps split: option.splits)
qed


fun rc_read_vars :: \<open>'v ram_comm \<Rightarrow> 'v set\<close> where
  \<open>rc_read_vars CSkip = {}\<close>
| \<open>rc_read_vars (CAssign x e) = ivars e\<close>
| \<open>rc_read_vars (CHeapR x e) = ivars e\<close>
| \<open>rc_read_vars (CHeapW ex ev) = ivars ex \<union> ivars ev\<close>
| \<open>rc_read_vars (CHeapNew x) = {}\<close>
| \<open>rc_read_vars (CHeapDel ex) = ivars ex\<close>
| \<open>rc_read_vars (CAssume bv) = bvars bv\<close>

fun rc_write_vars :: \<open>'v ram_comm \<Rightarrow> 'v set\<close> where
  \<open>rc_write_vars CSkip = {}\<close>
| \<open>rc_write_vars (CAssign x e) = {x}\<close>
| \<open>rc_write_vars (CHeapR x e) = {x}\<close>
| \<open>rc_write_vars (CHeapW _ _) = {}\<close>
| \<open>rc_write_vars (CHeapNew x) = {x}\<close>
| \<open>rc_write_vars (CHeapDel _) = {}\<close>
| \<open>rc_write_vars (CAssume _) = {}\<close>

fun rc_read_hvars :: \<open>'v varenv \<Rightarrow> 'v ram_comm \<Rightarrow> nat set\<close> where
  \<open>rc_read_hvars _ CSkip = {}\<close>
| \<open>rc_read_hvars _ (CAssign x e) = {}\<close>
| \<open>rc_read_hvars v (CHeapR x ep) = (case \<lbrakk>ep\<rbrakk>\<^sub>I (the_varenv v) of Some p \<Rightarrow> {p} | None \<Rightarrow> {})\<close>
| \<open>rc_read_hvars _ (CHeapW ep ev) = {}\<close>
| \<open>rc_read_hvars _ (CHeapNew x) = {}\<close>
| \<open>rc_read_hvars _ (CHeapDel ep) = {}\<close>
| \<open>rc_read_hvars _ (CAssume _) = {}\<close>

fun rc_write_hvars :: \<open>'v varenv \<Rightarrow> 'v ram_comm \<Rightarrow> nat set\<close> where
  \<open>rc_write_hvars _ CSkip = {}\<close>
| \<open>rc_write_hvars _ (CAssign x e) = {}\<close>
| \<open>rc_write_hvars _ (CHeapR x e) = {}\<close>
| \<open>rc_write_hvars v (CHeapW ep ev) = (case \<lbrakk>ep\<rbrakk>\<^sub>I (the_varenv v) of Some p \<Rightarrow> {p} | None \<Rightarrow> {})\<close>
| \<open>rc_write_hvars _ (CHeapNew x) = {}\<close>
| \<open>rc_write_hvars v (CHeapDel ep) = (case \<lbrakk>ep\<rbrakk>\<^sub>I (the_varenv v) of Some p \<Rightarrow> {p} | None \<Rightarrow> {})\<close>
| \<open>rc_write_hvars _ (CAssume _) = {}\<close>


fun c_read_vars :: \<open>'v comm \<Rightarrow> 'v set\<close> where
  \<open>c_read_vars (CRam rc) = rc_read_vars rc\<close>
| \<open>c_read_vars (CSeq c0 c1) = c_read_vars c0 \<union> c_read_vars c1\<close>
| \<open>c_read_vars (CNDet c0 c1) = c_read_vars c0 \<union> c_read_vars c1\<close>
| \<open>c_read_vars (CLoop c) = c_read_vars c\<close>
| \<open>c_read_vars (CAcquire k) = {}\<close>
| \<open>c_read_vars (CRelease k) = {}\<close>

fun c_write_vars :: \<open>'v comm \<Rightarrow> 'v set\<close> where
  \<open>c_write_vars (CRam rc) = rc_write_vars rc\<close>
| \<open>c_write_vars (CSeq c0 c1) = c_write_vars c0 \<union> c_write_vars c1\<close>
| \<open>c_write_vars (CNDet c0 c1) = c_write_vars c0 \<union> c_write_vars c1\<close>
| \<open>c_write_vars (CLoop c) = c_write_vars c\<close>
| \<open>c_write_vars (CAcquire k) = {}\<close>
| \<open>c_write_vars (CRelease k) = {}\<close>


fun c_read_hvars :: \<open>'v varenv \<Rightarrow> 'v comm \<Rightarrow> nat set\<close> where
  \<open>c_read_hvars v (CRam rc) = rc_read_hvars v rc\<close>
| \<open>c_read_hvars v (CSeq c0 c1) = c_read_hvars v c0 \<union> c_read_hvars v c1\<close>
| \<open>c_read_hvars v (CNDet c0 c1) = c_read_hvars v c0 \<union> c_read_hvars v c1\<close>
| \<open>c_read_hvars v (CLoop c) = c_read_hvars v c\<close>
| \<open>c_read_hvars _ (CAcquire k) = {}\<close>
| \<open>c_read_hvars _ (CRelease k) = {}\<close>

fun c_write_hvars :: \<open>'v varenv \<Rightarrow> 'v comm \<Rightarrow> nat set\<close> where
  \<open>c_write_hvars v (CRam rc) = rc_write_hvars v rc\<close>
| \<open>c_write_hvars v (CSeq c0 c1) = c_write_hvars v c0 \<union> c_write_hvars v c1\<close>
| \<open>c_write_hvars v (CNDet c0 c1) = c_write_hvars v c0 \<union> c_write_hvars v c1\<close>
| \<open>c_write_hvars v (CLoop c) = c_write_hvars v c\<close>
| \<open>c_write_hvars _ (CAcquire k) = {}\<close>
| \<open>c_write_hvars _ (CRelease k) = {}\<close>


lemma opsem_ram_comm_mostly_deterministic:
  \<open>s, c \<leadsto> s0 \<Longrightarrow> s, c \<leadsto> s1 \<Longrightarrow> \<forall>x. c \<noteq> CHeapNew x \<Longrightarrow> s0 = s1\<close>
  by (induct arbitrary: s1 rule: opsem_ram_comm.inducts) fastforce+

lemma opsem_ram_comm_success_mono:
  \<open>s, c \<leadsto> os' \<Longrightarrow>
  P \<le> Q \<Longrightarrow>
  P s \<Longrightarrow>
  \<exists>s. Q s \<and> s, c \<leadsto> os'\<close>
  by (induct rule: opsem_ram_comm.inducts)
    (fastforce simp add: le_fun_def intro: opsem_ram_comm.intros)+

lemma opsem_ram_comm_same_resources:
  \<open>s, c \<leadsto> os' \<Longrightarrow> os' = Some s' \<Longrightarrow> snd (snd s) = snd (snd s')\<close>
  by (induct arbitrary: s' rule: opsem_ram_comm.inducts) force+

lemma opsem_ram_comm_same_dom_varenv:
  \<open>s, c \<leadsto> os' \<Longrightarrow> os' = Some s' \<Longrightarrow> dom (the_varenv (fst s)) = dom (the_varenv (fst s'))\<close>
  by (induct arbitrary: s' rule: opsem_ram_comm.inducts) force+


section \<open>ram_comm forwards predicate transformer\<close>

definition ram_comm_forward :: \<open>'v ram_comm \<Rightarrow> ('v state \<Rightarrow> bool) \<Rightarrow> ('v state \<Rightarrow> bool)\<close> where
  \<open>ram_comm_forward c P \<equiv> \<lambda>s'. \<exists>s. P s \<and> (s, c \<leadsto> Some s')\<close>

lemma ram_comm_step_iff_forward:
  \<open>(s, c \<leadsto> Some s') \<longleftrightarrow> (=) s' \<le> ram_comm_forward c ((=) s)\<close>
  by (simp add: ram_comm_forward_def le_fun_def prod_eq_decompose)

lemma ram_comm_forward_simps:
  \<open>ram_comm_forward CSkip P = P\<close>
  \<open>ram_comm_forward (CAssign x e0) P =
    (\<lambda>(v, h, r). \<exists>vinit ex.
      P (vinit, h, r) \<and>
      the_varenv vinit x \<noteq> None \<and>
      \<lbrakk>e0\<rbrakk>\<^sub>I (the_varenv vinit) = Some ex \<and>
      v = VarEnv ((the_varenv vinit)(x \<mapsto> ex)))\<close> (is ?CAssign)
  \<open>ram_comm_forward (CHeapR x ep) P =
    (\<lambda>(v, h, r). \<exists>v' p val.
      P (v', h, r) \<and>
      the_varenv v' x \<noteq> None \<and>
      \<lbrakk>ep\<rbrakk>\<^sub>I (the_varenv v') = Some p \<and>
      the_heap h p = Some val \<and>
      v = VarEnv ((the_varenv v')(x \<mapsto> val))
    )\<close> (is ?CHeapR)
  \<open>ram_comm_forward (CHeapW ep e) P =
    (\<lambda>(v, h, r). \<exists>h' p ex val.
      P (v, h', r) \<and>
      the_heap h' p \<noteq> None \<and>
      \<lbrakk>ep\<rbrakk>\<^sub>I (the_varenv v) = Some p \<and>
      \<lbrakk>e\<rbrakk>\<^sub>I (the_varenv v) = Some val \<and>
      h = Heap ((the_heap h')(p \<mapsto> val))
    )\<close> (is ?CHeapW)
  \<open>ram_comm_forward (CHeapNew x) P =
    (\<lambda>(v', h', r). \<exists>v h p.
      P (v, h, r) \<and>
      the_varenv v x \<noteq> None \<and> 
      the_heap h p = None \<and>
      v' = VarEnv ((the_varenv v)(x \<mapsto> p)) \<and>
      h' = Heap ((the_heap h)(p \<mapsto> undefined))
    )\<close> (is ?CHeapNew)
  \<open>ram_comm_forward (CHeapDel e) P =
    (\<lambda>(v, h', r).
      \<exists>h p.
        P (v, h, r) \<and>
        \<lbrakk>e\<rbrakk>\<^sub>I the_varenv v = Some p \<and>
        the_heap h p \<noteq> None \<and>
        h' = Heap ((the_heap h)(p := None)))\<close>
  \<open>ram_comm_forward (CAssume be) P = (\<lambda>(s, h, r). P (s, h, r) \<and> (\<lbrakk> be \<rbrakk>\<^sub>B (the_varenv s) = Some True))\<close>
proof -
  show ?CAssign
    apply (intro ext)
    apply (clarsimp simp add: ram_comm_forward_def)
    apply (subst opsem_ram_comm_simps)
    apply (force split: option.splits)
    done
  show ?CHeapNew
    apply (intro ext)
    apply (clarsimp simp add: ram_comm_forward_def)
    apply (subst opsem_ram_comm_simps)
    apply (force split: option.splits)
    done
  show ?CHeapR
    apply (intro ext)
    apply (clarsimp simp add: ram_comm_forward_def)
    apply (subst opsem_ram_comm_simps)
    apply (simp split: option.splits, fastforce)
    done
  show ?CHeapW
    apply (intro ext)
    apply (clarsimp simp add: ram_comm_forward_def)
    apply (subst opsem_ram_comm_simps)
    apply (force split: option.splits)
    done

  {
    fix v' h' r'
    have \<open>
      (\<exists>v h r.
        P (v, h, r) \<and>
        (\<exists>vm. v = VarEnv vm \<and>
          (\<exists>y. \<lbrakk>e\<rbrakk>\<^sub>I vm = Some y) \<and>
          (\<exists>hm. \<forall>x2. (hm x2 = None \<longrightarrow> \<lbrakk>e\<rbrakk>\<^sub>I vm \<noteq> Some x2) \<and>
          ((\<exists>x2a. hm x2 = Some x2a) \<longrightarrow>
            \<lbrakk>e\<rbrakk>\<^sub>I vm = Some x2 \<longrightarrow>
            h = Heap hm \<and> v' = VarEnv vm \<and> h' = Heap (hm(x2 := None)) \<and> r' = r)))) \<longleftrightarrow>
      (\<exists>vm hm p.
        P (VarEnv vm, Heap hm, r') \<and>
        \<lbrakk>e\<rbrakk>\<^sub>I vm = Some p \<and>
          (\<forall>p'. \<lbrakk>e\<rbrakk>\<^sub>I vm = Some p' \<longrightarrow> hm p' \<noteq> None) \<and>
          (\<forall>p'. \<lbrakk>e\<rbrakk>\<^sub>I vm = Some p' \<longrightarrow>
            (\<forall>a. hm p' = Some a \<longrightarrow> v' = VarEnv vm \<and> h' = Heap (hm(p' := None)))))
    \<close> (is \<open>?lhs = _\<close>)
      by blast
    also have \<open>... \<longleftrightarrow>
      (\<exists>vm hm p a.
        P (VarEnv vm, Heap hm, r') \<and>
        \<lbrakk>e\<rbrakk>\<^sub>I vm = Some p \<and>
        hm p = Some a \<and>
        v' = VarEnv vm \<and> h' = Heap (hm(p := None)))
    \<close> (is \<open>_ = ?rhs\<close>)
      by fastforce
    finally have \<open>?lhs = ?rhs\<close> .
  }
  note s0 = this

  show \<open>ram_comm_forward (CHeapDel e) P =
    (\<lambda>(v, h', r). \<exists>h p.
      P (v, h, r) \<and>
      \<lbrakk>e\<rbrakk>\<^sub>I the_varenv v = Some p \<and>
      the_heap h p \<noteq> None \<and>
      h' = Heap ((the_heap h)(p := None)))\<close>
    unfolding ram_comm_forward_def
    by (force simp add: s0 fun_eq_iff opsem_ram_comm_simps split: option.splits)
qed (force simp add: ram_comm_forward_def fun_eq_iff opsem_ram_comm_simps split: option.splits)+


subsection \<open>Healthiness Conditions\<close>

lemma ram_comm_forward_mono:
  \<open>mono (ram_comm_forward c)\<close>
  unfolding mono_def ram_comm_forward_def le_fun_def
  by (simp, metis)

lemma ram_comm_forward_conj:
  \<open>ram_comm_forward c (P \<^bold>\<and> Q) \<le> ram_comm_forward c P \<^bold>\<and> ram_comm_forward c Q\<close>
proof (induct c)
  case CHeapW then show ?case
    by (clarsimp split: prod.splits simp add: pred_conj_def ram_comm_forward_def, metis)
qed (force split: prod.splits simp add: ram_comm_forward_simps pred_conj_def)+

lemma ram_comm_forward_disj:
  \<open>ram_comm_forward c (P \<^bold>\<or> Q) = ram_comm_forward c P \<^bold>\<or> ram_comm_forward c Q\<close>
proof (induct c)
  case CHeapW then show ?case
    by (clarsimp intro!: ext split: prod.splits simp add: pred_disj_def ram_comm_forward_def, metis)
qed (force intro!: ext split: prod.splits simp add: ram_comm_forward_simps pred_disj_def)+

lemma ram_comm_forward_false:
  \<open>ram_comm_forward c \<^bold>F = \<^bold>F\<close>
proof (induct c)
  case CHeapW then show ?case
    by (force intro!: ext split: prod.splits simp add: ram_comm_forward_def pred_false_def)
qed (force intro!: ext split: prod.splits simp add: ram_comm_forward_simps pred_false_def)+


section \<open> Frame \<close>

lemma iexpr_right_frame:
  \<open>dom va \<inter> dom vb = {} \<Longrightarrow> ivars e \<inter> dom vb = {} \<Longrightarrow> \<lbrakk>e\<rbrakk>\<^sub>I (va ++ vb) = \<lbrakk>e\<rbrakk>\<^sub>I va\<close>
  by (induct e)
    (force simp add: map_add_dom_app_simps Int_Un_distrib2 option.case_eq_if)+

lemma iexpr_left_frame:
  \<open>dom va \<inter> dom vb = {} \<Longrightarrow> ivars e \<inter> dom vb = {}  \<Longrightarrow> \<lbrakk>e\<rbrakk>\<^sub>I (vb ++ va) = \<lbrakk>e\<rbrakk>\<^sub>I va\<close>
  by (metis iexpr_right_frame map_add_comm)

lemma iexpr_right_frame_goodvars:
  \<open>dom va \<inter> dom vb = {} \<Longrightarrow> ivars e \<subseteq> dom va \<Longrightarrow> \<lbrakk>e\<rbrakk>\<^sub>I (va ++ vb) = \<lbrakk>e\<rbrakk>\<^sub>I va\<close>
  by (meson iexpr_right_frame disjoint_eq_subset_Compl subset_trans)

lemma iexpr_right_frame_goodeval:
  \<open>dom va \<inter> dom vb = {} \<Longrightarrow> \<lbrakk>e\<rbrakk>\<^sub>I va = Some x \<Longrightarrow> \<lbrakk>e\<rbrakk>\<^sub>I (va ++ vb) = \<lbrakk>e\<rbrakk>\<^sub>I va\<close>
  by (simp add: iexpr_right_frame_goodvars iexpr_success_imp_goodvars)

(* n.b. this is a dangerous simp rule, because the rhs shape unifies with the lhs shape.
 * I recommend using this with 'only'.
 *)
lemma iexpr_novars_iff:
  \<open>ivars e \<inter> dom v = {} \<Longrightarrow> \<lbrakk>e\<rbrakk>\<^sub>I v = x \<longleftrightarrow> \<lbrakk>e\<rbrakk>\<^sub>I Map.empty = x\<close>
  by (metis dom_empty empty_map_add iexpr_left_frame inf_bot_left map_add_comm)

lemma iexpr_some_imp_none_or_all:
  \<open>dom v0 \<inter> dom v1 = {} \<Longrightarrow> \<lbrakk>e\<rbrakk>\<^sub>I v0 = Some y \<Longrightarrow> \<lbrakk>e\<rbrakk>\<^sub>I v1 = None \<or> (\<forall>v. \<lbrakk>e\<rbrakk>\<^sub>I v \<noteq> None)\<close>
  by (force dest: iexpr_success_imp_goodvars
      simp add: iexpr_failure_iff_missingvars disjoint_iff subset_iff)


lemma bexpr_right_frame:
  \<open>dom va \<inter> dom vb = {} \<Longrightarrow> bvars e \<inter> dom vb = {} \<Longrightarrow> \<lbrakk>e\<rbrakk>\<^sub>B (va ++ vb) = \<lbrakk>e\<rbrakk>\<^sub>B va\<close>
  by (induct e)
   (force simp add: iexpr_right_frame map_add_dom_app_simps Int_Un_distrib2 option.case_eq_if)+

lemma bexpr_right_frame_goodeval:
  \<open>dom va \<inter> dom vb = {} \<Longrightarrow> \<lbrakk>e\<rbrakk>\<^sub>B va = Some x \<Longrightarrow> \<lbrakk>e\<rbrakk>\<^sub>B (va ++ vb) = \<lbrakk>e\<rbrakk>\<^sub>B va\<close>
  by (meson bexpr_right_frame bexpr_success_imp_goodvars disjoint_eq_subset_Compl subset_trans)

lemma bexpr_left_frame:
  \<open>dom va \<inter> dom vb = {} \<Longrightarrow> bvars e \<inter> dom vb = {} \<Longrightarrow> \<lbrakk>e\<rbrakk>\<^sub>B (vb ++ va) = \<lbrakk>e\<rbrakk>\<^sub>B va\<close>
  by (metis bexpr_right_frame map_add_comm)


lemma map_add_fun_upd_left:
  \<open>m \<notin> dom e2 \<Longrightarrow> e1(m := u) ++ e2 = (e1 ++ e2)(m := u)\<close>
  by (force simp add: map_add_def option.case_eq_if map_add_dom_app_simps)

lemma map_add_fun_upd_left_None:
  \<open>e2 m = None \<Longrightarrow> e1(m := u) ++ e2 = (e1 ++ e2)(m := u)\<close>
  by (simp add: domIff map_add_fun_upd_left)


lemma the_varenv_plus_lookup:
  \<open>the_varenv (a + b) x = (the_varenv a ++ the_varenv b) x\<close>
  by (simp add: plus_varenv_def)

lemma the_heap_plus_lookup:
  \<open>the_heap (a + b) x = (the_heap a ++ the_heap b) x\<close>
  by (simp add: plus_heap_def)

lemma the_varenv_add_app_simps:
  \<open>the_varenv b x = Some z \<Longrightarrow> the_varenv (a + b) x = Some z\<close>
  \<open>the_varenv b x = Some z \<Longrightarrow> a \<currency> b \<Longrightarrow> the_varenv (b + a) x = Some z\<close>
  \<open>the_varenv b x = None \<Longrightarrow> the_varenv (a + b) x = the_varenv a x\<close>
  \<open>the_varenv a x = None \<Longrightarrow> the_varenv (a + b) x = the_varenv b x\<close>
     by (simp add: domIff plus_varenv_def disjoint_varenv_def map_add_comm inf_commute
      map_add_dom_app_simps)+

lemma the_heap_add_app_simps:
  \<open>the_heap b x = Some z \<Longrightarrow> the_heap (a + b) x = Some z\<close>
  \<open>the_heap b x = Some z \<Longrightarrow> a \<currency> b \<Longrightarrow> the_heap (b + a) x = Some z\<close>
  \<open>the_heap b x = None \<Longrightarrow> the_heap (a + b) x = the_heap a x\<close>
  \<open>the_heap a x = None \<Longrightarrow> the_heap (a + b) x = the_heap b x\<close>
     by (simp add: domIff plus_heap_def disjoint_heap_def map_add_comm inf_commute
      map_add_dom_app_simps)+

lemma ex_eqVarEnv_invert:
  \<open>(\<exists>v0. v = VarEnv v0 \<and> P v0) \<longleftrightarrow> P (the_varenv v)\<close>
  by force

lemma ex_eqHeap_invert:
  \<open>(\<exists>h1. h = Heap h1 \<and> P h1) \<longleftrightarrow> P (the_heap h)\<close>
  by force

lemma plus_and_disjoint_nice_triple_split_ex:
  \<open>(\<exists>b. a = b + c \<and> b \<currency> c) \<longleftrightarrow>
    (case a of (a0,a1,a2) \<Rightarrow>
      (case c of (c0,c1,c2) \<Rightarrow>
        (\<exists>b0. a0 = b0 + c0 \<and> b0 \<currency> c0) \<and>
        (\<exists>b1. a1 = b1 + c1 \<and> b1 \<currency> c1) \<and>
        (\<exists>b2. a2 = b2 + c2 \<and> b2 \<currency> c2)))\<close>
  by force

lemma not_UNIV_iff_some_elem_notin:
  \<open>A \<noteq> UNIV \<longleftrightarrow> (\<exists>a. a \<notin> A)\<close>
  by blast

lemma disjoint_maps_asome_imp_bnone:
  \<open>e1 x = Some a \<Longrightarrow> dom e1 \<inter> dom e2 = {} \<Longrightarrow> e2 x = None\<close>
  by blast

lemma map_add_right_disjoint_upd_left:
  \<open>e1 m = Some a \<Longrightarrow> dom e1 \<inter> dom e2 = {} \<Longrightarrow> e1(m \<mapsto> u1) ++ e2 = (e1 ++ e2)(m \<mapsto> u1)\<close>
  by (simp add: disjoint_iff domI map_add_upd_left)

lemmas disjoint_the_varenv_asome_imp_bnone =
  disjoint_maps_asome_imp_bnone[where ?e1.0=\<open>the_varenv _\<close> and ?e2.0=\<open>the_varenv _\<close>]

lemma map_upd_eq: \<open>a(b \<mapsto> c1) = a(b \<mapsto> c2) \<longleftrightarrow> c1 = c2\<close>
  by (meson map_upd_eqD1)


lemma ram_comm_step_extend:
  assumes
    \<open>sa, c \<leadsto> Some sb\<close>
    \<open>sa \<currency> sc\<close>
    \<open>\<And>p. c \<noteq> CHeapNew p\<close>
  shows
    \<open>sa + sc, c \<leadsto> Some (sb + sc) \<and> sb \<currency> sc\<close>
  using assms
  apply -
  apply (cases sa, cases sb, cases sc, clarsimp simp del: ex_simps)
  apply (rename_tac va ha ra vb hb rb vc hc rc)
  apply (cases c)
        apply (force intro: opsem_ram_comm.intros)

       apply clarsimp
       apply (subst (asm) opsem_ram_comm_simps, subst opsem_ram_comm_simps)
       apply (clarsimp simp add: option.case_eq_if verit_ite_simplify(11) cong: if_cong)
        apply (force simp add: iexpr_right_frame_goodeval disjoint_varenv_def plus_varenv_def
      domIff map_add_Some_iff domI map_add_upd_left disjoint_iff)

      apply (clarsimp simp add: opsem_ram_comm_simps option.case_eq_if verit_ite_simplify(11)
      cong: if_cong)
       apply (force simp add: map_add_fun_upd_left iexpr_right_frame_goodeval
      disjoint_heap_def plus_varenv_def plus_heap_def disjoint_varenv_def
      disjoint_iff domIff map_add_dom_app_simps(3) domI)

     apply (clarsimp simp add: opsem_ram_comm_simps option.case_eq_if verit_ite_simplify(11)
      cong: if_cong)
     apply (force simp add: disjoint_heap_def disjoint_varenv_def plus_heap_def plus_varenv_def
      iexpr_right_frame_goodeval  map_add_upd_left domIff disjoint_iff map_add_dom_app_simps(3))

    apply force

   apply (clarsimp simp add: opsem_ram_comm_simps option.case_eq_if verit_ite_simplify(10-11)
      cong: if_cong)
   apply (force simp add: disjoint_varenv_def plus_varenv_def disjoint_heap_def plus_heap_def
      iexpr_right_frame_goodeval map_add_fun_upd_left_None)

  apply (force simp add: opsem_ram_comm_simps option.case_eq_if verit_ite_simplify(10-11)
      plus_varenv_def disjoint_varenv_def bexpr_right_frame_goodeval cong: if_cong)

  done


lemma ram_comm_step_safety_mono:
  assumes
    \<open>sa, c \<leadsto> Some sb\<close>
    \<open>the_heap (fst (snd sc)) p = None\<close>
    \<open>the_heap (fst (snd sa)) p = None\<close>
    \<open>sa \<currency> sc\<close>
  shows \<open>\<exists>so. sa + sc, c \<leadsto> Some so\<close>
  using assms
  apply -
  apply (cases sa, cases sb, cases sc)
  apply (rename_tac va ha ra vb hb rb vc hc rc)
  apply (cases c)
        apply (simp add: opsem_ram_comm_simps)
       apply (meson ram_comm.distinct ram_comm_step_extend)
      apply (meson ram_comm.distinct ram_comm_step_extend)
     apply (meson ram_comm.distinct ram_comm_step_extend)
    apply (force simp add: opsem_ram_comm_simps verit_ite_simplify(1-12) option.case_eq_if
      ex_eqVarEnv_invert ex_eqHeap_invert plus_heap_def disjoint_iff disjoint_varenv_def domIff
      the_varenv_add_app_simps cong: if_cong)
   apply (meson ram_comm.distinct ram_comm_step_extend)
  apply (meson ram_comm.distinct ram_comm_step_extend)
  done


lemma ram_comm_step_shrink:
  assumes
    \<open>sa + sc, c \<leadsto> Some (sb + sc)\<close>
    \<open>sa \<currency> sc\<close>
    \<open>sb \<currency> sc\<close>
    \<open>rc_read_vars c \<inter> dom (the_varenv (fst sc)) = {}\<close>
    \<open>rc_write_vars c \<inter> dom (the_varenv (fst sc)) = {}\<close>
    \<open>rc_read_hvars (fst (sa + sc)) c \<inter> dom (the_heap (fst (snd sc))) = {}\<close>
    \<open>rc_write_hvars (fst (sa + sc)) c \<inter> dom (the_heap (fst (snd sc))) = {}\<close>
  shows \<open>sa, c \<leadsto> Some sb\<close>
  using assms
  apply -
  apply (cases sa, cases sb, cases sc, clarsimp simp del: ex_simps)
  apply (cases c)
        apply (clarsimp simp add: opsem_ram_comm_simps disjoint_symm partial_right_cancel)

       apply (simp, subst (asm) opsem_ram_comm_simps, subst opsem_ram_comm_simps)
       apply (simp add: if_distrib if_distribR verit_ite_simplify(1-12) option.case_eq_if
      opsem_ram_comm_simps ex_eqVarEnv_invert partial_right_cancel cong: if_cong)
       apply (force simp add: map_add_fun_upd_left_None[symmetric] insert_dom
      map_disjoint_dom_cancel_right map_add_Some_iff iexpr_right_frame
      plus_varenv_def disjoint_varenv_def the_varenv_add_app_simps the_varenv_eq_iff)

      apply (simp add: if_distrib if_distribR verit_ite_simplify(1-12) option.case_eq_if
      opsem_ram_comm_simps ex_eqVarEnv_invert cong: if_cong)
      apply (elim conjE exE, simp add: plus_varenv_def disjoint_varenv_def
      partial_right_cancel the_heap_plus_lookup iexpr_right_frame map_add_dom_app_simps
      map_disjoint_dom_cancel_right the_varenv_eq_iff[symmetric] map_add_upd_left[symmetric])

     apply (simp add: if_distrib if_distribR verit_ite_simplify(1-12) option.case_eq_if
      opsem_ram_comm_simps ex_eqVarEnv_invert ex_eqHeap_invert cong: if_cong)
     apply (force simp add: plus_varenv_def disjoint_varenv_def plus_heap_def disjoint_heap_def
      partial_right_cancel iexpr_right_frame map_disjoint_dom_cancel_right inf_sup_distrib2
      the_varenv_eq_iff[symmetric] the_heap_eq_iff[symmetric] map_add_upd_left[symmetric]
      the_varenv_inject)

    apply (simp add: if_distrib if_distribR verit_ite_simplify(1-12) option.case_eq_if
      opsem_ram_comm_simps ex_eqVarEnv_invert ex_eqHeap_invert cong: if_cong)
    apply (fastforce simp add: plus_varenv_def disjoint_varenv_def plus_heap_def disjoint_heap_def
      partial_right_cancel map_disjoint_dom_cancel_right domIff the_varenv_eq_iff[symmetric]
      the_heap_eq_iff[symmetric] map_add_upd_left[symmetric])

   apply (simp add: if_distrib if_distribR verit_ite_simplify(1-12) option.case_eq_if
      opsem_ram_comm_simps ex_eqVarEnv_invert ex_eqHeap_invert cong: if_cong)
   apply (fastforce simp add: plus_varenv_def disjoint_varenv_def plus_heap_def disjoint_heap_def
      partial_right_cancel iexpr_right_frame the_varenv_inject the_heap_eq_iff[symmetric]
      map_add_fun_upd_left[symmetric] domIff map_disjoint_dom_cancel_right Diff_Int_distrib2
      map_add_Some_iff)

  apply (simp add: if_distrib if_distribR verit_ite_simplify(1-12) option.case_eq_if
      opsem_ram_comm_simps ex_eqVarEnv_invert ex_eqHeap_invert cong: if_cong)
  apply (fastforce simp add: plus_varenv_def disjoint_varenv_def the_varenv_inject the_heap_inject
      partial_right_cancel map_disjoint_dom_cancel_right bexpr_right_frame )

  done

lemmas ram_comm_step_shrink2 =
  ram_comm_step_shrink[
    where sa=\<open>(va,ha,ra)\<close> and sb=\<open>(vb,hb,rb)\<close> and sc=\<open>(vc,hc,rc)\<close>
    for va ha ra vb hb rb vc hc rc, simplified]

lemma ram_comm_step_split_in_split_out:
  assumes
    \<open>sa + sc, c \<leadsto> Some so\<close>
    \<open>sa \<currency> sc\<close>
    \<open>rc_read_vars c \<inter> dom (the_varenv (fst sc)) = {}\<close>
    \<open>rc_write_vars c \<inter> dom (the_varenv (fst sc)) = {}\<close>
    \<open>rc_read_hvars (fst (sa + sc)) c \<inter> dom (the_heap (fst (snd sc))) = {}\<close>
    \<open>rc_write_hvars (fst (sa + sc)) c \<inter> dom (the_heap (fst (snd sc))) = {}\<close>
  shows
    \<open>\<exists>sb. so = sb + sc \<and> sb \<currency> sc\<close>
  using assms
  apply -
  apply (simp only: plus_and_disjoint_nice_triple_split_ex)
  apply (cases sa, cases sc, cases so, clarsimp)
  apply (rename_tac va ha ra vc hc rc vo ho ro)
  apply (cases c)
        apply (force simp add: opsem_ram_comm_simps)

       apply (simp, subst (asm) opsem_ram_comm_simps)
       apply (clarsimp simp add: verit_ite_simplify(1-12) option.case_eq_if ex_eqVarEnv_invert ex_eqHeap_invert
      domIff cong: if_cong)
       apply (rename_tac x e y0 y1)
       apply (rule conjI)
        apply (rule_tac x=\<open>VarEnv (_(x \<mapsto> _))\<close> in exI)
        apply (force simp add: plus_varenv_def disjoint_varenv_def map_add_fun_upd_left_None)
       apply force

      apply (clarsimp simp add: opsem_ram_comm_simps verit_ite_simplify(1-12) option.case_eq_if
      ex_eqVarEnv_invert ex_eqHeap_invert domIff cong: if_cong)
      apply (rename_tac x e y0 y1 y2)
      apply (rule conjI)
       apply (rule_tac x=\<open>VarEnv (_(x \<mapsto> _))\<close> in exI)
       apply (force simp add: plus_varenv_def disjoint_varenv_def map_add_fun_upd_left_None)
      apply force

     apply (clarsimp simp add: opsem_ram_comm_simps verit_ite_simplify(1-12) option.case_eq_if
      ex_eqVarEnv_invert ex_eqHeap_invert domIff cong: if_cong)
     apply (rename_tac x e yp y1 y2)
     apply (rule conjI, force)
     apply (rule conjI)
      apply (rule_tac x=\<open>Heap (_(yp \<mapsto> _))\<close> in exI)
      apply (force simp add: plus_heap_def disjoint_heap_def map_add_fun_upd_left_None)
     apply force

    apply (clarsimp simp add: opsem_ram_comm_simps verit_ite_simplify(1-12) option.case_eq_if
      ex_eqVarEnv_invert ex_eqHeap_invert domIff cong: if_cong)
    apply (rename_tac x y p)
    apply (rule conjI)
     apply (rule_tac x=\<open>VarEnv (_(x \<mapsto> _))\<close> in exI)
     apply (force simp add: plus_varenv_def disjoint_varenv_def map_add_fun_upd_left_None)
    apply (rule conjI)
     apply (rule_tac x=\<open>Heap (_(p \<mapsto> _))\<close> in exI)
     apply (force simp add: plus_heap_def disjoint_heap_def map_add_fun_upd_left_None)
    apply force

   apply (clarsimp simp add: opsem_ram_comm_simps verit_ite_simplify(1-12) option.case_eq_if
      ex_eqVarEnv_invert ex_eqHeap_invert domIff cong: if_cong)
   apply (rename_tac x y0 y1)
   apply (rule conjI, force)
   apply (rule conjI)
    apply (rule_tac x=\<open>Heap (_(y0 := _))\<close> in exI)
    apply (force simp add: plus_heap_def disjoint_heap_def map_add_fun_upd_left_None)
   apply force

  apply force

  done

lemmas ram_comm_step_split_in_split_out2 =
  ram_comm_step_split_in_split_out
    [where sa=\<open>(va,ha,ra)\<close> and sc=\<open>(vc,hc,rc)\<close> for va ha ra vc hc rc, simplified]


lemma ram_comm_step_shrinkD:
  assumes
    \<open>sa + sc, c \<leadsto> Some so\<close>
    \<open>sa \<currency> sc\<close>
    \<open>rc_read_vars c \<inter> dom (the_varenv (fst sc)) = {}\<close>
    \<open>rc_write_vars c \<inter> dom (the_varenv (fst sc)) = {}\<close>
    \<open>rc_read_hvars (fst sa + fst sc) c \<inter> dom (the_heap (fst (snd sc))) = {}\<close>
    \<open>rc_write_hvars (fst sa + fst sc) c \<inter> dom (the_heap (fst (snd sc))) = {}\<close>
  shows \<open>\<exists>sb. sa, c \<leadsto> Some sb \<and> so = sb + sc \<and> sb \<currency> sc\<close>
  using assms
  apply -
  apply clarsimp
  apply (frule ram_comm_step_split_in_split_out2, force, force, force, force, force)
  apply clarify
  apply (drule ram_comm_step_shrink2, force, force, force, force, force, force)
  apply force
  done

lemmas ram_comm_step_shrinkD2 =
  ram_comm_step_shrinkD[
    where sa=\<open>(va,ha,ra)\<close> and sc=\<open>(vc,hc,rc)\<close>
    for va ha ra vc hc rc, simplified]


lemma ram_comm_forward_frame_right:
  assumes
    \<open>\<And>s. P s \<Longrightarrow> rc_read_vars c \<inter> dom (the_varenv (fst s)) = {}\<close>
    \<open>\<And>s. P s \<Longrightarrow> rc_write_vars c \<inter> dom (the_varenv (fst s)) = {}\<close>
    \<open>\<And>sq sp. Q sq \<Longrightarrow> P sp \<Longrightarrow> sq \<currency> sp \<Longrightarrow> rc_read_hvars (fst sq + fst sp) c \<inter> dom (the_heap (fst (snd sp))) = {}\<close>
    \<open>\<And>sq sp. Q sq \<Longrightarrow> P sp \<Longrightarrow> sq \<currency> sp \<Longrightarrow> rc_write_hvars (fst sq + fst sp) c \<inter> dom (the_heap (fst (snd sp))) = {}\<close>
  shows
    \<open>ram_comm_forward c (Q \<^emph> P) \<le> ram_comm_forward c Q \<^emph> P\<close>
  using assms
  apply -
  apply (clarsimp simp add: ram_comm_forward_def le_fun_def sepconj_def)
  apply (drule ram_comm_step_shrinkD2, force, force, force, force, force)
  apply blast
  done

lemma ram_comm_forward_frame_left:
  assumes
    \<open>\<And>s. P s \<Longrightarrow> rc_read_vars c \<inter> dom (the_varenv (fst s)) = {}\<close>
    \<open>\<And>s. P s \<Longrightarrow> rc_write_vars c \<inter> dom (the_varenv (fst s)) = {}\<close>
    \<open>\<And>sq sp. Q sq \<Longrightarrow> P sp \<Longrightarrow> sp \<currency> sq \<Longrightarrow> rc_read_hvars (fst sp + fst sq) c \<inter> dom (the_heap (fst (snd sp))) = {}\<close>
    \<open>\<And>sq sp. Q sq \<Longrightarrow> P sp \<Longrightarrow> sp \<currency> sq \<Longrightarrow> rc_write_hvars (fst sp + fst sq) c \<inter> dom (the_heap (fst (snd sp))) = {}\<close>
  shows
    \<open>ram_comm_forward c (P \<^emph> Q) \<le> P \<^emph> ram_comm_forward c Q\<close>
  using assms
  apply (simp add: sepconj_comm[where P=P])
  apply (rule ram_comm_forward_frame_right[where P=P and Q=Q])
     apply (simp add: disjoint_symm partial_add_commute)+
  done


subsection \<open> mfault forward semantics \<close>

fun mfaultsem_ram_comm :: \<open>'v ram_comm \<Rightarrow> 'v state \<Rightarrow> ('v state \<Rightarrow> bool) mfault\<close> where
  \<open>mfaultsem_ram_comm CSkip s = Success ((=) s)\<close>
| \<open>mfaultsem_ram_comm (CAssign x e) s = (case s of
      (VarEnv v, h, r) \<Rightarrow>
        (if v x = None then Fault
        else case \<lbrakk>e\<rbrakk>\<^sub>I v of
          None \<Rightarrow> Fault
        | Some vx \<Rightarrow> Success ((=) (VarEnv (v(x \<mapsto> vx)), h, r))))\<close>
| \<open>mfaultsem_ram_comm (CHeapR x ep) s = (case s of
    (VarEnv v, h, r) \<Rightarrow>
      (if v x = None then Fault
      else case \<lbrakk>ep\<rbrakk>\<^sub>I v of
        None \<Rightarrow> Fault
      | Some p \<Rightarrow> (case the_heap h p of
          None \<Rightarrow> Fault
        | Some val \<Rightarrow> Success ((=) (VarEnv (v(x \<mapsto> val)), h, r)))))\<close>
| \<open>mfaultsem_ram_comm (CHeapW ep e) s = (case s of
    (VarEnv v, Heap h, r) \<Rightarrow>
      (case \<lbrakk>ep\<rbrakk>\<^sub>I v of
        None \<Rightarrow> Fault
      | Some p \<Rightarrow>
          if h p = None then Fault
          else (case \<lbrakk>e\<rbrakk>\<^sub>I v of
            None \<Rightarrow> Fault
            | Some val \<Rightarrow> Success ((=) (VarEnv v, Heap (h(p \<mapsto> val)), r)))))\<close>
| \<open>mfaultsem_ram_comm (CHeapNew x) s = (case s of
    (VarEnv v, Heap h, r) \<Rightarrow>
      (if v x = None then Fault
       else (if (\<exists>p. h p = None)
          then Success (\<lambda>s'. \<exists>p. h p = None \<and> s' = (VarEnv (v(x \<mapsto> p)), Heap (h(p \<mapsto> undefined)), r))
          else Fault)))\<close>
| \<open>mfaultsem_ram_comm (CHeapDel e) s = (case s of
    (VarEnv v, Heap h, r) \<Rightarrow>
      (case \<lbrakk>e\<rbrakk>\<^sub>I v of
        Some p \<Rightarrow> (case h p of
            Some _ \<Rightarrow> Success ((=) (VarEnv v, Heap (h(p := None)), r))
          | None \<Rightarrow> Fault
          )
      | None \<Rightarrow> Fault))\<close>
| \<open>mfaultsem_ram_comm (CAssume b) s = Success ((=) s \<^bold>\<and> (\<lambda>_. \<lbrakk>b\<rbrakk>\<^sub>B (the_varenv (fst s)) = Some True))\<close>






lemma mfaultsem_ram_comm_local:
  \<open>s0 \<currency> s1 \<Longrightarrow> mfaultsem_ram_comm c (s0 + s1) \<le> mfaultsem_ram_comm c s0 \<^emph>\<^sub>f Success ((=) s1)\<close>
  apply (cases s0, cases s1)
  apply (rename_tac v0 h0 r0 v1 h1 r1)
  apply (cases c)
        apply (force simp add: sepconj_mfault_def)

       apply (simp add: sepconj_mfault_def)

  sorry



section \<open>Operational Semantics\<close>

definition transition_labels :: \<open>('l \<times> 'a \<times> 'l) set \<Rightarrow> 'l set\<close> where
  \<open>transition_labels T \<equiv> fst ` T \<union> (snd \<circ> snd) ` T\<close>

lemma transition_labels_include_start:
  \<open>(a,c,b) \<in> T \<Longrightarrow> a \<in> transition_labels T\<close>
  by (force simp add: transition_labels_def)

lemma transition_labels_include_end:
  \<open>(a,c,b) \<in> T \<Longrightarrow> b \<in> transition_labels T\<close>
  by (force simp add: transition_labels_def)

lemmas transition_labels_include_startend =
  transition_labels_include_start
  transition_labels_include_end

lemma transition_labels_empty[simp]:
  \<open>transition_labels {} = {}\<close>
  by (force simp add: transition_labels_def)

lemma transition_labels_insert_eq[simp]:
  \<open>transition_labels (insert t T) = insert (fst t) (insert (snd (snd t)) (transition_labels T))\<close>
  by (force simp add: transition_labels_def)

lemma transition_labels_un_eq[simp]:
  \<open>transition_labels (T1 \<union> T2) = transition_labels T1 \<union> transition_labels T2\<close>
  by (force simp add: transition_labels_def)

lemma transition_labels_disjoint_then_transitions_disjoint:
  \<open>transition_labels T1 \<inter> transition_labels T2 = {} \<Longrightarrow> T1 \<inter> T2 = {}\<close>
  by (force simp add: transition_labels_def)


inductive cfg :: \<open>'v comm \<Rightarrow> ('l \<times> 'v comm \<times> 'l) set \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> bool\<close> where
  cfg_skip: \<open>s \<noteq> e \<Longrightarrow> cfg (CRam c) {(s, CRam c, e)} s e\<close>
| cfg_seq:
  \<open>\<lbrakk> cfg c1 T1 s1 e1
   ; cfg c2 T2 s2 e2
   ; transition_labels T1 \<inter> transition_labels T2 = {}
   ; T = insert (e1, CRam CSkip, s2) (T1 \<union> T2)
   \<rbrakk> \<Longrightarrow> cfg (c1 ;; c2) T s1 e2\<close>
| cfg_ndet:
  \<open>\<lbrakk> cfg c1 T1 s1 e1
   ; cfg c2 T2 s2 e2
   ; transition_labels T1 \<inter> transition_labels T2 = {}
   ; s \<notin> transition_labels T1
   ; s \<notin> transition_labels T2
   ; e \<notin> transition_labels T1
   ; e \<notin> transition_labels T2
   ; s \<noteq> e
   ; T = {(s, CRam CSkip, s1), (s, CRam CSkip, s2), (e1, CRam CSkip, e), (e2, CRam CSkip, e)} \<union> (T1 \<union> T2)
   \<rbrakk> \<Longrightarrow> cfg (c1 \<box> c2) T s e\<close>
| cfg_loop:
  \<open>\<lbrakk> cfg c T' s' e'
   ; s \<notin> transition_labels T'
   ; e \<notin> transition_labels T'
   ; s \<noteq> e
   ; (e', CRam CSkip, s') \<notin> T'
   ; T = {(e', CRam CSkip, s'), (s, CRam CSkip, s'), (e', CRam CSkip, e)} \<union> T'
   \<rbrakk> \<Longrightarrow> cfg (c\<^sup>\<star>) T s e\<close>

inductive_cases cfg_CRamE[elim!]: \<open>cfg (CRam c) T s e\<close>
inductive_cases cfg_CSeqE[elim!]: \<open>cfg (c1 ;; c2) T s e\<close>
inductive_cases cfg_CNDetE[elim!]: \<open>cfg (c1 \<box> c2) T s e\<close>
inductive_cases cfg_CLoopE[elim!]: \<open>cfg (c\<^sup>\<star>) T s e\<close>


lemma cfg_simps:
  \<open>cfg (CRam cr) T s e \<longleftrightarrow> T = {(s, CRam cr, e)} \<and> s \<noteq> e\<close>
  \<open>cfg (c1 ;; c2) T s e \<longleftrightarrow> (\<exists>T1 T2 e1 s2.
    cfg c1 T1 s e1 \<and>
    cfg c2 T2 s2 e \<and>
    transition_labels T1 \<inter> transition_labels T2 = {} \<and>
    T = insert (e1, CRam CSkip, s2) (T1 \<union> T2)
  )\<close>
  \<open>cfg (c1 \<box> c2) T s e \<longleftrightarrow> s \<noteq> e \<and> (\<exists>T1 T2 s1 s2 e1 e2.
    cfg c1 T1 s1 e1 \<and>
    cfg c2 T2 s2 e2 \<and>
    transition_labels T1 \<inter> transition_labels T2 = {} \<and>
    s \<notin> transition_labels T1 \<and>
    e \<notin> transition_labels T1 \<and>
    s \<notin> transition_labels T2 \<and>
    e \<notin> transition_labels T2 \<and>
    T = {(s, CRam CSkip, s1), (s, CRam CSkip, s2), (e1, CRam CSkip, e), (e2, CRam CSkip, e)} \<union> T1 \<union> T2
  )\<close>
  \<open>cfg (c\<^sup>\<star>) T s e \<longleftrightarrow> s \<noteq> e \<and> (\<exists>T' s' e'.
    cfg c T' s' e' \<and>
    s \<notin> transition_labels T' \<and>
    e \<notin> transition_labels T' \<and>
    (e', CRam CSkip, s') \<notin> T' \<and>
    T = {(e', CRam CSkip, s'), (s, CRam CSkip, s'), (e', CRam CSkip, e)} \<union> T'
  )\<close>
     apply (blast intro: cfg.intros)
    apply (blast intro: cfg.intros)

   apply (rule iffI)
    apply (erule cfg_CNDetE, simp, blast)
   apply (blast intro: cfg.intros)

   apply (blast intro: cfg.intros)
  done

lemma cfg_transition_labels_include_start:
  \<open>cfg c T s e \<Longrightarrow> s \<in> transition_labels T\<close>
  by (induct rule: cfg.inducts)
    (force simp add: transition_labels_def)+

lemma cfg_transition_labels_include_end:
  \<open>cfg c T s e \<Longrightarrow> e \<in> transition_labels T\<close>
  by (induct rule: cfg.inducts)
    (force simp add: transition_labels_def)+

lemmas cfg_transition_labels_include_startend =
  cfg_transition_labels_include_start
  cfg_transition_labels_include_end


lemma cfg_transition_labels_start_not_end:
  \<open>cfg c T s e \<Longrightarrow> s \<noteq> e\<close>
proof (induct rule: cfg.inducts)
  case (cfg_seq c1 T1 s1 e1 c2 T2 s2 e2 T)
  then show ?case
    by (meson cfg_transition_labels_include_startend disjoint_iff_not_equal)
qed blast+


definition
  \<open>cfg_iso \<equiv> \<lambda>(Ta,sa,ea) (Tb,sb,eb).
    \<exists>f.
      bij_betw (\<lambda>(la,c,lb). (f la, c, f lb)) Ta Tb \<and>
      bij_betw f (transition_labels Ta) (transition_labels Tb) \<and>
      f sa = sb \<and>
      f ea = eb
  \<close>

lemma cfg_same_label_bij:
  assumes
    \<open>cfg c Ta sa ea\<close>
    \<open>cfg c Tb sb eb\<close>
  shows
    \<open>cfg_iso (Ta,sa,ea) (Tb,sb,eb)\<close>
  unfolding cfg_iso_def
  using assms
proof (induct arbitrary: Tb sb eb)
  case (cfg_skip sa ea ca)
  then show ?case
    apply simp
    apply (rule_tac x=\<open>\<lambda>l. if l = ea then eb else sb\<close> in exI)
    apply (force simp add: bij_betw_def)
    done
next
  case (cfg_seq c1 T1a s1a e1a c2 T2a s2a e2a Ta Tb s1b e2b)

  obtain T1b T2b e1b s2b
    where cfg_b:
       \<open>cfg c1 T1b s1b e1b\<close>
       \<open>cfg c2 T2b s2b e2b\<close>
       \<open>transition_labels T1b \<inter> transition_labels T2b = {}\<close>
       \<open>Tb = insert (e1b, CRam CSkip, s2b) (T1b \<union> T2b)\<close>
    using cfg_seq.prems by blast

  obtain f1
    where iso1:
      \<open>bij_betw (\<lambda>a. case a of (la, c, lb) \<Rightarrow> (f1 la, c, f1 lb)) T1a T1b\<close>
      \<open>bij_betw f1 (transition_labels T1a) (transition_labels T1b)\<close>
      \<open>f1 s1a = s1b\<close>
      \<open>f1 e1a = e1b\<close>
    using cfg_b cfg_seq.hyps by blast

  obtain f2
    where iso2:
      \<open>bij_betw (\<lambda>a. case a of (la, c, lb) \<Rightarrow> (f2 la, c, f2 lb)) T2a T2b\<close>
      \<open>bij_betw f2 (transition_labels T2a) (transition_labels T2b)\<close>
      \<open>f2 s2a = s2b\<close>
      \<open>f2 e2a = e2b\<close>
    using cfg_b cfg_seq.hyps by blast

  show ?case
    using cfg_seq.hyps(1,3,5-) cfg_b iso1 iso2
    apply simp
    apply (rule_tac x=\<open>\<lambda>l. if l \<in> transition_labels T1a then f1 l else f2 l\<close> in exI)
    apply (intro conjI)
       apply (subst bij_betw_cong[
          where g=\<open>\<lambda>t.
            if t = (e1a, CRam CSkip, s2a)
            then (e1b, CRam CSkip, s2b)
            else if t \<in> T1a
            then case t of (la, c, lb) \<Rightarrow> (f1 la, c, f1 lb)
            else case t of (la, c, lb) \<Rightarrow> (f2 la, c, f2 lb)
          \<close>])
        apply clarsimp
        apply (rename_tac lx c ly)
        apply (case_tac \<open>lx \<in> transition_labels T1a\<close>; case_tac \<open>ly \<in> transition_labels T1a\<close>)
           apply (meson transition_labels_include_start cfg_transition_labels_include_start disjoint_iff)
          apply (meson disjoint_iff transition_labels_include_startend)
         apply (meson cfg_transition_labels_include_end transition_labels_include_startend disjoint_iff)
        apply (meson cfg_transition_labels_include_end transition_labels_include_end)

       apply clarsimp
       apply (rule bij_betw_disjoint_insert, rule bij_betw_singleton, force)
         apply (rule bij_betw_disjoint_Un, blast, blast)
          apply (metis transition_labels_disjoint_then_transitions_disjoint)
         apply (metis transition_labels_disjoint_then_transitions_disjoint)
        apply (metis cfg_transition_labels_include_startend transition_labels_include_startend
        Un_iff disjoint_iff)
       apply (metis cfg_transition_labels_include_startend transition_labels_include_startend
        Un_iff disjoint_iff)
      apply (intro bij_betw_insert_ignore, (intro bij_betw_disjoint_Un; blast))
         apply (simp add: cfg_transition_labels_include_start)
        apply (simp add: cfg_transition_labels_include_start)
       apply (simp add: cfg_transition_labels_include_end)
      apply (simp add: cfg_transition_labels_include_end)
     apply (simp add: cfg_transition_labels_include_start)
    apply (metis cfg_transition_labels_include_end disjoint_iff)
    done
next
  case (cfg_ndet c1 T1a s1a e1a c2 T2a s2a e2a sa ea Ta Tb sb eb)

  obtain T1b T2b s1b e1b s2b e2b
    where cfg_b:
      \<open>cfg c1 T1b s1b e1b\<close>
      \<open>cfg c2 T2b s2b e2b\<close>
      \<open>transition_labels T1b \<inter> transition_labels T2b = {}\<close>
      \<open>sb \<notin> transition_labels T1b\<close>
      \<open>sb \<notin> transition_labels T2b\<close>
      \<open>eb \<notin> transition_labels T1b\<close>
      \<open>eb \<notin> transition_labels T2b\<close>
      \<open>sb \<noteq> eb\<close>
      \<open>Tb = {(sb, CRam CSkip, s1b), (sb, CRam CSkip, s2b), (e1b, CRam CSkip, eb), (e2b, CRam CSkip, eb)} \<union>  (T1b \<union> T2b)\<close>
    using cfg_ndet.prems by blast

  obtain f1
    where iso1:
      \<open>bij_betw (\<lambda>a. case a of (la, c, lb) \<Rightarrow> (f1 la, c, f1 lb)) T1a T1b\<close>
      \<open>bij_betw f1 (transition_labels T1a) (transition_labels T1b)\<close>
      \<open>f1 s1a = s1b\<close>
      \<open>f1 e1a = e1b\<close>
    using cfg_b cfg_ndet.hyps by blast

  obtain f2
    where iso2:
      \<open>bij_betw (\<lambda>a. case a of (la, c, lb) \<Rightarrow> (f2 la, c, f2 lb)) T2a T2b\<close>
      \<open>bij_betw f2 (transition_labels T2a) (transition_labels T2b)\<close>
      \<open>f2 s2a = s2b\<close>
      \<open>f2 e2a = e2b\<close>
    using cfg_b cfg_ndet.hyps by blast

  have label_lemmas1:
    \<open>s1a \<noteq> ea\<close> \<open>s1a \<noteq> sa\<close>
    \<open>s2a \<noteq> ea\<close> \<open>s2a \<noteq> sa\<close>
    \<open>e1a \<noteq> sa\<close> \<open>e1a \<noteq> ea\<close>
    \<open>e2a \<noteq> sa\<close> \<open>e2a \<noteq> ea\<close>
    \<open>ea \<noteq> s1a\<close> \<open>sa \<noteq> s1a\<close>
    \<open>ea \<noteq> s2a\<close> \<open>sa \<noteq> s2a\<close>
    \<open>sa \<noteq> e1a\<close> \<open>ea \<noteq> e1a\<close>
    \<open>sa \<noteq> e2a\<close> \<open>ea \<noteq> e2a\<close>

    \<open>s1a \<noteq> s2a\<close>
    \<open>e1a \<noteq> e2a\<close>
    \<open>e2a \<noteq> s1a\<close>
    using cfg_ndet
    by (force simp add: disjoint_iff dest: cfg_transition_labels_include_startend)+

  have label_lemmas2:
    \<open>s2a \<notin> transition_labels T1a\<close>
    \<open>e2a \<notin> transition_labels T1a\<close>
    \<open>s1a \<notin> transition_labels T2a\<close>
    \<open>e1a \<notin> transition_labels T2a\<close>
    \<open>s1a \<in> transition_labels T1a\<close>
    \<open>e1a \<in> transition_labels T1a\<close>
    \<open>s2a \<in> transition_labels T2a\<close>
    \<open>e2a \<in> transition_labels T2a\<close>

    \<open>e1a \<noteq> s1a\<close>
    using cfg_ndet
    by (force simp add: disjoint_iff
        dest: cfg_transition_labels_include_startend cfg_transition_labels_start_not_end)+

  note label_lemmas = label_lemmas1 label_lemmas2

  have transition_lemmas:
  \<open>\<And>c ly. (sa, c, ly) \<notin> T1a\<close>
  \<open>\<And>c ly. (sa, c, ly) \<notin> T2a\<close>
  \<open>\<And>c lx. (lx, c, ea) \<notin> T1a\<close>
  \<open>\<And>c lx. (lx, c, ea) \<notin> T2a\<close>
    using cfg_ndet
    by (force dest: transition_labels_include_startend)+

  show ?case
    using cfg_ndet.hyps(1,3,5-) cfg_b iso1 iso2
    apply simp
    apply (rule_tac x=\<open>\<lambda>l.
      if l = sa then sb
      else if l = ea then eb
      else if l \<in> transition_labels T1a then f1 l else f2 l
    \<close> in exI)
    apply (intro conjI)
         apply (subst bij_betw_cong[
          where g=\<open>\<lambda>t.
            if t = (sa, CRam CSkip, s1a) then (sb, CRam CSkip, s1b)
            else if t = (sa, CRam CSkip, s2a) then (sb, CRam CSkip, s2b)
            else if t = (e1a, CRam CSkip, ea) then (e1b, CRam CSkip, eb)
            else if t = (e2a, CRam CSkip, ea) then (e2b, CRam CSkip, eb)
            else if t \<in> T1a
            then case t of (la, c, lb) \<Rightarrow> (f1 la, c, f1 lb)
            else case t of (la, c, lb) \<Rightarrow> (f2 la, c, f2 lb)
          \<close>])
        apply clarify
        apply (rename_tac lx c ly)
        apply (case_tac \<open>(lx, c, ly) \<notin> T1a \<and> (lx, c, ly) \<notin> T2a\<close>)
         apply (force simp add: label_lemmas transition_lemmas)
        apply (clarsimp simp add: label_lemmas transition_lemmas)
        apply (erule disjE)
         apply (clarsimp simp add: transition_labels_include_startend)
         apply (metis transition_labels_include_startend)
        apply (clarsimp simp add: transition_labels_include_startend disjoint_iff)
        apply (subgoal_tac \<open>lx \<notin> transition_labels T1a \<and> ly \<notin> transition_labels T1a\<close>)
         apply (simp, metis transition_labels_include_startend)
        apply (meson transition_labels_include_startend)

       apply clarsimp
       apply (rule bij_betw_disjoint_insert, rule bij_betw_singleton, blast)
         apply (rule bij_betw_disjoint_insert, rule bij_betw_singleton, blast)
           apply (rule bij_betw_disjoint_insert, rule bij_betw_singleton, blast)
             apply (rule bij_betw_disjoint_insert, rule bij_betw_singleton, blast)
               apply (rule bij_betw_disjoint_Un, blast, blast)
                apply (metis transition_labels_disjoint_then_transitions_disjoint)
               apply (metis transition_labels_disjoint_then_transitions_disjoint)
              apply (force simp add: transition_lemmas)
             apply (force dest: transition_labels_include_end)
            apply (force simp add: label_lemmas transition_lemmas)
           apply (simp, metis cfg_transition_labels_include_end transition_labels_include_end disjoint_iff)
          apply (force simp add: label_lemmas transition_lemmas)
         apply (simp, metis cfg_transition_labels_include_start transition_labels_include_start)
        apply (force simp add: label_lemmas transition_lemmas)
       apply (simp, metis cfg_transition_labels_include_start disjoint_iff transition_labels_include_start)

      apply clarsimp
      apply (rule bij_betw_insert_ignore)
        apply (rule bij_betw_insert_ignore)
          apply (rule bij_betw_disjoint_insert, rule bij_betw_singleton, blast)
            apply (rule bij_betw_insert_ignore)
              apply (rule bij_betw_insert_ignore)
                apply (rule bij_betw_insert_ignore)
                  apply (rule bij_betw_insert_ignore)
                    apply (rule bij_betw_disjoint_insert, rule bij_betw_singleton, blast)
                      apply (rule bij_betw_disjoint_Un, blast, blast)
                       apply blast
                      apply blast
                     apply blast
                    apply blast
                   apply (force simp add: label_lemmas)
                  apply (metis Un_iff cfg_transition_labels_include_end insert_iff)
                 apply blast
                apply blast
               apply (force simp add: label_lemmas)
              apply (metis Un_iff Un_insert_right cfg_transition_labels_include_end)
             apply (force simp add: label_lemmas)
            apply (metis Un_iff Un_insert_left cfg_transition_labels_include_start)
           apply (force simp add: label_lemmas)
          apply (metis Un_iff cfg_transition_labels_include_startend insert_iff)
         apply (force simp add: label_lemmas)
        apply (metis Un_iff Un_insert_right cfg_transition_labels_include_start)
       apply blast
      apply blast

     apply (force simp add: label_lemmas)
    apply (force simp add: label_lemmas)
    done
next
  case (cfg_loop c Ta' sa' ea' sa ea Ta Tb sb eb)

  obtain Tb' sb' eb'
    where cfg_b:
      \<open>cfg c Tb' sb' eb'\<close>
      \<open>sb \<notin> transition_labels Tb'\<close>
      \<open>eb \<notin> transition_labels Tb'\<close>
      \<open>sb \<noteq> eb\<close>
      \<open>(eb', CRam CSkip, sb') \<notin> Tb'\<close>
      \<open>Tb = insert (eb', CRam CSkip, sb') (insert (sb, CRam CSkip, sb') (insert (eb', CRam CSkip, eb) Tb'))\<close>
    using cfg_loop.prems
    by blast

  obtain f
    where cfgiso:
      \<open>bij_betw (\<lambda>a. case a of (la, c, lb) \<Rightarrow> (f la, c, f lb)) Ta' Tb'\<close>
      \<open>bij_betw f (transition_labels Ta') (transition_labels Tb')\<close>
      \<open>f sa' = sb'\<close>
      \<open>f ea' = eb'\<close>
    using cfg_b cfg_loop.hyps
    by blast

  have label_lemmas:
    \<open>sa' \<noteq> ea\<close>
    \<open>ea' \<noteq> sa\<close>
    \<open>sa' \<noteq> sa\<close>
    \<open>ea \<noteq> ea'\<close> \<open>ea' \<noteq> ea\<close>
    using cfg_loop.hyps
    by (force dest: cfg_transition_labels_include_startend)+

  have transition_lemmas:
    \<open>\<And>lx c ly. (lx, c, ly) \<in> Ta' \<Longrightarrow> lx \<noteq> sa\<close>
    \<open>\<And>lx c ly. (lx, c, ly) \<in> Ta' \<Longrightarrow> lx \<noteq> ea\<close>
    \<open>\<And>lx c ly. (lx, c, ly) \<in> Ta' \<Longrightarrow> ly \<noteq> sa\<close>
    \<open>\<And>lx c ly. (lx, c, ly) \<in> Ta' \<Longrightarrow> ly \<noteq> ea\<close>
    using cfg_loop.hyps
    by (force dest: transition_labels_include_startend)+

  show ?case
    using cfg_loop.hyps(1,3,5-) cfg_b cfgiso
    apply simp
    apply (rule_tac x=\<open>\<lambda>l.
      if l = sa then sb
      else if l = ea then eb
      else f l
    \<close> in exI)
    apply (intro conjI)
       apply (subst bij_betw_cong[
          where g=\<open>\<lambda>t.
            if t = (ea', CRam CSkip, sa') then (eb', CRam CSkip, sb')
            else if t = (sa, CRam CSkip, sa') then (sb, CRam CSkip, sb')
            else if t = (ea', CRam CSkip, ea) then (eb', CRam CSkip, eb)
            else case t of (la, c, lb) \<Rightarrow> (f la, c, f lb)
          \<close>])
        apply clarify
        apply (rename_tac lx c ly)
        apply (case_tac \<open>(lx, c, ly) \<notin> Ta'\<close>)
         apply (force simp add: label_lemmas)
        apply (simp add: label_lemmas transition_lemmas)

       apply clarsimp
       apply (rule bij_betw_disjoint_insert, rule bij_betw_singleton, blast)
         apply (rule bij_betw_disjoint_insert, rule bij_betw_singleton, blast)
           apply (rule bij_betw_disjoint_insert, rule bij_betw_singleton, blast)
             apply force
            apply (force dest: transition_lemmas)
           apply (force dest: transition_labels_include_end)
          apply (force simp add: label_lemmas dest: transition_lemmas)
         apply (force dest: cfg_transition_labels_include_end transition_labels_include_start)
        apply (force simp add: label_lemmas)
       apply (force dest: cfg_transition_labels_include_end cfg_transition_labels_include_start)

      apply clarsimp
      apply (rule bij_betw_insert_ignore)
        apply (rule bij_betw_insert_ignore)
          apply (rule bij_betw_disjoint_insert, rule bij_betw_singleton, blast)
            apply (rule bij_betw_insert_ignore)
              apply (rule bij_betw_insert_ignore)
                apply (rule bij_betw_disjoint_insert, rule bij_betw_singleton, blast)
                  apply blast
                 apply (force simp add: cfg_loop.hyps)
                apply (force simp add: cfg_loop.hyps)
               apply (force dest: cfg_transition_labels_include_end)
              apply (force dest: cfg_transition_labels_include_end)
             apply (force dest: cfg_transition_labels_include_start)
            apply (force dest: cfg_transition_labels_include_start)
           apply (metis insertE label_lemmas(2-3))
          apply (force dest: cfg_transition_labels_include_startend)
         apply (force simp add: label_lemmas)
        apply blast
       apply blast
      apply blast
     apply simp
    apply simp
    done
qed


subsection \<open>Small-step\<close>

inductive opsem_prog_smallstep ::
  \<open>'l list \<Rightarrow> 'v state \<Rightarrow> resources \<Rightarrow>
    ('l \<times> 'v comm \<times> 'l) set \<Rightarrow>
    'l list \<Rightarrow> 'v state option \<Rightarrow> resources \<Rightarrow>
    bool\<close>
  (\<open>_, _, _ \<sim>[_]\<leadsto>\<^sub>S _, _, _\<close> [80,0,80,0,80] 80)
  where
  \<open>\<lbrakk> k < length p
   ; (p ! k, CRam c, l') \<in> T
   ; \<sigma>, c \<leadsto> Some \<sigma>'
   \<rbrakk> \<Longrightarrow> p, \<sigma>, fR \<sim>[T]\<leadsto>\<^sub>S p[k := l'], Some \<sigma>', fR\<close>
| \<open>\<lbrakk> k < length p; (p ! k, CRam c, l') \<in> T
   ; \<sigma>, c \<leadsto> None
   \<rbrakk> \<Longrightarrow> p, \<sigma>, fR \<sim>[T]\<leadsto>\<^sub>S p[k := l'], None, fR\<close>
| \<open>\<lbrakk> k < length p
   ; (p ! k, CRelease j, l') \<in> T
   ; j \<notin> the_resources fR
   \<rbrakk> \<Longrightarrow> p, \<sigma>, fR \<sim>[T]\<leadsto>\<^sub>S p[k := l'], Some \<sigma>, (insert_res j fR)\<close>
| \<open>\<lbrakk> k < length p
   ; (p ! k, CAcquire j, l') \<in> T
   ; j \<in> the_resources fR
   \<rbrakk> \<Longrightarrow> p, \<sigma>, fR \<sim>[T]\<leadsto>\<^sub>S p[k := l'], Some \<sigma>, (remove_res j fR)\<close>

inductive opsem_prog_iter_smallstep ::
  \<open>'l list \<Rightarrow> 'v state \<Rightarrow> resources \<Rightarrow>
    ('l \<times> 'v comm \<times> 'l) set \<Rightarrow>
    'l list \<Rightarrow> 'v state option \<Rightarrow> resources \<Rightarrow>
    bool\<close>
  (\<open>_, _, _ \<sim>[_]\<leadsto>*\<^sub>S _, _, _\<close> [80,0,80,0,80] 80)
where
  opsem_prog_iter_smallstep_base: \<open>p, s, fR \<sim>[T]\<leadsto>*\<^sub>S p, Some s, fR\<close>
| opsem_prog_iter_smallstep_step:
  \<open>\<lbrakk> p, s, fR \<sim>[T]\<leadsto>\<^sub>S p', Some s', fR'
   ; p', s', fR' \<sim>[T]\<leadsto>*\<^sub>S p'', s'', fR''
   \<rbrakk> \<Longrightarrow> p, s, fR \<sim>[T]\<leadsto>*\<^sub>S p'', s'', fR''\<close>

lemma opsem_prog_smallstep_length:
  \<open>p, s, fR \<sim>[T]\<leadsto>\<^sub>S p', os', fR' \<Longrightarrow> length p = length p'\<close>
  by (induct rule: opsem_prog_smallstep.induct) simp+

lemma opsem_prog_iter_smallstep_length:
  \<open>p, s, fR \<sim>[T]\<leadsto>*\<^sub>S p', os', fR' \<Longrightarrow> length p = length p'\<close>
  by (induct rule: opsem_prog_iter_smallstep.induct) (simp add: opsem_prog_smallstep_length)+


definition semantic_proof :: \<open>'v comm \<Rightarrow> ('l \<Rightarrow> ('v state \<Rightarrow> bool)) \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close> where
  \<open>semantic_proof c G I T \<equiv>
    (\<exists>s e. cfg c T s e) \<and>
    (\<forall>(l,c',l')\<in>T. case c' of
      CRam cr' \<Rightarrow> ram_comm_forward cr' (G l) \<le> G l'
    | CAcquire r \<Rightarrow> r < length I \<and> G l \<^emph> I ! r \<le> G l'
    | CRelease r \<Rightarrow> r < length I \<and> G l \<le> G l' \<^emph> I ! r
    )\<close>


lemma map_if_index_update_eq:
  \<open>j < n \<Longrightarrow> map (\<lambda>i. if j = i then f i else g i) [0..<n] = (map g [0..<n])[j := f j]\<close>
  by (induct n arbitrary: j)
   (simp add: less_Suc_eq list_update_append split: nat.splits)+

lemma iterated_sepconj_update:
  \<open>i < length ps \<Longrightarrow>
    iterated_sepconj (ps[i := p]) =
    iterated_sepconj (take i ps) \<^emph> p \<^emph> iterated_sepconj (drop (Suc i) ps)\<close>
  by (induct ps arbitrary: p i)
    (force simp add: less_Suc_eq_0_disj sepconj_assoc)+

lemma iterated_sepconj_append_split:
  \<open>iterated_sepconj (xs @ ys) = iterated_sepconj xs \<^emph> iterated_sepconj ys\<close>
  by (induct xs arbitrary: ys) (simp add: sepconj_assoc)+

lemma iterated_sepconj_take_drop_split_at:
  assumes
    \<open>k < length xs\<close>
  shows
    \<open>iterated_sepconj xs =
    iterated_sepconj (take k xs) \<^emph> xs ! k \<^emph> iterated_sepconj (drop (Suc k) xs)\<close>
  using assms
  by (induct xs arbitrary: k) (force simp add: less_Suc_eq_0_disj sepconj_assoc)+

lemma iterated_sepconj_map_range_split_at:
  assumes
    \<open>k < n\<close>
  shows
    \<open>iterated_sepconj (map f [0..<n]) =
    iterated_sepconj (map f [0..<k]) \<^emph> f k \<^emph> iterated_sepconj (map f [Suc k..<n])\<close>
  using assms
  by (simp add: iterated_sepconj_take_drop_split_at take_map drop_map)

definition \<open>local_command P c \<equiv> \<forall>Q. ram_comm_forward c (P \<^emph> Q) \<le> (ram_comm_forward c P) \<^emph> Q\<close>

lemma local_commandI:
  \<open>local_command P c \<Longrightarrow> ram_comm_forward c (P \<^emph> Q) \<le> (ram_comm_forward c P) \<^emph> Q\<close>
  by (simp add: local_command_def)

definition
  \<open>active_resource_invs I fR \<equiv>
    map (\<lambda>k. if k \<in> the_resources fR then I ! k else emp) [0..<length I]\<close>


lemma active_resource_invs_index[simp]:
  \<open>k < length I \<Longrightarrow> active_resource_invs I fR ! k = (if k \<in> the_resources fR then I ! k else emp)\<close>
  by (simp add: active_resource_invs_def)

lemma active_resource_invs_length[simp]:
  \<open>length (active_resource_invs I fR) = length I\<close>
  by (simp add: active_resource_invs_def)


lemma lem_4_2_separation_property:
  assumes
    \<open>pc0, s0, fR0 \<sim>[T]\<leadsto>*\<^sub>S pc, os, fR\<close>
    \<open>os = Some s\<close>
    \<open>\<forall>k<length pc0. semantic_proof (Cs k) (Gs k) I T\<close>
    \<open>\<forall>l0 l1 c. (l0, CRam c, l1) \<in> T \<longrightarrow> (\<forall>k. local_command (Gs k l0) c)\<close>
    \<open>(iterated_sepconj (map (\<lambda>k. Gs k (pc0 ! k)) [0..<length pc0]) \<^emph>
      iterated_sepconj (active_resource_invs I fR0))
      s0\<close>
  shows
    \<open>(iterated_sepconj (map (\<lambda>k. Gs k (pc ! k)) [0..<length pc]) \<^emph>
      iterated_sepconj (active_resource_invs I fR))
      s\<close>
  using assms
proof (induct arbitrary: s rule: opsem_prog_iter_smallstep.induct)
  case opsem_prog_iter_smallstep_base then show ?case by (simp add: le_fun_def)
next
  case (opsem_prog_iter_smallstep_step p s fR T p' s' fR' p'' os'' fR'' s'')
  then show ?case
  proof (cases rule: opsem_prog_smallstep.cases[case_names CRam_succeed CRam_fail CRelease CAcquire])
    case (CRam_succeed k c l')

    have c_local: \<open>local_command (Gs k (p ! k)) c\<close>
      using CRam_succeed opsem_prog_iter_smallstep_step
      by blast

    show ?thesis
    proof (rule opsem_prog_iter_smallstep_step)
      show \<open>\<forall>k<length p'. semantic_proof (Cs k) (Gs k) I T\<close>
        using opsem_prog_iter_smallstep_step.prems CRam_succeed
        by clarsimp

      show \<open>os'' = Some s''\<close>
        using opsem_prog_iter_smallstep_step.prems
        by simp

      show \<open>\<forall>l0 l1 c. (l0, CRam c, l1) \<in> T \<longrightarrow> (\<forall>k. local_command (Gs k l0) c)\<close>
        using opsem_prog_iter_smallstep_step.prems
        by simp

      have c_predicate_transformer: \<open>ram_comm_forward c (Gs k (p ! k)) \<le> Gs k l'\<close>
        using CRam_succeed opsem_prog_iter_smallstep_step
        by (fastforce simp add: semantic_proof_def)

      show
        \<open>(iterated_sepconj (map (\<lambda>k. Gs k (p' ! k)) [0..<length p']) \<^emph>
          iterated_sepconj (active_resource_invs I fR')) s'\<close>
      proof -
        have \<open>(=) s' \<le> ram_comm_forward c ((=) s)\<close>
          using CRam_succeed
          by (clarsimp simp add: le_fun_def ram_comm_forward_def prod_eq_decompose)
        also have \<open>... \<le>
          ram_comm_forward c (iterated_sepconj (map (\<lambda>k. Gs k (p ! k)) [0..<length p]) \<^emph>
          iterated_sepconj (active_resource_invs I fR))\<close>
          using opsem_prog_iter_smallstep_step.prems
          by (force intro!: monoD[OF ram_comm_forward_mono] simp add: le_fun_def)
        also have \<open>... \<le>
          ram_comm_forward c
         (iterated_sepconj (map (\<lambda>k. Gs k (p ! k)) [0..<k]) \<^emph>
          iterated_sepconj (map (\<lambda>k. Gs k (p ! k)) [k..<length p]) \<^emph>
          iterated_sepconj (active_resource_invs I fR))\<close>
          using CRam_succeed
          by (simp add:
              iterated_sepconj_append_split upt_add_eq_append[OF le0 order.strict_implies_order])
        also have \<open>... \<le>
          ram_comm_forward c
          (Gs k (p ! k) \<^emph>
          (iterated_sepconj (map (\<lambda>k. Gs k (p ! k)) [0..<k]) \<^emph>
          iterated_sepconj (map (\<lambda>k. Gs k (p ! k)) [Suc k..<length p]) \<^emph>
          iterated_sepconj (active_resource_invs I fR)))\<close>
          using CRam_succeed
          by (simp add: upt_conv_Cons sepconj_assoc sepconj_left_comm)
        also have \<open>... \<le>
          ram_comm_forward c (Gs k (p ! k)) \<^emph>
          (iterated_sepconj (map (\<lambda>k. Gs k (p ! k)) [0..<k]) \<^emph>
          iterated_sepconj (map (\<lambda>k. Gs k (p ! k))[Suc k..<length p]) \<^emph>
          iterated_sepconj (active_resource_invs I fR))\<close>
          using c_local
          by (force intro!: local_commandI)
        also have \<open>... \<le>
          Gs k l' \<^emph>
          ((iterated_sepconj (map (\<lambda>k. Gs k (p ! k)) [0..<k]) \<^emph>
          iterated_sepconj (map (\<lambda>k. Gs k (p ! k))[Suc k..<length p])) \<^emph>
          iterated_sepconj (active_resource_invs I fR))\<close>
          using c_predicate_transformer
          by (simp add: sepconj_left_mono sepconj_right_mono)
        also have \<open>... \<le>
          (iterated_sepconj (map (\<lambda>ka. Gs ka (p ! ka)) [0..<k]) \<^emph>
          Gs k l' \<^emph>
          iterated_sepconj (map (\<lambda>ka. Gs ka (p ! ka)) [Suc k..<length p])) \<^emph>
          iterated_sepconj (active_resource_invs I fR)\<close>
          by (simp add: sepconj_assoc sepconj_left_comm)
        also have \<open>... \<le>
          iterated_sepconj (map (\<lambda>ka. Gs ka (p[k := l'] ! ka)) [0..<length p]) \<^emph>
          iterated_sepconj (active_resource_invs I fR)\<close>
        proof -
          have s0: \<open>map (\<lambda>ka. Gs ka (p[k := l'] ! ka)) [0..<k] = map (\<lambda>ka. Gs ka (p ! ka)) [0..<k]\<close>
            by simp
          have s1: \<open>
          map (\<lambda>ka. Gs ka (p[k := l'] ! ka)) [Suc k..<length p] =
          map (\<lambda>ka. Gs ka (p ! ka)) [Suc k..<length p]\<close>
            by simp
          have s2: \<open>
            map (\<lambda>ka. Gs ka (p[k := l'] ! ka)) [0..<length p] =
              map (\<lambda>ka. Gs ka (p[k := l'] ! ka)) [0..<k] @
              map (\<lambda>ka. Gs ka (p[k := l'] ! ka)) [k..<length p]\<close>
            using CRam_succeed
            by (force dest: upt_add_eq_append[OF le0 less_imp_le_nat])
          show ?thesis
            using CRam_succeed
            by (simp add: s0 s1 s2 iterated_sepconj_append_split sepconj_assoc upt_conv_Cons)
        qed
        finally show ?thesis
          using CRam_succeed
          by (force simp add: opsem_ram_comm_same_resources)
      qed
    qed
  next
    case (CRelease k r l')
    show ?thesis
    proof (rule opsem_prog_iter_smallstep_step.hyps)
      show \<open>\<forall>k<length p'. semantic_proof (Cs k) (Gs k) I T\<close>
        using CRelease opsem_prog_iter_smallstep_step.prems
        by simp

      show \<open>os'' = Some s''\<close>
        using opsem_prog_iter_smallstep_step.prems
        by simp

      show \<open>\<forall>l0 l1 c. (l0, CRam c, l1) \<in> T \<longrightarrow> (\<forall>k. local_command (Gs k l0) c)\<close>
        using opsem_prog_iter_smallstep_step.prems
        by simp

      have sem_proof_step:
        \<open>r < length I\<close>
        \<open>Gs k (p ! k) \<le> Gs k l' \<^emph> I ! r\<close>
        using CRelease opsem_prog_iter_smallstep_step.prems
        by (force simp add: semantic_proof_def)+

      have
        \<open>iterated_sepconj (map (\<lambda>j. Gs j (p ! j)) [0..<length p]) \<^emph>
          iterated_sepconj (active_resource_invs I fR)
        \<le> iterated_sepconj (map (\<lambda>j. Gs j (p[k := l'] ! j)) [0..<length p]) \<^emph>
          iterated_sepconj (active_resource_invs I fR')\<close>
      proof -
        have
          \<open>iterated_sepconj (map (\<lambda>j. Gs j (p ! j)) [0..<length p]) \<^emph>
            iterated_sepconj (active_resource_invs I fR)
          \<le>
            (iterated_sepconj (map (\<lambda>j. Gs j (p ! j)) [0..<k]) \<^emph>
            Gs k (p ! k) \<^emph>
            iterated_sepconj (map (\<lambda>j. Gs j (p ! j)) [Suc k..<length p])) \<^emph>
            (iterated_sepconj (take r (active_resource_invs I fR)) \<^emph>
            emp \<^emph>
            iterated_sepconj (drop (Suc r) (active_resource_invs I fR)))\<close>
          using CRelease sem_proof_step
          by (clarsimp simp add:
              iterated_sepconj_map_range_split_at
              iterated_sepconj_take_drop_split_at[where xs=\<open>active_resource_invs _ _\<close>])
        also have \<open>... \<le>
          Gs k (p ! k) \<^emph>
          (iterated_sepconj (map (\<lambda>j. Gs j (p ! j)) [0..<k]) \<^emph>
          iterated_sepconj (map (\<lambda>j. Gs j (p ! j)) [Suc k..<length p])) \<^emph>
          (iterated_sepconj (take r (active_resource_invs I fR)) \<^emph>
          iterated_sepconj (drop (Suc r) (active_resource_invs I fR)))\<close>
          by (simp add: upt_conv_Cons sepconj_ac)
        also have \<open>... \<le>
          Gs k l' \<^emph> I ! r \<^emph>
          (iterated_sepconj (map (\<lambda>j. Gs j (p ! j)) [0..<k]) \<^emph>
          iterated_sepconj (map (\<lambda>j. Gs j (p ! j)) [Suc k..<length p])) \<^emph>
          (iterated_sepconj (take r (active_resource_invs I fR)) \<^emph>
          iterated_sepconj (drop (Suc r) (active_resource_invs I fR)))\<close>
          using sem_proof_step
          by (simp add: sepconj_left_mono)
        also have \<open>... \<le>
          iterated_sepconj (map (\<lambda>j. Gs j (p[k := l'] ! j)) [0..<length p]) \<^emph>
          iterated_sepconj (active_resource_invs I fR')\<close>
        proof -
          have s0: \<open>map (\<lambda>ka. Gs ka (p[k := l'] ! ka)) [0..<k] = map (\<lambda>ka. Gs ka (p ! ka)) [0..<k]\<close>
            by simp
          have s1: \<open>
          map (\<lambda>ka. Gs ka (p[k := l'] ! ka)) [Suc k..<length p] =
          map (\<lambda>ka. Gs ka (p ! ka)) [Suc k..<length p]\<close>
            by simp
          have s2:
            \<open>iterated_sepconj (take r (active_resource_invs I fR))
              = iterated_sepconj (take r (active_resource_invs I fR'))\<close>
            using CRelease
            by (force intro: arg_cong[where f=iterated_sepconj] simp add: list_eq_iff_nth_eq)
          have s3:
            \<open>iterated_sepconj (drop (Suc r) (active_resource_invs I fR))
              = iterated_sepconj (drop (Suc r) (active_resource_invs I fR'))\<close>
            using CRelease
            by (force intro: arg_cong[where f=iterated_sepconj] simp add: list_eq_iff_nth_eq)
          show ?thesis
            using CRelease sem_proof_step
            by (simp add: sepconj_ac  s0 s1 s2 s3
                iterated_sepconj_map_range_split_at
                iterated_sepconj_take_drop_split_at[where k=r])
        qed
        finally show ?thesis
          by blast
      qed
      then show
        \<open>(iterated_sepconj (map (\<lambda>k. Gs k (p' ! k)) [0..<length p']) \<^emph>
          iterated_sepconj (active_resource_invs I fR')) s'\<close>
        using CRelease opsem_prog_iter_smallstep_step.prems
          length_list_update predicate1D
        by auto
  qed
  next
    case (CAcquire k r l')
    show ?thesis
    proof (rule opsem_prog_iter_smallstep_step.hyps)
      show \<open>\<forall>k<length p'. semantic_proof (Cs k) (Gs k) I T\<close>
        using CAcquire opsem_prog_iter_smallstep_step.prems
        by simp

      show \<open>os'' = Some s''\<close>
        using opsem_prog_iter_smallstep_step.prems
        by simp

      show \<open>\<forall>l0 l1 c. (l0, CRam c, l1) \<in> T \<longrightarrow> (\<forall>k. local_command (Gs k l0) c)\<close>
        using opsem_prog_iter_smallstep_step.prems
        by simp

      have sem_proof_step:
        \<open>r < length I\<close>
        \<open>Gs k (p ! k) \<^emph> I ! r \<le> Gs k l'\<close>
        using CAcquire opsem_prog_iter_smallstep_step.prems
        by (force simp add: semantic_proof_def)+

      have
        \<open>iterated_sepconj (map (\<lambda>j. Gs j (p ! j)) [0..<length p]) \<^emph>
          iterated_sepconj (active_resource_invs I fR)
        \<le> iterated_sepconj (map (\<lambda>j. Gs j (p[k := l'] ! j)) [0..<length p]) \<^emph>
          iterated_sepconj (active_resource_invs I fR')\<close>
      proof -
        have
          \<open>iterated_sepconj (map (\<lambda>j. Gs j (p ! j)) [0..<length p]) \<^emph>
            iterated_sepconj (active_resource_invs I fR)
          \<le>
            (iterated_sepconj (map (\<lambda>j. Gs j (p ! j)) [0..<k]) \<^emph>
            Gs k (p ! k) \<^emph>
            iterated_sepconj (map (\<lambda>j. Gs j (p ! j)) [Suc k..<length p])) \<^emph>
            (iterated_sepconj (take r (active_resource_invs I fR)) \<^emph>
            I ! r \<^emph>
            iterated_sepconj (drop (Suc r) (active_resource_invs I fR)))\<close>
          using CAcquire sem_proof_step
          by (clarsimp simp add:
              iterated_sepconj_map_range_split_at
              iterated_sepconj_take_drop_split_at[where xs=\<open>active_resource_invs _ _\<close>])
        also have \<open>... \<le>
          Gs k (p ! k) \<^emph> I ! r \<^emph>
          (iterated_sepconj (map (\<lambda>j. Gs j (p ! j)) [0..<k]) \<^emph>
          iterated_sepconj (map (\<lambda>j. Gs j (p ! j)) [Suc k..<length p])) \<^emph>
          (iterated_sepconj (take r (active_resource_invs I fR)) \<^emph>
          iterated_sepconj (drop (Suc r) (active_resource_invs I fR)))\<close>
          by (simp add: upt_conv_Cons sepconj_ac)
        also have \<open>... \<le>
          Gs k l' \<^emph>
          (iterated_sepconj (map (\<lambda>j. Gs j (p ! j)) [0..<k]) \<^emph>
          iterated_sepconj (map (\<lambda>j. Gs j (p ! j)) [Suc k..<length p])) \<^emph>
          (iterated_sepconj (take r (active_resource_invs I fR)) \<^emph>
          iterated_sepconj (drop (Suc r) (active_resource_invs I fR)))\<close>
          using sem_proof_step
          by (simp add: sepconj_left_mono)
        also have \<open>... \<le>
          iterated_sepconj (map (\<lambda>j. Gs j (p[k := l'] ! j)) [0..<length p]) \<^emph>
          iterated_sepconj (active_resource_invs I fR')\<close>
        proof -
          have s0: \<open>map (\<lambda>ka. Gs ka (p[k := l'] ! ka)) [0..<k] = map (\<lambda>ka. Gs ka (p ! ka)) [0..<k]\<close>
            by simp
          have s1: \<open>
          map (\<lambda>ka. Gs ka (p[k := l'] ! ka)) [Suc k..<length p] =
          map (\<lambda>ka. Gs ka (p ! ka)) [Suc k..<length p]\<close>
            by simp
          have s2:
            \<open>iterated_sepconj (take r (active_resource_invs I fR))
              = iterated_sepconj (take r (active_resource_invs I fR'))\<close>
            using CAcquire
            by (force intro: arg_cong[where f=iterated_sepconj] simp add: list_eq_iff_nth_eq)
          have s3:
            \<open>iterated_sepconj (drop (Suc r) (active_resource_invs I fR))
              = iterated_sepconj (drop (Suc r) (active_resource_invs I fR'))\<close>
            using CAcquire
            by (force intro: arg_cong[where f=iterated_sepconj] simp add: list_eq_iff_nth_eq)
          show ?thesis
            using CAcquire sem_proof_step
            by (simp add: sepconj_ac s0 s1 s2 s3
              iterated_sepconj_map_range_split_at
              iterated_sepconj_take_drop_split_at[where k=r])
        qed
        finally show ?thesis
          by blast
      qed
      then show
        \<open>(iterated_sepconj (map (\<lambda>k. Gs k (p' ! k)) [0..<length p']) \<^emph>
          iterated_sepconj (active_resource_invs I fR')) s'\<close>
        using CAcquire opsem_prog_iter_smallstep_step.prems
          length_list_update predicate1D
        by auto
    qed
  qed
qed

end