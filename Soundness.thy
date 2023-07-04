theory Soundness
  imports Semantics
begin


lemma htriple_zero: 
  \<open>\<lbrace> \<bottom> \<rbrace> 0 \<lbrace> q \<rbrace>\<close>  
  unfolding htriple_def generic_htriple_def 
  by blast  

lemma htriple_one: 
  \<open>\<lbrace> p \<rbrace> 1 \<lbrace> p \<rbrace>\<close> unfolding htriple_def generic_htriple_def lift_interp_process_def one_process_def
  by (simp add: htriple_def generic_htriple_def lift_interp_process_def one_process_def)

lemma htriple_ndet:
  fixes a b :: \<open>('x,'p) action process\<close>
  assumes
    \<open>\<lbrace> p1 \<rbrace> a \<lbrace> q1 \<rbrace>\<close>
    \<open>\<lbrace> p2 \<rbrace> b \<lbrace> q2 \<rbrace>\<close>
  shows 
    \<open>\<lbrace> p1 \<sqinter> p2 \<rbrace>  (a + b) \<lbrace> q1 \<squnion> q2 \<rbrace>\<close>
  using assms unfolding htriple_def generic_htriple_def lift_interp_process_def plus_process_def
  by (clarsimp, metis Un_iff plus_process.rep_eq proctr_inverse)
  
lemma htriple_parallel:
  fixes a b :: \<open>('x,'p) action process\<close>
  assumes
    \<open>\<lbrace> p1 \<rbrace>  a \<lbrace> q1 \<rbrace>\<close>
    \<open>\<lbrace> p2 \<rbrace>  b \<lbrace> q2 \<rbrace>\<close>
  shows 
    \<open>\<lbrace> p1 \<^emph> p2 \<rbrace>  (a * b) \<lbrace>  (q1 \<^emph> q2) \<rbrace>\<close>
(*this may be missing something about non-interference (wsstablerel?) *)
  using assms 
  unfolding htriple_def generic_htriple_def lift_interp_process_def 
            times_process.rep_eq  
  apply -
  apply (intro allI)
  apply (case_tac "\<exists> s''. (\<forall>t\<in>proctr a. sstep_sem\<^sup>* t s s'')")
   prefer 2
  subgoal sorry
  apply (erule exE)  
  apply (erule_tac x=s in allE, erule_tac x=s'' in allE, erule impE, assumption)
apply (case_tac "(\<forall>t\<in>proctr b. sstep_sem\<^sup>* t s'' s')")
   prefer 2
  subgoal sorry

  apply (erule_tac x=s'' in allE, erule_tac x=s' in allE, erule impE, assumption)
  apply (rule impI) 

  apply (clarsimp )
  apply (rename_tac l1 h1 ln hn l1' h1')
  find_theorems "_ \<le> _" "_ * _"

  sorry


lemma trace_TCons_concatD:
  \<open>x \<cdot> t' = ta + tb \<Longrightarrow>
      (ta = TNil \<and> tb = x \<cdot> t') \<or>
     (\<exists>ta'. ta = x \<cdot> ta' \<and> t' = ta' + tb)\<close>
  by (metis plus_trace.elims trace.sel(2) trace_start.simps(2))

lemma trace_TCons_concatI:
  \<open>(ta = TNil \<and> tb = x \<cdot> t') \<or>
   (\<exists>ta'. ta = x \<cdot> ta' \<and> t' = ta' + tb) \<Longrightarrow>
  x \<cdot> t' = ta + tb\<close>
  by fastforce

lemma trace_TCons_concat_eq:
  \<open>(x \<cdot> t' = ta + tb) \<longleftrightarrow>
      (ta = TNil \<and> tb = x \<cdot> t') \<or>
     (\<exists>ta'. ta = x \<cdot> ta' \<and> t' = ta' + tb)\<close>
  using  trace_TCons_concatD 
  by fastforce

lemma interp_trace_concatD':
  \<open>f\<^sup>* t s s' \<Longrightarrow> t = ta + tb \<Longrightarrow> \<exists>si. f\<^sup>* ta s si \<and> f\<^sup>* tb si s'\<close>
  by (induct f t s s' arbitrary: ta tb rule: lift_interp_trace.induct)
     (fastforce dest!: trace_TCons_concatD)+

lemma interp_trace_concatD:
  \<open>f\<^sup>* (ta + tb) s s' \<Longrightarrow> \<exists>si. f\<^sup>* ta s si \<and> f\<^sup>* tb si s'\<close>
  by (fastforce dest: interp_trace_concatD')

lemma interp_trace_concatI:
  \<open>f\<^sup>* ta s si \<Longrightarrow> f\<^sup>* tb si s'\<Longrightarrow> t = ta + tb \<Longrightarrow>  f\<^sup>* t s s'\<close>
  using trace_TCons_concat_eq
  by (induct f ta s si arbitrary: t tb rule: lift_interp_trace.induct)
    (fastforce dest!: trace_TCons_concatD)+

lemma interp_trace_concat_eq:
  \<open>f\<^sup>* (ta + tb) s s' = (\<exists>si. f\<^sup>* ta s si \<and> f\<^sup>* tb si s')\<close>
  using interp_trace_concatD interp_trace_concatI
  by fast

lemma interp_seq_0_eq:
  \<open>lift_interp_process sstep_sem (0 \<triangleright> b) s s' =
  (\<exists>si. lift_interp_process sstep_sem 0 s si \<and> lift_interp_process sstep_sem b si s')\<close>
  oops



lemma lift_interp_0:
  \<open>lift_interp_process f 0 s s'\<close>
  by (simp add: lift_interp_process_def zero_process.rep_eq)


lemma lift_interp_process_seqI:
  \<open>lift_interp_process f a s si \<Longrightarrow> 
   lift_interp_process f b si s' \<Longrightarrow> 
   lift_interp_process f (a \<triangleright> b) s s'\<close>
  by (fastforce simp: lift_interp_process_def interp_trace_concat_eq)

(*
lemma lift_interp_process_seq:
  \<open>lift_interp_process f a s si \<Longrightarrow> 
   lift_interp_process f b si s' \<Longrightarrow> 
   lift_interp_process f (a \<triangleright> b) s s'\<close>
  by (fastforce simp: lift_interp_process_def interp_trace_concat_eq)
*)
lemma htriple_seq:
  fixes a b :: \<open>('x,'p) action process\<close>
  assumes
    \<open>\<lbrace> p \<rbrace> a \<lbrace> q \<rbrace>\<close>
    \<open>\<lbrace> q \<rbrace> b \<lbrace> r \<rbrace>\<close>
  shows \<open>\<lbrace> p \<rbrace>  (a \<triangleright> b) \<lbrace> r \<rbrace>\<close>
  (* what's the difference between seq and times? *)
  using assms unfolding htriple_def generic_htriple_def  
  apply (intro allI impI)
  unfolding lift_interp_process_def
  sorry

 



(*

lemma 
 fixes c1 c2 :: \<open>('x,'p) action process\<close>
  assumes
    \<open>\<lbrace> pa \<rbrace> \<lambda>s s'. \<forall>t1\<in>proctr c1. s \<sim>t1\<leadsto>\<^sup>* s' \<lbrace> qa \<rbrace>\<close>
    \<open> \<lbrace> pb \<rbrace> \<lambda>s s'. \<forall>t2\<in>proctr c2. s \<sim>t2\<leadsto>\<^sup>* s' \<lbrace> qb \<rbrace>\<close>
  shows \<open>\<lbrace> pa \<^emph> pb \<rbrace> \<lambda>s s'. \<forall>t1_t2\<in>proctr (c1 * c2). s \<sim>t1_t2\<leadsto>\<^sup>* s' \<lbrace> qa \<^emph> qb \<rbrace>\<close>
  oops
*)

lemma triple_rule_frame:
  fixes a b :: \<open>('x,'p) action process\<close>
  assumes \<open>\<lbrace> p \<rbrace>  a \<lbrace> q \<rbrace>\<close>
  shows \<open>\<lbrace> p \<^emph> r \<rbrace> a \<lbrace> q \<^emph> r \<rbrace>\<close>
  using assms
  sorry



end