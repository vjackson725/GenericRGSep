theory Soundness
  imports Semantics
begin


lemma htriple_zero: 
  \<open>\<lbrace> \<bottom> \<rbrace> 0 \<lbrace> q \<rbrace>\<close>  
  unfolding htriple_def generic_htriple_def 
  by blast  

lemma htriple_one: 
  \<open>\<lbrace> p \<rbrace> 1 \<lbrace> p \<rbrace>\<close> 
  by (simp add: htriple_def generic_htriple_def lift_interp_def one_process_def)



lemma htriple_ndet:
  fixes a b :: \<open>('x,'p) action process\<close>
  assumes
    \<open>\<lbrace> p1 \<rbrace> a \<lbrace> q1 \<rbrace>\<close>
    \<open>\<lbrace> p2 \<rbrace> b \<lbrace> q2 \<rbrace>\<close>
  shows 
    \<open>\<lbrace> p1 \<sqinter> p2 \<rbrace>  (a + b) \<lbrace> q1 \<squnion> q2 \<rbrace>\<close>
  using assms unfolding htriple_def generic_htriple_def lift_interp_def plus_process_def
  by (clarsimp, metis Un_iff plus_process.rep_eq proctr_inverse)
  
lemma htriple_parallel:
  fixes a b :: \<open>('x,'p) action process\<close>
  assumes
    \<open>\<lbrace> p1 \<rbrace>  a \<lbrace> q1 \<rbrace>\<close>
    \<open>\<lbrace> p2 \<rbrace>  b \<lbrace> q2 \<rbrace>\<close>
  shows 
    \<open>\<lbrace> p1 \<^emph> p2 \<rbrace>  (a * b) \<lbrace> q1 \<^emph> q2 \<rbrace>\<close>
(*this may be missing something about non-interference *)
  using assms 
  unfolding htriple_def generic_htriple_def lift_interp_def 
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


lemma htriple_seq:
  fixes a b :: \<open>('x,'p) action process\<close>
  assumes
    \<open>\<lbrace> p \<rbrace> a \<lbrace> q \<rbrace>\<close>
    \<open>\<lbrace> q \<rbrace> b \<lbrace> r \<rbrace>\<close>
  shows \<open>\<lbrace> p \<rbrace>  (a \<triangleright> b) \<lbrace> r \<rbrace>\<close>
  (* what's the difference between seq and times? *)
  using assms unfolding htriple_def generic_htriple_def lift_interp_def 
using lift_interp_trace.simps
  apply clarsimp
  apply (cases a; cases b; clarsimp)
  apply (rename_tac a' b')

  using one_process.rep_eq times_process.rep_eq less_eq_process_def proctr_inverse
leD
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