theory Soundness
  imports Semantics
begin


lemma htriple_ndet:
  fixes a b :: \<open>('x,'p) action process\<close>
  assumes
    \<open>\<lbrace> p1 \<rbrace> a \<lbrace> q1 \<rbrace>\<close>
    \<open>\<lbrace> p2 \<rbrace> b \<lbrace> q2 \<rbrace>\<close>
  shows 
    \<open>\<lbrace> p1 \<sqinter> p2 \<rbrace>  (a + b) \<lbrace> q1 \<squnion> q2 \<rbrace>\<close>
  sorry


lemma htriple_seq:
  fixes a b :: \<open>('x,'p) action process\<close>
  assumes
    \<open>\<lbrace> p \<rbrace> a \<lbrace> q \<rbrace>\<close>
    \<open>\<lbrace> q \<rbrace> b \<lbrace> r \<rbrace>\<close>
  shows \<open>\<lbrace> p \<rbrace>  (a \<triangleright> b) \<lbrace> r \<rbrace>\<close>
  using assms htriple'_def seq_process_def  leD less_eq_process_def
      zero_process_def 
  sorry

lemma htriple_parallel:
  fixes a b :: \<open>('x,'p) action process\<close>
  assumes
    \<open>\<lbrace> p1 \<rbrace>  a \<lbrace> q1 \<rbrace>\<close>
    \<open>\<lbrace> p2 \<rbrace>  b \<lbrace> q2 \<rbrace>\<close>
  shows 
    \<open>\<lbrace> p1 \<^emph> p2 \<rbrace>  (a * b) \<lbrace> q1 \<^emph> q2 \<rbrace>\<close>
  sorry


lemma htriple_zero: \<open>\<lbrace> \<bottom> \<rbrace> 0 \<lbrace> q \<rbrace>\<close>  sorry

lemma htriple_one: \<open>\<lbrace> p \<rbrace> 1 \<lbrace> p \<rbrace>\<close> 
  using htriple'_def htriple_def one_process.rep_eq sorry


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