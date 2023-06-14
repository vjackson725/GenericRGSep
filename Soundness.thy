theory Soundness
  imports Semantics
begin

lemma triple_rule_parallel:
  fixes a b :: \<open>('x,'p) action process\<close>
  assumes
    \<open>\<lbrace> pa \<rbrace> interp_act a \<lbrace> qa \<rbrace>\<close>
    \<open>\<lbrace> pb \<rbrace> interp_act b \<lbrace> qb \<rbrace>\<close>
  shows \<open>\<lbrace> pa \<^emph> pb \<rbrace> interp_act (a \<parallel> b) \<lbrace> qa \<^emph> qb \<rbrace>\<close>
  using assms
  sorry

lemma triple_rule_frame:
  fixes a b :: \<open>('x,'p) action process\<close>
  assumes \<open>\<lbrace> p \<rbrace> interp_act a \<lbrace> q \<rbrace>\<close>
  shows \<open>\<lbrace> p \<^emph> r \<rbrace> interp_act a \<lbrace> q \<^emph> r \<rbrace>\<close>
  using assms
  sorry

end