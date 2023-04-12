theory StableLang
  imports Stabilisation
begin

thm HOL.imp_conjR

notation(input)
  plus (infixl \<open>\<parallel>\<close> 65)

text \<open>
  A process can be represented as a trace of predicate pairs.
\<close>
codatatype 'a ptrace =
    TCons \<open>('a \<Rightarrow> bool) \<times> ('a \<Rightarrow> bool)\<close> \<open>'a ptrace\<close> (infixr "\<cdot>" 70)
  | TEnd

coinductive pmergep :: \<open>'a ptrace \<Rightarrow> 'a ptrace \<Rightarrow> 'a ptrace \<Rightarrow> bool\<close>
  where
  \<open>pmergep a TEnd TEnd\<close>
| \<open>pmergep TEnd b TEnd\<close>
| \<open>pmergep a b c \<Longrightarrow> pmergep ((p,q) \<cdot> a) b ((p,q) \<cdot> c)\<close>
| \<open>pmergep a b c \<Longrightarrow> pmergep a ((p,q) \<cdot> b) ((p,q) \<cdot> c)\<close>
| \<open>pmergep a b c \<Longrightarrow> pmergep ((p,r) \<cdot> a) ((r,q) \<cdot> b) ((p,q) \<cdot> c)\<close>
| \<open>pmergep a b c \<Longrightarrow> pmergep ((r,q) \<cdot> a) ((p,r) \<cdot> b) ((p,q) \<cdot> c)\<close>

datatype 'a process = Process (proctr: \<open>'a ptrace set\<close>)

lemma pmergep_iff[iff]:
  \<open>pmergep TEnd b c \<longleftrightarrow> b = c\<close>
  \<open>pmergep a TEnd c \<longleftrightarrow> a = c\<close>
  sorry

lemma pmergep_comm:
  \<open>pmergep a b t \<Longrightarrow> pmergep b a t\<close>
  apply (erule pmergep.cases)
       apply (rule pmergep.coinduct, assumption)
  apply clarsimp
  oops

lemma pmergep_assoc1:
  \<open>pmergep a b m1 \<Longrightarrow> pmergep m1 c d \<Longrightarrow> \<exists>m2. pmergep b c m2 \<and> pmergep a m2 d\<close>
  oops

instantiation process :: (type) monoid_add
begin

definition plus_process :: \<open>'a process \<Rightarrow> 'a process \<Rightarrow> 'a process\<close> where
  \<open>plus_process A B \<equiv> Process {c|c a b. a \<in> proctr A \<and> b \<in> proctr B \<and> pmergep a b c }\<close>

instance
proof
  fix a b c :: \<open>'a process\<close>
  show \<open>a + b + c = a + (b + c)\<close>
    apply (clarsimp simp add: plus_process_def set_eq_iff)
    apply (intro iffI; clarsimp)
     apply (rename_tac dt at ct bt)
     apply (rule_tac x=at in exI)
     apply simp
     apply (rule_tac x=new in exI)
    apply (rule conjI)
      apply (rule_tac x=bt in exI)
      apply simp
      apply (rule_tac x=ct in exI)
      apply simp
    sorry
  show \<open>0 + a = a\<close>
    sorry
  show \<open>a + 0 = a\<close>
    sorry

qed

end





end