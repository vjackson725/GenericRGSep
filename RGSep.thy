theory RGSep
  imports Stabilisation PermHeap
begin

definition \<open>passert p \<equiv> \<lambda>a b. p a\<close>
definition \<open>passume p \<equiv> \<lambda>a b. p b\<close> 


datatype ('h) basic_comm =
  Nop

inductive basic_rel :: \<open>'h basic_comm \<Rightarrow> 'h \<Rightarrow> 'h \<Rightarrow> bool\<close> where
  \<open>basic_rel c h h'\<close>

datatype 'h comm =
  Skip
  | Abort
  | Seq \<open>'h comm\<close> \<open>'h comm\<close> (infixr \<open>;;\<close> 75)
  | Par \<open>'h comm\<close> \<open>'h comm\<close> (infixr \<open>\<parallel>\<close> 65)
  | Ndet \<open>'h comm\<close> \<open>'h comm\<close> (infixr \<open>\<^bold>+\<close> 65)
  | Iter \<open>'h comm\<close> (\<open>_\<^sup>\<star>\<close> [80] 80)
  | Basic \<open>'h basic_comm\<close>
  | Assert \<open>'h \<Rightarrow> bool\<close>
  | Assume \<open>'h \<Rightarrow> bool\<close>

datatype act =
    ReduceSeq
  | ReduceNdetLeft
  | ReduceNdetRight
  | ReduceParLeft
  | ReduceParRight
  | ActAssert
  | ActAssume
  | ActIterStep

inductive opsem :: \<open>act \<Rightarrow> 'h \<times> 'h comm \<Rightarrow> 'h \<times> 'h comm \<Rightarrow> bool\<close> where
  SeqL: \<open>opsem a (h,s) (h',s) \<Longrightarrow> opsem a (h, s ;; t) (h', s' ;; t)\<close>
| SeqR: \<open>opsem ReduceSeq (h, Skip ;; t) (h, t)\<close>
| NdetL: \<open>opsem ReduceNdetLeft (h, s \<^bold>+ t) (h, s)\<close>
| NdetR: \<open>opsem ReduceNdetRight (h, s \<^bold>+ t) (h, t)\<close>
| ParStepL: \<open>opsem a (h, s) (h', s') \<Longrightarrow> opsem a (h, s \<parallel> t) (h', s' \<parallel> t)\<close>
| ParStepR: \<open>opsem a (h, t) (h', t') \<Longrightarrow> opsem a (h, s \<parallel> t) (h', s \<parallel> t')\<close>
| ParL: \<open>opsem ReduceParLeft (h, Skip \<parallel> t) (h, t)\<close>
| ParR: \<open>opsem ReduceParRight (h, s \<parallel> Skip) (h, s)\<close>
| IterStep: \<open>opsem ActIterStep (h, s\<^sup>\<star>) (h', s ;; s\<^sup>\<star>)\<close>
| AssertTrue: \<open>p h \<Longrightarrow> opsem ActAssert (h, Assert p) (h, Skip)\<close>
| AssertFalse: \<open>\<not> p h \<Longrightarrow> opsem ActAssert (h, Assume p) (h, Abort)\<close>
| AssumeTrue: \<open>p h \<Longrightarrow> opsem ActAssume (h, Assume p) (h, Skip)\<close>
| AssumeFalse: \<open>\<not> p h \<Longrightarrow> opsem ActAssume (h, Assert p) (h, c)\<close>

abbreviation pretty_opsem :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _\<close> (\<open>_ \<midarrow>(_)\<rightarrow> _\<close>) where
  \<open>hs \<midarrow>a\<rightarrow> ht \<equiv> opsem a hs ht\<close>

inductive rgsat
  :: \<open>'h comm \<Rightarrow> ('h \<Rightarrow> 'h \<Rightarrow> bool) \<Rightarrow> ('h \<Rightarrow> 'h \<Rightarrow> bool) \<Rightarrow> ('h \<Rightarrow> bool) \<Rightarrow> ('h \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where
  rg_skip: \<open>rgsat Skip r g p (\<lceil> p \<rceil>\<^bsub>R\<^esub>)\<close>
| rg_iter: \<open>rgsat c r g p p \<Longrightarrow> rgsat (c\<^sup>\<star>) r g p p\<close>
| rg_weaken: \<open>p \<le> p' \<Longrightarrow> q' \<le> q \<Longrightarrow> r \<le> r' \<Longrightarrow> g' \<le> g \<Longrightarrow> rgsat c r' g' p' q' \<Longrightarrow> rgsat c r g p q\<close>
| rg_par:
  \<open>rgsat s1 (r \<squnion> g2) g1 p1 q1 \<Longrightarrow>
    rgsat s2 (r \<squnion> g1) g2 p2 q2 \<Longrightarrow>
    rgsat (s1 \<parallel> s2) r (g1 \<squnion> g2) (p1 \<sqinter> p2) (q1 \<sqinter> q2)\<close>
| rg_basic:
  \<open>passert p \<sqinter> basic_rel c \<le> passume q \<Longrightarrow>
    passert p \<sqinter> basic_rel c \<le> g \<Longrightarrow>
    rgsat (Basic c) r g (\<lfloor> p \<rfloor>\<^bsub>r\<^esub>) (\<lceil> q \<rceil>\<^bsub>r\<^esub>)\<close>

end