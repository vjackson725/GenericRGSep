theory RGSep
  imports Stabilisation PermHeap
begin

datatype 'h comm =
  Skip
  | Abort
  | Seq \<open>'h comm\<close> \<open>'h comm\<close> (infixr \<open>;;\<close> 75)
  | Par \<open>'h comm\<close> \<open>'h comm\<close> (infixr \<open>\<parallel>\<close> 65)
  | Ndet \<open>'h comm\<close> \<open>'h comm\<close> (infixr \<open>\<^bold>+\<close> 65)
  | Iter \<open>'h comm\<close> (\<open>_\<^sup>\<star>\<close> [80] 80)
  | Basic \<open>'h \<Rightarrow> 'h \<Rightarrow> bool\<close>

datatype 'h act =
    Tau
  | Env \<open>'h \<Rightarrow> 'h \<Rightarrow> bool\<close>

inductive opsem :: \<open>'h act \<Rightarrow> 'h \<times> 'h comm \<Rightarrow> 'h \<times> 'h comm \<Rightarrow> bool\<close> where
  SeqL: \<open>opsem a (h,s) (h',s) \<Longrightarrow> opsem a (h, s ;; t) (h', s' ;; t)\<close>
| SeqR: \<open>opsem Tau (h, Skip ;; t) (h, t)\<close>
| NdetL: \<open>opsem Tau (h, s \<^bold>+ t) (h, s)\<close>
| NdetR: \<open>opsem Tau (h, s \<^bold>+ t) (h, t)\<close>
| ParStepL: \<open>opsem a (h, s) (h', s') \<Longrightarrow> opsem a (h, s \<parallel> t) (h', s' \<parallel> t)\<close>
| ParStepR: \<open>opsem a (h, t) (h', t') \<Longrightarrow> opsem a (h, s \<parallel> t) (h', s \<parallel> t')\<close>
| ParL: \<open>opsem Tau (h, Skip \<parallel> t) (h, t)\<close>
| ParR: \<open>opsem Tau (h, s \<parallel> Skip) (h, s)\<close>
| IterStep: \<open>opsem Tau (h, s\<^sup>\<star>) (h', s ;; s\<^sup>\<star>)\<close>
| BasicStep: \<open>c h h' \<Longrightarrow> opsem Tau (h, Basic c) (h', Skip)\<close>
| BasicFail: \<open>\<forall>h'. \<not> c h h' \<Longrightarrow> opsem Tau (h, Basic c) (h, Abort)\<close>
| EnvStep: \<open>r h h' \<Longrightarrow> opsem (Env r) (h, t) (h', t)\<close>

definition \<open>passert p \<equiv> \<lambda>a b. p a\<close>
definition \<open>passume p \<equiv> \<lambda>a b. p b\<close> 

abbreviation \<open>Assert p \<equiv> Basic (passert p)\<close>
abbreviation \<open>Assume p \<equiv> Basic (passume p)\<close>

abbreviation(input) pretty_opsem :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _\<close> (\<open>_ \<midarrow>(_)\<rightarrow> _\<close> [60,0,60] 60) where
  \<open>hs \<midarrow>a\<rightarrow> ht \<equiv> opsem a hs ht\<close>

(* TODO: infinite behaviour *)
inductive rtrans_opsem :: \<open>'h act list \<Rightarrow> 'h \<times> 'h comm \<Rightarrow> 'h \<times> 'h comm \<Rightarrow> bool\<close> where
  ISemStep:
  \<open>opsem a (h, s) (h', s) \<Longrightarrow>
    rtrans_opsem as (h', s') (h'', s'') \<Longrightarrow> 
    rtrans_opsem (a # as) (h, s) (h'', s'')\<close>
| ISemEnd: \<open>rtrans_opsem [] (h, s) (h, s)\<close>

abbreviation(input) pretty_rtrans_opsem :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _\<close> (\<open>_ \<midarrow>(_)\<rightarrow>\<^sup>\<star> _\<close> [60,0,60] 60) where
  \<open>hs \<midarrow>as\<rightarrow>\<^sup>\<star> ht \<equiv> rtrans_opsem as hs ht\<close>

definition erasing_rtrans_opsem
  :: \<open>'h \<times> 'h comm \<Rightarrow> 'h \<times> 'h comm \<Rightarrow> bool\<close> (\<open>_ \<longlongrightarrow>\<^sup>\<star> _\<close> [60,60] 60) 
  where
  \<open>erasing_rtrans_opsem hs ht \<equiv> \<exists>as. rtrans_opsem as hs ht\<close>

lemma eventually_skip_or_abort:
  \<open>\<exists>h' s'. (h, s) \<longlongrightarrow>\<^sup>\<star> (h', s') \<and> (s' = Skip \<or> s' = Abort)\<close>

  oops

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
  \<open>passert p \<sqinter> c \<le> passume q \<Longrightarrow>
    passert p \<sqinter> c \<le> g \<Longrightarrow>
    rgsat (Basic c) r g (\<lfloor> p \<rfloor>\<^bsub>r\<^esub>) (\<lceil> q \<rceil>\<^bsub>r\<^esub>)\<close>


lemma soundness:
  \<open>(h, s) \<midarrow>a\<rightarrow> ht\<close>

end