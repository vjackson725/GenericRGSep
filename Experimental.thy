theory Experimental
  imports Stabilisation
begin


class distrib_sep_alg = glb_multiunit_sep_alg + cancel_multiunit_sep_alg +
  assumes distrib_law:
    \<open>a ## b \<Longrightarrow> a ## c \<Longrightarrow>
      \<not> b ## c \<Longrightarrow> \<not> (a + b ## a + c) \<Longrightarrow>
         (a + b) \<sqinter> (a + c) \<le> a + (b \<sqinter> c)\<close>

end