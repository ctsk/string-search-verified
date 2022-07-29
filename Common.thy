theory Common
  imports Main
begin

\<comment> \<open>Yanked from AFP/Knuth_Morris_Pratt.KMP\<close>
fun sublist_at :: "'a list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> bool" where
  "sublist_at (x#xs) (y#ys) 0 \<longleftrightarrow> x=y \<and> sublist_at xs ys 0" |
  "sublist_at xs (y#ys) (Suc i) \<longleftrightarrow> sublist_at xs ys i" |
  "sublist_at [] ys 0 \<longleftrightarrow> True" |
  "sublist_at _ [] _ \<longleftrightarrow> False"

end