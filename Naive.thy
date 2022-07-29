theory Naive
  imports Common 
begin

fun is_prefix :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "is_prefix [] str = True"
| "is_prefix pref [] = False"
| "is_prefix (p#pref) (s#str) = (if s = p then is_prefix pref str else False)"

text \<open>naive_search [needle] [haystack]\<close>
fun naive_search ::  "'a list \<Rightarrow> 'a list \<Rightarrow> nat list" where
  "naive_search [] hay = [0]"
| "naive_search needle [] = []"
| "naive_search needle (h#ay) =
    (if is_prefix needle (h#ay)
     then 0 # (map Suc (naive_search needle ay))
     else map Suc (naive_search needle ay))"

value "naive_search ''hello'' ''hello world hello'' = [0, 12]"
value "naive_search ''a'' ''aba'' = [0, 2]"

lemma is_prefix_substring_at: "is_prefix needle hay = sublist_at needle hay 0"
  by (induction hay rule: is_prefix.induct) auto

lemma naive_search_correct:
  assumes "idx \<in> set (naive_search needle hay)"
    shows "sublist_at needle hay idx"
  using assms
proof (induction hay arbitrary: idx rule: naive_search.induct)
  case (1 hay)
  then show ?case by simp
next
  case (2 n eedle)
  then show ?case by simp
next
  case (3 n eedle h ay idx)

  let ?needle = "n#eedle"
  let ?hay = "h#ay"

  have "idx \<in> set (map Suc (naive_search ?needle ay)) \<Longrightarrow> sublist_at ?needle ?hay idx"
    using "3.IH" by fastforce

  then show ?case 
    using is_prefix_substring_at 
    by (metis "3.prems" naive_search.simps(3) set_ConsD)
qed



end