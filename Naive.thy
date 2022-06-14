theory Naive
  imports "HOL-Library.Sublist"
begin


fun is_prefix :: "string \<Rightarrow> string \<Rightarrow> bool" where
  "is_prefix [] str = True"
| "is_prefix pref [] = False"
| "is_prefix (p#pref) (s#str) = (if s = p then is_prefix pref str else False)"


text \<open>naive_search [needle] [haystack]\<close>
fun naive_search :: "string \<Rightarrow> string \<Rightarrow> bool" where
  "naive_search [] hay = True"
| "naive_search needle [] = False"
| "naive_search needle (h#ay) = 
    (if is_prefix needle (h#ay)
     then True
     else naive_search needle ay)"

value "naive_search ''hello'' ''hello world''"

lemma is_prefix_correct: "is_prefix needle hay = prefix needle hay"
  by (induction hay rule: is_prefix.induct) auto

lemma naive_search_correct: "naive_search needle hay = sublist needle hay"
proof (induction hay rule: naive_search.induct)
  case (1 hay)
  then show ?case by simp
next
  case (2 n eedle)
  then show ?case by simp
next
  case IH: (3 n eedle h ay)
  let ?needle = "n#eedle"
  let ?hay = "h#ay"
  show ?case
  proof (cases "is_prefix ?needle ?hay")
    case prefix: True

    have 0: "naive_search ?needle ?hay"
      using prefix by auto

    have 1: "sublist ?needle ?hay"
      using is_prefix_correct prefix by blast

    show ?thesis using 0 1 by blast
  next
    case notprefix: False

    then have "naive_search ?needle ay = sublist ?needle ay"
      using IH notprefix by blast

    then show ?thesis
      by (metis is_prefix_correct naive_search.simps(3) sublist_Cons_right)
  qed
qed

end