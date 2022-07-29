theory Boyer_Moore                     
  imports Main Common "HOL-Library.Sublist"
begin


fun inits :: "'a list \<Rightarrow> 'a list list" where
  "inits l = prefixes l"

fun scanl :: "('b \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "scanl _ x [] = [x]" |
  "scanl f x (y#ys) = x # scanl f (f x y) ys"

fun scanr :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "scanr _ x [] = [x]" |
  "scanr f x (y#ys) = 
    (let partialResult = scanr f x ys 
      in (f y (hd partialResult)) # partialResult)"

(*
The Scanl lemma

  map (foldl op e) \<circ> inits = scanl op e
*)

lemma scanlI: "map (foldl op e) (inits l) = scanl op e l"
  by  (induction l arbitrary: op e) (auto simp add: comp_def)


fun fork :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> ('b*'c)" where
  "fork f g a = (f a, g a)"

(*
The Map-Filter-Fork lemma

  map f \<circ> filter p = map fst \<circ> filter snd \<circ> map (fork (f, p))

The Generalized Version:

  map f \<circ> filter (p \<circ> g) = map fst \<circ> filter (p \<circ> snd) \<circ> map (fork (f, g))
*)

(*More general*)
lemma MFF_Gen: "(map f \<circ> filter (p \<circ> g)) l = (map fst \<circ> filter (p \<circ> snd) \<circ> map (fork f g)) l"
  by (induction l) auto

(*Clearer*)
lemma MFF: "(map f \<circ> filter p) l = (map fst \<circ> filter snd \<circ> map (fork f p)) l"
  using MFF_Gen[of f id p l] by simp


(*
The Tupling lemma

  fork (foldl op1 e1, foldl op2 e2) = foldl op (e1, e2)
    where op (a,b) x = (op1 a x, op2 b x)
*)

lemma tupling: "(fork (foldl op1 e1) (foldl op2 e2)) l = (foldl (\<lambda>(a,b) x. (op1 a x, op2 b x)) (e1, e2)) l"
  by (induction l arbitrary: e1 e2) auto


fun endswith :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "endswith ws = (prefix (rev ws)) \<circ> rev"

fun step :: "(nat*'a list) \<Rightarrow> 'a \<Rightarrow> (nat*'a list)" where
  "step (n, sx) x = (n + 1, x#sx)"

fun matches0 where
  "matches0 ws = (map length) \<circ> (filter (endswith ws)) \<circ> inits"

fun matches1 where 
  "matches1 ws =
    (let sw = rev ws
      in map fst \<circ> filter ((prefix sw) \<circ> snd) \<circ> scanl step (0, []))"

value "matches0 ''abc'' ''sddabcdefg''"
value "matches1 ''abc'' ''sddabcdefg''"

fun flip :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'c)" where
  "flip f = (\<lambda>a b. f b a)"

find_theorems "fold" "foldl"
find_theorems "rev"

lemma "rev l = foldl (flip (#)) [] l"
  by (auto simp: foldl_conv_fold rev_conv_fold)

(*
  Trace through the transformations to show that the optimized matches1 performs the same 
  function as matches0.
*)
lemma "matches0 ws xs = matches1 ws xs"
  sorry

(* Apparently unnecessary (for now) *)
lemma endswith_sublist_at: 
  assumes "endswith ws xs"
    shows "sublist_at ws xs (length xs - length ws)"
  using assms
  apply (induction xs arbitrary: ws)
  apply (auto simp add: suffix_to_prefix[symmetric])
  apply (metis cancel_comm_monoid_add_class.diff_cancel length_Cons rev.simps(2) 
               rev_is_rev_conv sublist_at.simps(1) suffix_order.dual_order.refl)
  by (simp add: Suc_diff_le suffix_length_le)

(* Ugly proof but works (for now) *)
lemma BM_correct:
  assumes "idx \<in> set (matches0 needle hay)"
    shows "sublist_at needle hay (idx - length needle)"
  using assms
  apply (induction hay arbitrary: needle idx)
   apply (auto split: if_splits)
  apply (metis (no_types, lifting) Nil_is_rev_conv diff_zero imageI list.size(3) mem_Collect_eq prefix_bot.extremum)
  apply (metis (no_types, lifting) cancel_comm_monoid_add_class.diff_cancel imageI length_Cons mem_Collect_eq prefix_order.eq_refl rev.simps(2) rev_is_rev_conv sublist_at.simps(1))
  by (simp add: Suc_diff_le suffix_length_le suffix_to_prefix)

end
