theory "concrete-semantics"
  imports Main
begin

(* 2.1 *)
value "1 + (2::nat)"
value "1 + (2::int)"
value "1 - (2::nat)"
value "1 - (2::int)"

(* 2.2 *)
fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
 "add 0 n = n" |
 "add (Suc m) n = Suc(add m n)"

theorem add_assoc [simp]: "add (add x y) z = add x (add y z)"
  apply(induction x)
   apply(auto)
  done

lemma add_zero2 [simp]: "add x 0 = x"
  apply(induction x)
   apply(auto)
  done

lemma add_suc2 [simp]: "add x (Suc y) = Suc(add x y)"
  apply(induction x)
   apply(auto)
  done

theorem add_commut [simp]: "add x y = add y x"
  apply(induction x)
   apply(auto)
  done

fun double :: "nat \<Rightarrow> nat" where
 "double 0 = 0" |
 "double (Suc n) = Suc(Suc(double n))"

theorem double_add [simp]: "double x = add x x"
  apply(induction x)
   apply(auto)
  done

(* 2.3 *)
fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
 "count y [] = 0" |
 "count y (x # xs) = (if x = y then Suc(count y xs) else count y xs)"

(* Nonlinear patterns not allowed in sequential mode.
 "count x (Cons x xs) = Suc(count x xs)"
*)

theorem count_length [simp]: "count x xs \<le> length xs"
  apply(induction xs)
   apply(auto)
  done

(* 2.4 *)
fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
 "snoc [] y = [y]" |
 "snoc (x # xs) y = x # (snoc xs y)"

fun reverse :: "'a list \<Rightarrow> 'a list" where
 "reverse [] = []" |
 "reverse (x # xs) = snoc (reverse xs) x"

(*
lemma rev_snoc: "reverse (snoc xs x) = x # xs"
Auto Quickcheck found a counterexample:
  xs = [a\<^sub>1, a\<^sub>2]
  x = a\<^sub>1
Evaluated terms:
  reverse (snoc xs x) = [a\<^sub>1, a\<^sub>2, a\<^sub>1]
  x # xs = [a\<^sub>1, a\<^sub>1, a\<^sub>2]
*)

(* don't forget [simp] for later lemma/theorems! *)
lemma rev_snoc [simp]: "reverse (snoc xs x) =  x # reverse xs"
  apply(induction xs)
   apply(auto)
  done

theorem rev_rev [simp]: "reverse (reverse xs) = xs"
  apply(induction xs)
   apply(auto)
  done

(* 2.5 *)
fun sum_upto :: "nat \<Rightarrow> nat" where
 "sum_upto 0 = 0" |
 "sum_upto (Suc n) = (Suc n) + sum_upto n"

theorem sum_formula [simp]: "sum_upto x = x * (x + 1) div 2"
  apply(induction x)
   apply(auto)
  done


end