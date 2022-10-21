theory "chapter3"
  imports Main
begin

type_synonym vname = string

datatype aexp = N int | V vname | Plus aexp aexp

type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
  "aval (N n) s = n" |
  "aval (V x) s = s x" |
  "aval (Plus a1 a2) s = aval a1 s + aval a2 s"

value "aval (Plus (N 3) (V ''x'')) (\<lambda>x. 0)"

fun asimp_const :: "aexp \<Rightarrow> aexp" where
  "asimp_const (N n) = N n" |
  "asimp_const (V x) = V x" |
  "asimp_const (Plus a1 a2) =
    (case (asimp_const a1, asimp_const a2) of
      (N n1, N n2) \<Rightarrow> N (n1 + n2) |
      (b1, b2) \<Rightarrow> Plus b1 b2)"

(* asimp_const preserves evaluation *)
lemma "aval (asimp_const a) s = aval a s"
  apply (induction a)
  apply (auto split: aexp.split)
  done

fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
  "plus (N n1) (N n2) = N (n1 + n2)" |
  "plus (N n) a = (if n = 0 then a else Plus (N n) a)" |
  "plus a (N n) = (if n = 0 then a else Plus a (N n))" |
  "plus a1 a2 = Plus a1 a2"

lemma aval_plus: "aval (plus a1 a2) s = aval a1 s + aval a2 s"
  apply (induction a1 rule: plus.induct)
  apply (induction a2 rule: plus.induct)
  apply auto
  done

fun asimp :: "aexp \<Rightarrow> aexp" where
  "asimp (N n) = N n" |
  "asimp (V x) = V x" |
  "asimp (Plus a1 a2) = plus (asimp a1) (asimp a2)"

(* asimp preserves evaluation *)
lemma "aval (asimp a) s = aval a s"
  apply (induction a)
  apply (auto simp: aval_plus)
  done

(* 3.1 *)
fun optimal :: "aexp \<Rightarrow> bool" where
  "optimal (N n) = True" |
  "optimal (V x) = True" |
  "optimal (Plus (N n1) (N n2)) = False" |
  "optimal (Plus a1 a2) = ((optimal a1) \<and> (optimal a2))"

theorem asimp_const_optimal: "optimal (asimp_const a)"
  apply (induction a)
  apply (auto split: aexp.split)
  done

(* 3.2 *)
fun full_plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
  (* Ways to combine two constants *)
  "full_plus (N n1) (N n2) = N (n1 + n2)" |
  "full_plus (Plus (N n1) a) (N n2) = Plus a (N (n1 + n2))" |
  "full_plus (Plus a (N n1)) (N n2) = Plus a (N (n1 + n2))" |
  "full_plus (N n1) (Plus (N n2) a) = Plus a (N (n1 + n2))" |
  "full_plus (N n1) (Plus a (N n2)) = Plus a (N (n1 + n2))" |
  (* Ways to shift constants right *)
  "full_plus (Plus a1 (N n1)) a2 = Plus (Plus a1 a2) (N n1)" |
  "full_plus a1 (Plus a2 (N n1)) = Plus (Plus a1 a2) (N n1)" |
  "full_plus (Plus (N n1) a1) (Plus (N n2) a2) = Plus (Plus a1 a2) (N (n1 + n2))" |
  (* Everything else *)
  "full_plus a1 a2 = Plus a1 a2"

lemma aval_full_plus: "aval (full_plus a1 a2) s = aval a1 s + aval a2 s"
  apply (induction rule: full_plus.induct)
  apply auto
  done

fun full_asimp :: "aexp \<Rightarrow> aexp" where
  "full_asimp (N n) = N n" |
  "full_asimp (V x) = V x" |
  "full_asimp (Plus a1 a2) = full_plus (full_asimp a1) (full_asimp a2)"

value "full_asimp (Plus (N 1) (Plus (V ''x'') (N 2)))"
value "full_asimp (Plus (N (- 2)) (Plus (N (- 1)) (V [])))"

lemma "aval (full_asimp a) s = aval a s"
  apply (induction a)
  apply (auto simp: aval_full_plus)
  done

(* Great, we preserved that it doesn't change evaluation, but can we
  prove that it's also optimal?  *)

fun count_n :: "aexp \<Rightarrow> int" where
  "count_n (N n) = 1" |
  "count_n (V x) = 0" |
  "count_n (Plus a1 a2) = (count_n a1) + (count_n a2)"

(* Adding more cases to full_plus is making the evaluation take awhile. There has
  to be a better way to write the simplification rules for full_plus. *)
theorem full_asimp_optimal: "count_n (full_asimp a) \<le> 1"
  oops

end