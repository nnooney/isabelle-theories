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
fun var_aexp :: "aexp \<Rightarrow> aexp option" where
  "var_aexp (N n) = None" |
  "var_aexp (V x) = Some (V x)" |
  "var_aexp (Plus a1 a2) =
    (case (var_aexp a1, var_aexp a2) of
      (None, None) \<Rightarrow> None |
      (Some b1, None) \<Rightarrow> Some b1 |
      (None, Some b2) \<Rightarrow> Some b2 |
      (Some b1, Some b2) \<Rightarrow> Some (Plus b1 b2))"

fun fold_consts :: "aexp \<Rightarrow> aexp option" where
  "fold_consts (N n) = Some (N n)" |
  "fold_consts (V x) = None" |
  "fold_consts (Plus a1 a2) = 
    (case (fold_consts a1, fold_consts a2) of
      (None, None) \<Rightarrow> None |
      (Some (N n1), None) \<Rightarrow> Some (N n1) |
      (None, Some (N n2)) \<Rightarrow> Some (N n2) |
      (Some (N n1), Some (N n2)) \<Rightarrow> Some (N (n1 + n2)))"

lemma "var_aexp a = None \<Longrightarrow> fold_consts a \<noteq> None"
  apply (induction a)
  apply auto
  apply (case_tac "var_aexp a1", case_tac "var_aexp a2")
  apply auto
  oops

(*
proof (prove)
goal (2 subgoals):
 1. \<And>a1 a2 y ya.
       var_aexp a1 = None \<Longrightarrow>
       var_aexp a2 = None \<Longrightarrow>
       fold_consts a1 = Some y \<Longrightarrow>
       fold_consts a2 = Some ya \<Longrightarrow>
       \<exists>ya. (case y of
             N n1 \<Rightarrow>
               case fold_consts a2 of None \<Rightarrow> Some (N n1)
               | Some (N n2) \<Rightarrow> Some (N (n1 + n2))) =
            Some ya
 2. \<And>a1 a2 a.
       (var_aexp a2 = None \<Longrightarrow> \<exists>y. fold_consts a2 = Some y) \<Longrightarrow>
       (case var_aexp a2 of None \<Rightarrow> Some a | Some b2 \<Rightarrow> Some (Plus a b2)) = None \<Longrightarrow>
       var_aexp a1 = Some a \<Longrightarrow>
       \<exists>y. (case fold_consts a1 of
            None \<Rightarrow> case fold_consts a2 of None \<Rightarrow> None | Some (N n2) \<Rightarrow> Some (N n2)
            | Some (N n1) \<Rightarrow>
                case fold_consts a2 of None \<Rightarrow> Some (N n1)
                | Some (N n2) \<Rightarrow> Some (N (n1 + n2))) =
           Some y
*)

lemma "fold_consts a = None \<Longrightarrow> var_aexp a \<noteq> None"
  oops

lemma "var_aexp a = None \<Longrightarrow> fold_consts a = None \<Longrightarrow> False"
  apply (induction a)
  oops

(* Acts like Plus but handles optional aexps *)
fun merge_aexps :: "aexp option \<Rightarrow> aexp option \<Rightarrow> aexp" where
  "merge_aexps None None = (N 0)" |
  "merge_aexps None (Some n) = n" |
  "merge_aexps (Some a) None = a" |
  "merge_aexps (Some a) (Some n) = Plus a n"

lemma "aval a s = aval (merge_aexps (var_aexp a) (fold_consts a)) s"
  apply (induction a)
  apply auto
  oops

fun full_asimp :: "aexp \<Rightarrow> aexp" where
  "full_asimp (N n) = N n" |
  "full_asimp (V x) = V x" |
  "full_asimp (Plus a1 a2) = merge_aexps (var_aexp (Plus a1 a2)) (fold_consts (Plus a1 a2))"

lemma "aval (full_asimp a) s = aval a s"
  apply (induction a)
  apply (auto split: aexp.split)
  oops

(*
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
*)

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