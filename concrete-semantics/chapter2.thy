theory "chapter2"
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
  apply (induction x)
  apply auto
  done

lemma add_zero2 [simp]: "add x 0 = x"
  apply (induction x)
  apply auto
  done

lemma add_suc2 [simp]: "add x (Suc y) = Suc(add x y)"
  apply (induction x)
  apply auto
  done

theorem add_commut [simp]: "add x y = add y x"
  apply (induction x)
  apply auto
  done

fun double :: "nat \<Rightarrow> nat" where
  "double 0 = 0" |
  "double (Suc n) = Suc(Suc(double n))"

theorem double_add [simp]: "double x = add x x"
  apply (induction x)
  apply auto
  done

(* 2.3 *)
fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "count y [] = 0" |
  "count y (x # xs) = (if x = y then Suc(count y xs) else count y xs)"

(* Nonlinear patterns not allowed in sequential mode.
  "count x (Cons x xs) = Suc(count x xs)"
*)

theorem count_length [simp]: "count x xs \<le> length xs"
  apply (induction xs)
  apply auto
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
  apply (induction xs)
  apply auto
  done

theorem rev_rev [simp]: "reverse (reverse xs) = xs"
  apply (induction xs)
  apply auto
  done

(* 2.5 *)
fun sum_upto :: "nat \<Rightarrow> nat" where
  "sum_upto 0 = 0" |
  "sum_upto (Suc n) = (Suc n) + sum_upto n"

theorem sum_formula [simp]: "sum_upto x = x * (x + 1) div 2"
  apply (induction x)
  apply auto
  done

(* 2.6 *)
datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

(* list @ list or elem # list *)
fun contents :: "'a tree \<Rightarrow> 'a list" where
  "contents Tip = []" |
  "contents (Node l a r) =  a # (contents l) @ (contents r)"

fun sum_tree :: "nat tree \<Rightarrow> nat" where
  "sum_tree Tip = 0" |
  "sum_tree (Node l a r) = (sum_tree l) + a + (sum_tree r)"

theorem sum_tree_list [simp]: "sum_tree t = sum_list (contents t)"
  apply (induction t)
  apply auto
  done

(* 2.7 *)
fun preorder :: "'a tree \<Rightarrow> 'a list" where
  "preorder Tip = []" |
  "preorder (Node l a r) = a # (preorder l) @ (preorder r)"

fun postorder :: "'a tree \<Rightarrow> 'a list" where
  "postorder Tip = []" |
  "postorder (Node l a r) = (postorder l) @ (postorder r) @ [a]"

(* 
theorem fails to prove but doesn't complain with
preorder (Node l a r) = (preorder l) @ (preorder r)
postorder (Node l a r) = (postorder r) @ (postorder l)

I'm forgetting to include the "a" part of a node, but interesting
that I don't get a counter-example (because an empty list is
equal to an empty list).

after induction on t and apply auto, left with this goal.
goal (1 subgoal):
 1. \<And>t1 t2.
       preorder (mirror t1) = rev (postorder t1) \<Longrightarrow>
       preorder (mirror t2) = rev (postorder t2) \<Longrightarrow>
       rev (postorder t2) @ rev (postorder t1) =
       rev (postorder t1) @ rev (postorder t2
*)

fun mirror :: "'a tree \<Rightarrow> 'a tree" where
  "mirror Tip = Tip" |
  "mirror (Node l a r ) = Node (mirror r ) a (mirror l)"

theorem mirror_ordering [simp]: "preorder (mirror t) = rev (postorder t)"
  apply (induction t)
  apply auto
  done

(* 2.8 *)
fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "intersperse a [] = []" |
  "intersperse a (x # xs) = (x # [a]) @ (intersperse a xs)"

(* 
Applying a function to an interspersed list is the same as applying the function
to the elements, then interspersing.
*)
theorem intersperse_over_map [simp]: "map f (intersperse a xs) = intersperse (f a) (map f xs)"
  apply (induction xs)
  apply auto
  done

(* 2.9 *)

(* How do I identify that a function is tail-recursive? 
The only difference between this and add is where the Suc goes. 

Ah, the example says "in the recursive case, itadd needs to call
itself directly". So no shenanigans on the outermost expression. *)
fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "itadd 0 n = n" |
  "itadd (Suc m) n = itadd m (Suc n)"

theorem itadd_is_add [simp]: "itadd m n = add m n"
(* Fancy argument sorcery? Why include a colon? *)
  apply (induction m arbitrary: n)
  apply auto
  done

(* So now I'm told not to litter [simp] everywhere, only for
actual simplifying equations, at risk of exponential blow up! *)

(* 2.10 *)
datatype tree0 = Tip | Node tree0 tree0

fun nodes :: "tree0 \<Rightarrow> nat" where
  "nodes Tip = 1" |
  "nodes (Node l r) = 1 + (nodes l) + (nodes r)"

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
  "explode 0 t = t" |
  "explode (Suc n) t = explode n (Node t t)"

(* create 2^n copies of t and then 2^n-1 nodes to connect all the
   copies *)
theorem explode_size: "nodes (explode n t) = 2 ^ n * nodes t + 2 ^ n - 1"
  apply (induction n arbitrary: t)
  (* boost auto with the algebra_simps deduction *)
  apply (auto simp add: algebra_simps)
  done

(* 2.11 *)
datatype exp = Var | Const int | Add exp exp | Mult exp exp

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
  "eval Var n = n" |
  "eval (Const x) n = x" |
  "eval (Add x y) n = (eval x n) + (eval y n)" |
  "eval (Mult x y) n = (eval x n) * (eval y n)"

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
  "evalp [] n = 0" |
  "evalp (x # xs) n = x + n * (evalp xs n)"

(* sum corresponding indices of lists *)
fun elem_sum :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "elem_sum [] y = y" |
  "elem_sum x [] = x" |
  "elem_sum (x # xs) (y # ys) = (x + y) # elem_sum xs ys"

(* multiply each index by n *)
fun scalar_mult :: "int  \<Rightarrow> int list \<Rightarrow> int list" where
  "scalar_mult k [] = []" |
  "scalar_mult k (x # xs) = (k * x) # scalar_mult k xs"

(* shift and multiply *)
fun poly_mult :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "poly_mult [] ys = []" |
  "poly_mult (x # xs) ys = elem_sum (scalar_mult x ys) (poly_mult xs (0 # ys))"

fun coeffs :: "exp \<Rightarrow> int list" where
  "coeffs Var = [0, 1]" |
  "coeffs (Const x) = [x]" |
  "coeffs (Add x y) = elem_sum (coeffs x) (coeffs y)" |
  "coeffs (Mult x y) = poly_mult (coeffs x) (coeffs y)"

lemma evalp_elem_sum [simp]: "evalp (elem_sum xs ys) n = evalp xs n + evalp ys n"
  apply (induction rule: elem_sum.induct)
  apply (auto simp add: algebra_simps)
  done

lemma evalp_scalar_mult [simp]: "evalp (scalar_mult k xs) n = k * evalp xs n"
  (* Doesn't work with
  apply (induction rule: scalar_mult.induct) *)
  apply (induction xs arbitrary:k)
  apply (auto simp add: algebra_simps)
  done

lemma evalp_poly_mult [simp]: "evalp (poly_mult xs ys) n = evalp xs n * evalp ys n"
  apply (induction rule: poly_mult.induct)
  apply (auto simp add: algebra_simps)
  done

theorem coeffs_preserves_eval: "evalp (coeffs e) x = eval e x"
  apply (induction e)
  apply auto
  done

(*
Function writing through counter-examples:

Problem 1:
Auto Quickcheck found a counterexample:
  e = Var
  x = - 1
Evaluated terms:
  evalp (coeffs e) x = 1
  eval e x = - 1
My investigation:
  culprit: "evalp (x # xs) n = n * x + n * (evalp xs n)"
  example: 
    "evalp [0, 1]" expands to 
    "(n * 0 + n * (n * 1 + n * (0)))"; simplifies to
    "n^2"
  reason: I have too many n's in my definition.
  fix: "evalp (x # xs) n = x + n * (evalp xs n)"

Problem 2:
Auto Quickcheck found a counterexample:
  e = Add Var Var
  x = - 2
Evaluated terms:
  evalp (coeffs e) x = 0
  eval e x = - 4
My investigation:
  cool, the counterexample is using add; I must have the Var and
  Const cases right. Back in math class, adding polynomials is
  the same as adding matching coefficients, so write elem_sum.

Problem 3:
Auto Quickcheck found a counterexample:
  e = Mult Var Var
  x = - 2
Evaluated terms:
  evalp (coeffs e) x = 0
  eval e x = 4
My investigation:
  cool, the counterexample is using mult; I must have Add right.
  Back in math class, multiplying polynomials requires some
  FOIL-ing. Right shift N and multiply by index N. Write
  scalar_mult and poly_mult.

No more problems, time to prove. Apply auto doesn't work. Onto
the lemmas:

Lemma 1: "evalp (elem_sum xs ys) n = evalp xs n + evalp ys n"

Lemma 2: "evalp (poly_mult xs ys) n = evalp xs n * evalp ys n
  requires a scalar_mult lemma

Lemma 1.5: "evalp (scalar_mult k xs) n = k * evalp xs n"
  for some reason, this doesn't solve when using rule:scalar_mult.induct

After the lemmas are in place, the theorem is proved with 
*)

end