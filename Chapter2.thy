theory Chapter2
  imports Main
begin


(* Exercise 2.1  *)

value "1 + (2::nat)"
value "1 + (2::int)"
value "1 - (2::nat)"
value "1 - (2::int)"

(* Exercise 2.2  *)

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where "add 0 n = n" |
"add (Suc m) n = Suc(add m n)"

lemma add_assoc [simp] : "add (add p q) r  = add p (add q r)"
  apply(induction p)
   apply(auto)
  done

lemma add_02 [simp] : "add m 0 = m" apply(induction m)
apply(auto)
done

lemma add_plus1 [simp] : "Suc (add q p) = add q (Suc p)"
  apply(induction q)
   apply(auto)
  done

lemma add_comm [simp] : "add p q = add q p"
  apply(induction p)
   apply(auto)
  done

fun double :: "nat \<Rightarrow> nat" where
"double 0 = 0"
| "double (Suc n) = 2 + (double n)"

lemma double_correct [simp] : "double n = add n n"
  apply(induction n)
   apply(auto)
  done

(* Exercise 2.3 *)

fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
"count x Nil = 0"
| "count x (Cons t ts) = 1 + (count x ts)"

lemma leq_count_length : "count x xs \<le> length xs"
  apply(induction xs)
   apply(auto)
  done

(* Exercise 2.4 *)

fun snoc :: " 'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"snoc Nil x = [x]"
|"snoc (Cons t ts) x = Cons t (snoc ts x)"

fun reverse :: " 'a list \<Rightarrow> 'a list" where
"reverse Nil = Nil"
|"reverse (Cons t ts) = snoc (reverse ts) t"

lemma app_assoc [simp]: "(xs @ ys) @ zs = xs @ (ys @ zs)" 
  apply(induction xs)
  apply(auto)
  done

lemma snoc_add1 [simp] : "snoc xs x = xs @ [x]"
  apply(induction xs)
   apply(auto)
  done

lemma rev_app_distr [simp] : "reverse (xs @ ys) = (reverse ys) @ reverse(xs)"
  apply(induction xs)
   apply(auto)
  done

lemma reverse_correct : "reverse (reverse xs) = xs"
  apply(induction xs)
   apply(auto)
  done

(* Exercise 2.5 *)

fun sum_upto  :: "nat \<Rightarrow> nat" where
"sum_upto 0 = 0"
| "sum_upto (Suc n) = (n + (sum_upto n)) + 1"

lemma sum_upto_correct : "sum_upto n = n * (n + 1) div 2"
  apply(induction n)
  apply(auto)
  done

(* Exercise 2.6 *)

datatype 'a tree = Tip | Node " 'a tree" 'a " 'a tree"

fun contents :: " 'a tree \<Rightarrow> 'a list " where
" contents Tip = Nil "
| " contents (Node l a r) =  a # ((contents l) @ (contents r))"

fun sum_tree :: "nat tree \<Rightarrow> nat" where
" sum_tree Tip = 0 "
| " sum_tree (Node l a r) = a + (sum_tree l) + (sum_tree r)"

lemma sum_tree_correct : "sum_tree t = sum_list(contents t)"
  apply(induction t)
   apply(auto)
  done

(* Exercise 2.7 *)

datatype 'a tree2 = Tip2 'a | Node " 'a tree2" 'a " 'a tree2"

fun mirror2 :: " 'a tree2 \<Rightarrow> 'a tree2 " where
 "mirror2 (Tip2 a) = Tip2 a"
| "mirror2 (Node l a r) = Node (mirror2 r) a (mirror2 l)"

fun pre_order :: " 'a tree2 \<Rightarrow> 'a list" where
"pre_order (Tip2 a) = [a]"
| "pre_order (Node l a r) = a # ((pre_order l) @ (pre_order r))"

fun post_order :: " 'a tree2 \<Rightarrow> 'a list" where
"post_order (Tip2 a) = [a]"
| "post_order (Node l a r) = (post_order l) @ (post_order r) @ [a] "

lemma tree2_orders_correct : "pre_order(mirror2 t) = rev(post_order t)"
  apply(induction t)
   apply(auto)
  done

(* Exercise 2.8 *)

fun intersperse :: " 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"intersperse a Nil = [a]"
| "intersperse a (Cons x Nil) = [x]"
| "intersperse a (Cons x xs) = [x, a] @ (intersperse a xs)"

lemma intersperse_correct : " map f (intersperse a xs) = intersperse (f a) (map f xs)"
  apply(induction a xs rule: intersperse.induct)
    apply(auto)
  done

(* Exercise 2.9 *)

fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
 "itadd 0 m  = m"
| "itadd (Suc 0) m = Suc m"
| "itadd (Suc n) m = itadd (Suc 0) (itadd n m)"

lemma add_suc0 : "Suc m = add m (Suc 0)"
  apply(induction m)
   apply(auto)
  done

lemma itadd_correct : "itadd n m = add n m"
  apply(induction n m rule: itadd.induct)
    apply(auto)
  apply (rule add_suc0)
  done

(* Exercise 2.10 *)

datatype tree0 = Tip0 | Node0 "tree0" "tree0"

fun nodes :: "tree0 \<Rightarrow> nat" where
"nodes Tip0 = 1"
| "nodes (Node0 l r) = nodes l + nodes r + 1"

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where 
"explode 0 t = t" 
|"explode (Suc n) t = explode n (Node0 t t)"

lemma exploded_tree_size: "nodes(explode n t) = (2^n)*(nodes t) + (2^n) - 1"
apply(induct n arbitrary: t)
apply(auto simp add: algebra_simps)
  done

(* Exercise 2.11 *)

datatype exp = Var | Const int | Add exp exp | Mult exp exp

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
"eval Var x = x"
| "eval (Const k) x = k"
| "eval (Add u v) x = (eval u x) + (eval v x)"
| "eval (Mult u v) x = (eval u x) * (eval v x)"

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
"evalp Nil k = 0"
| "evalp (Cons x xs) k = x + (k * (evalp xs k))"


fun coeffs_add :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"coeffs_add Nil ys = ys"
| "coeffs_add xs Nil = xs"
| "coeffs_add (Cons x xs) (Cons y ys) = (x + y) # (coeffs_add xs ys)"

value "coeffs_add [0,1,4,5] [1,0,5]"

fun MultByC :: "int \<Rightarrow> int list \<Rightarrow> int list" where
"MultByC c Nil = Nil"
| "MultByC c (Cons x xs) = (c * x) # (MultByC c xs)"

fun coeffs_mult :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"coeffs_mult Nil ys = Nil"
| "coeffs_mult (Cons x xs) ys = coeffs_add (MultByC x ys) (0 # (coeffs_mult xs ys))"

fun coeffs :: "exp \<Rightarrow> int list" where
"coeffs Var = [0,1]"
| "coeffs (Const k) = [k]"
| "coeffs (Add e1 e2) = coeffs_add (coeffs e1) (coeffs e2)"
| "coeffs (Mult e1 e2) = coeffs_mult (coeffs e1) (coeffs e2)"

lemma coeffs_add_correct [simp] : "evalp (coeffs_add xs ys) x = (evalp xs x) + (evalp ys x)"
  apply(induction xs ys arbitrary: x rule: coeffs_add.induct)
    apply(auto simp add: algebra_simps)
  done

lemma factor_by_const_prop : " evalp (MultByC a ys) x = a * evalp ys x"
  apply(induction ys)
   apply(auto simp add: algebra_simps)
  done

lemma coeffs_mult_correct [simp] : "evalp (coeffs_mult xs ys) x = (evalp xs x) * (evalp ys x)"
  apply(induction xs arbitrary: ys  x)
   apply(auto simp add: algebra_simps)
  apply(rule factor_by_const_prop)
  done


lemma coeffs_correct : "evalp (coeffs e) x = eval e x"
  apply(induction e arbitrary: x)
     apply(auto simp add: algebra_simps)
  done


end