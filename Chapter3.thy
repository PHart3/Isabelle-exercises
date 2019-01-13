theory Chapter3
imports Main Chapter2
begin


(* Exercise 3.1 *)

datatype 'a tree = Tip | Node " 'a tree" 'a " 'a tree"

fun set :: " 'a tree \<Rightarrow> 'a set" where
"set Tip = {}"
| "set (Node l a r) = {a} \<union> (set l) \<union> (set r)"

fun leq_tree :: "int tree \<Rightarrow> int \<Rightarrow> bool" where
"leq_tree Tip x = True"
| "leq_tree (Node l a r) x = ((a \<le> x) & (leq_tree l x) & (leq_tree r x))"

fun sg_tree :: "int tree \<Rightarrow> int \<Rightarrow> bool" where
"sg_tree Tip x = True"
| "sg_tree (Node l a r) x = ((x < a) & (sg_tree l x) & (sg_tree r x))"

fun ord :: "int tree \<Rightarrow> bool" where
"ord Tip = True"
| "ord (Node l a r) = ( (ord l) & (ord r) & (leq_tree l a) & (sg_tree r a)  ) "

fun ins :: "int \<Rightarrow> int tree \<Rightarrow> int tree" where
"ins x Tip = Node Tip x Tip"
| "ins x (Node l a r) = ( 
    if x = a then Node l a r
    else (if x < a then Node (ins x l) a r  else Node l a (ins x r)) 
)"

lemma ins_spec : "set (ins x t) = {x} \<union> set t"
  apply(induction t arbitrary: x)
   apply(auto)
  done

lemma tree_ord_prop1 [simp] : "leq_tree t1 x2  \<Longrightarrow> x < x2 \<Longrightarrow> leq_tree (ins x t1) x2"
  apply(induction t1 arbitrary: x2 x)
   apply(auto)
  done

lemma trich_int_prop : "\<not> x < x2 \<Longrightarrow> x \<noteq> x2 \<Longrightarrow> x2 < (x::int)"
  apply(auto)
  done

lemma tree_ord_prop2 [simp]  : " sg_tree t2 x2 \<Longrightarrow> x2 < x \<Longrightarrow> sg_tree (ins x t2) x2"
  apply(induction t2 arbitrary: x2 x)
   apply(auto)
  done

lemma ord_spec : "ord t \<Longrightarrow>  ord (ins x t)"
  apply(induction t)
   apply(auto)
  done

(* Exercise 3.2 *)

inductive palindrome :: " 'a list \<Rightarrow> bool " where
empty : " palindrome Nil"
| singleton : "palindrome [a]"
| palin_append : " palindrome xs \<Longrightarrow> palindrome (a # xs @ [a])"

lemma palindrome_correct : " palindrome xs \<Longrightarrow> rev xs = xs "
  apply(induction xs rule: palindrome.induct)
    apply(auto)
  done

(* Exercise 3.3 *)

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where 
refl : "star r x x" |
step : " r x y  \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

inductive star' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where 
refl' : "star' r x x" |
step' : "star' r x y \<Longrightarrow> r y z \<Longrightarrow> star' r x z"

lemma star_step_symm [intro] : "star r x y \<Longrightarrow> r y z \<Longrightarrow> star r x z"
  apply(induction rule: star.induct)
   apply(rule step)
    apply(auto)
   apply(rule refl)
  apply(rule step)
   apply(auto)
  done

lemma star'_step'_symm [intro] : "  star' r y z \<Longrightarrow> r x y  \<Longrightarrow>  star' r x z"
 apply(induction rule: star'.induct)
   apply(rule step')
    apply(auto)
   apply(rule refl')
  apply(rule step')
   apply(auto)
  done

lemma star_star'_equiv : "star' r x y = star r x y"
  apply(rule)
   apply(induction rule: star'.induct)
    apply(simp add: refl)
   apply(auto)
  apply(induction rule: star.induct)
   apply(rule refl')
  apply(auto)
  done

(* Exercise 3.4 *)

inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
 iter0: "iter r 0 x x"
| iter1: "r x y \<Longrightarrow>  iter r (Suc 0) x y"
| iter_step: "iter r n x y \<Longrightarrow> iter r m y z \<Longrightarrow> iter r (n + m) x z"

lemma trivial [simp] : "  iter r n y z \<Longrightarrow> \<exists> m.  iter r m y z"
  by auto

lemma iter_spec : " star r x y \<Longrightarrow> EX n.  iter r n x y"
  apply(induction rule: star.induct)
   apply(rule)
   apply(rule iter0)
  apply(auto)
  apply(rule)
  apply(rule iter_step)
   apply(rule iter1)
   apply(assumption)
  apply(rule)
   apply(auto)
  apply(rule iter0)
  done
  
(* Exercise 3.5 *)

datatype alpha = a | b | c

type_synonym word = "alpha list"

inductive S :: "word  \<Rightarrow> bool" where
Sempty : "S Nil"
| Sconj : " S w \<Longrightarrow> S ( a # w @ [b]) "
| Sdouble : " S w \<Longrightarrow> S u  \<Longrightarrow> S (w @ u)"

inductive T :: "word  \<Rightarrow> bool" where
Tempty : "T Nil"
| Talt : " T w \<Longrightarrow> T u \<Longrightarrow> T ( w @ [a] @ u @ [b]) "

lemma T_append [simp] : " T u \<Longrightarrow> T w \<Longrightarrow> T(w @ u) "
  apply(induction rule: T.induct)
   apply(simp)
  apply(metis T.simps app_assoc) (* by Sledgehammer *)
  done
  

lemma S_T_equiv : " S w = T w "
  apply(rule)
   apply(induction rule: S.induct)
     apply(rule Tempty)
    apply(auto)
   apply (metis T.simps Tempty append.simps(1) append.simps(2)) (* by Sledgehammer *)
  apply(induction rule: T.induct)
   apply(rule)
  apply(auto)
  apply(simp add: Sconj Sdouble)
  done
  
  
end