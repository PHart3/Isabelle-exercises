theory Chapter4
  imports Main Chapter2
begin


(* Exercise 4.1 *)

lemma 
  assumes T: "ALL x y. T x y \<or> T y x" 
and 
A: "ALL x y. A x y \<and> A y x \<longrightarrow> x = y" 
and 
TA: "ALL x y. T x y \<longrightarrow> A x y" 
and 
"A x y"
shows "T x y"
proof -
  from assms show  "T x y" by blast
qed

(* Exercise 4.2 *)

lemma "EX ys zs. xs = ys @ zs \<and> (length ys = length zs \<or> length ys = length zs + 1)"
proof -
  consider (odd) "odd (length xs)" | (even) "even (length xs)" by auto
  then show ?thesis
  proof cases
    case odd
    let ?l1 =  " take ((length xs + 1) div 2) xs" 
    let ?l2 = " drop ((length xs + 1) div 2) xs" 
    have 1: "xs = ?l1 @ ?l2" by auto
    have 2: " length ?l1 = length ?l2 + 1"  
    by (smt "1" add.commute add_diff_cancel_right' diff_diff_left dvd_mult_div_cancel length_append 
length_drop mult_2 odd odd_even_add odd_one odd_succ_div_two)
    from 1 have "xs = ?l1 @ ?l2 \<and> ( length ?l1 = length ?l2 + 1)" using 2 by auto
    thus ?thesis by blast
  next
    case even
    let ?l1 =  " take ((length xs) div 2) xs" 
    let ?l2 = " drop ((length xs) div 2) xs" 
    have 1: "xs = ?l1 @ ?l2" by auto
    have 2: " length ?l1 = length ?l2"  
    using even by auto
  from 1 have "xs = ?l1 @ ?l2 \<and> ( length ?l1 = length ?l2)" using 2 by auto
  thus ?thesis by blast
qed
qed

(* Exercise 4.3 *)

inductive ev :: "nat \<Rightarrow> bool" where 
ev0: "ev 0" |
evSS: "ev n \<Longrightarrow> ev(n+2)"

lemma 
  assumes a: "ev(Suc(Suc n))" 
  shows "ev n"
proof -
  from a show ?thesis
  proof cases
    case ev0
  next
    case (evSS n)
    then show ?thesis by auto
  qed
qed
   

(* Exercise 4.4 *)

lemma " \<not> ev (Suc (Suc (Suc 0))) "
proof
  assume a: " ev (Suc (Suc (Suc 0)))"
  thus "False"
  proof cases
    case ev0
next
  case (evSS n)
  hence "n = (Suc 0) " by arith
  hence "ev (Suc 0)" using evSS by auto
  thus "False"  
  using ev.cases by auto 
qed
qed

(* Exercise 4.5 *)

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where 
refl : "star r x x" |
step : " r x y  \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
 iter0: "iter r 0 x x"
| iter1: "r x y \<Longrightarrow>  iter r (Suc 0) x y"
| iter_step: "iter r n x y \<Longrightarrow> iter r m y z \<Longrightarrow> iter r (n + m) x z"


lemma star_trans: "star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
    proof(induction rule: star.induct)
      case (refl x)
      then show ?case by auto
    next
      case (step x y z)
      then show ?case by (metis star.step)
    qed

lemma "iter r n x y \<Longrightarrow> star r x y "
proof(induction rule: iter.induct)
case (iter0 x)
  then show ?case by (simp add: star.refl)
next
case (iter1 x y)
  then show ?case
  proof
    show "star r y y" by (simp add: star.refl)
  qed
next
  case (iter_step n x y m z)
  from iter_step(3-4) show ?case using star_trans by fastforce
qed

(* Exercise 4.6 *)

fun elems :: " 'a list \<Rightarrow> 'a set " where
"elems Nil = {}"
| "elems (Cons x xs) = {x} Un (elems xs)"

lemma "x : elems xs \<Longrightarrow> EX ys zs. xs = ys @ x # zs \<and> x \<notin> elems ys "
proof(induction xs)
case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then show ?case
  proof (cases "x = a")
    case True
    then show ?thesis by fastforce
  next
    case False
    hence "x : elems xs"
    using Cons.prems by auto
  hence " \<exists>ys zs. xs = ys @ x # zs \<and> x \<notin> elems ys" using Cons by auto
  then obtain ys zs where " xs = ys @ x # zs \<and> x \<notin> elems ys" by blast
  hence "a # xs = a # ys @ x # zs \<and> x \<notin> elems (a # ys)" using False by auto
  thus ?thesis  
  by (metis append_Cons)
  qed
qed

(* Exercise 4.7 *)

datatype alpha = a | b

type_synonym word = "alpha list"

inductive S :: "word  \<Rightarrow> bool" where
Sempty : "S Nil"
| Sconj : " S w \<Longrightarrow> S ( a # w @ [b]) "
| Sdouble : " S w \<Longrightarrow> S u  \<Longrightarrow> S (w @ u)"

fun balanced :: "nat \<Rightarrow> word \<Rightarrow> bool" where
"balanced 0 Nil = True"
| "balanced n (Cons a w) = balanced (Suc n) w"
| "balanced (Suc n) (Cons b w) = balanced n w"
| "balanced _ _ = False"


lemma replicate_prop1 : "replicate (Suc n) a @ b # w = (replicate n a) @ a # b # w"
proof -
  show ?thesis  
  by (simp add: replicate_app_Cons_same)
qed

lemma Insert_ab: 
  assumes u: "S u" 
  shows "\<And> v w. u = v @ w \<Longrightarrow> S (v @ (a # (b # w))) "
using u
proof(induct)
case (Sempty) thus ?case
  using S.Sempty Sconj by fastforce
next
case (Sconj u)
have uS: "S u"
and IH: "\<And> v w. u = v @ w \<Longrightarrow> S (v @ a # b # w) " by fact+
  have asm: "a # u @ [b] = v @ w" using Sconj by blast
show "S(v @ a # b # w)"
proof (cases v)
case Nil
hence "w = a # u @ [b]" using asm  
  using Sconj.prems by simp
hence "S w" using uS  
  using S.Sconj by auto
hence "S ([a,b] @ w)"  
  using S.Sconj Sdouble Sempty by force
thus ?thesis using Nil by simp
next
case (Cons x v')
show ?thesis
proof (cases w rule:rev_cases)
case Nil
from uS have "S((a # u @ [b]) @ [a,b])"  
  by (metis S.Sconj Sdouble Sempty append_Nil)
thus ?thesis using Nil Cons asm by auto
next
case (snoc w' y)
hence u: "u = v' @ w'" and [simp]: "x = a & y = b"
  using Cons asm by auto
have "S(v' @ a # b # w')" using Sconj.hyps and u
hence "S(a # (v' @ a # b # w') @ [b])" using Sconj.prems by blast
thus ?thesis using Sconj.prems  
  by (metis S.simps \<open>x = a \<and> y = b\<close> append.assoc append_Cons local.Cons snoc)
qed
qed
next
case (Sdouble v' w')
have v'S: "S v'" and w'S: "S w'"
and IHv: "\<And> v w. v' = v @ w \<Longrightarrow> S(v @ a # b # w)"
and IHw: "\<And> v w. w' = v @ w \<Longrightarrow> S(v @ a # b # w)" by fact+
have asm: "v' @ w' = v @ w" using Sdouble by blast
then obtain r where "v' = v @ r \<and> r @ w' = w \<or> v' @ r = v \<and> w' = r @ w" (is "?A \<or> ?B")
by (auto simp:append_eq_append_conv2)
thus "S(v @ a # b # w)"
proof
assume A: ?A
hence "S(v @ a # b # r)" using IHv using Sdouble.prems by blast
hence "S((v @ a # b # r) @ w')" using w'S S.Sdouble S.intros(3) by blast
thus ?thesis using A by auto
next
assume B: ?B
  hence "S(r @ a # b # w)" using Sdouble.prems IHw by blast
  have "S(v' @ (r @ a # b # w))" using v'S S.Sdouble S.intros(3) \<open>S (r @ a # b # w)\<close> by blast
thus ?thesis using B by auto
qed
qed



lemma balanced_add_b: "balanced n w \<Longrightarrow> balanced (Suc n) (w @ [b])"
proof(induction n w rule: balanced.induct)
case 1
  then show ?case by auto
next
case (2 n w)
  then show ?case by simp
next
  case (3 n w)
then show ?case by simp
next
  case ("4_1" v)
  then show ?case by simp
next
case ("4_2" va)
then show ?case by simp
qed

lemma balanced_append: "balanced n x \<Longrightarrow> balanced 0 y \<Longrightarrow> balanced n (x @ y)"
proof(induction n x rule: balanced.induct)
case 1
  then show ?case by auto
next
  case (2 n w)
then show ?case by simp
next
  case (3 n w)
  then show ?case by simp
next
case ("4_1" v)
then show ?case by simp
next
  case ("4_2" va)
  then show ?case by simp
qed

lemma replicate_pinch: "m < n \<Longrightarrow> replicate n x = replicate m x @ replicate (n - m) x"
   
  by (metis add_diff_inverse_nat less_imp_not_less replicate_add)

lemma append_pinch: 
"length zs < length xs \<Longrightarrow> xs @ ys = zs @ ws \<Longrightarrow> EX us. xs = zs @ us"
  by (metis append_eq_append_conv_if id_take_nth_drop nat_less_le)



theorem "balanced n w = S (replicate n a @ w) "
proof
  show "balanced n w \<Longrightarrow> S (replicate n a @ w)"
  proof(induction n w rule: balanced.induct)
case 1
  then show ?case  
  by (simp add: Sempty)
next
  case (2 n w)
  then show ?case  
  by (simp add: replicate_app_Cons_same)
next
  case (3 n w)
  hence c1: "S (replicate n a @ w)" by simp
  have c2: "replicate (Suc n) a @ b # w = replicate n a @ a # b # w" using replicate_prop1 by auto
  have  c3: "S(replicate n a @ a # b # w)" using Insert_ab c1 by simp
  thus ?case using c2 by auto
next
  case ("4_1" v)
  then show ?case by simp
next
  case ("4_2" va)
  then show ?case by simp
qed
next
  show "S (replicate n a @ w) \<Longrightarrow> balanced n w"
  proof(induction "replicate n a @ w" arbitrary: n w rule: S.induct)
case Sempty
then show ?case by simp
next
  case (Sconj u)
  thus ?case
  proof (cases n)
    case 0
    then have "balanced 0 u" using Sconj(2) by auto
    thus ?thesis using 0 Sconj(3) balanced_add_b by auto
  next
    case (Suc k)
    then obtain z where p: "z @ [b] = w" using Sconj(3)
      by (metis Nil_is_append_conv alpha.distinct(1) append_butlast_last_id last.simps last_appendR 
list.distinct(1) replicate_app_Cons_same)
    hence "u = replicate k a @ z" using Sconj(3) Suc by auto
    hence "balanced k z" using Sconj(2) by simp
    thus ?thesis using Suc p balanced_add_b by auto
  qed
next
  case (Sdouble x y)
  then show ?case
  proof (cases "x = Nil")
    case True
then show ?thesis using Sdouble.hyps(4) Sdouble.hyps(5) by auto
next
case False
  then show ?thesis
  proof (cases " length x < n")
    case True
    hence "x @ y = replicate (length x) a @ replicate (n - length x) a @ w" using Sdouble(5)
      by (simp add: replicate_pinch)
    hence "x = replicate (length x) a" by auto
    hence False using False Sdouble(1)
      by (metis Sdouble.hyps(2) append.right_neutral balanced.simps(4) lessI less_Suc_eq_0_disj 
replicate_empty)
    thus ?thesis by blast
next
case False
  then obtain z' where p': "x = replicate n a @ z'" using Sdouble(5) append_pinch  
  by (metis append_Nil2 append_eq_append_conv length_replicate linorder_neqE_nat)
  hence L : "balanced n z'" by (simp add: Sdouble.hyps(2))
  have R : "balanced 0 y"  by (simp add: Sdouble.hyps(4))
  from p' and Sdouble(5) have "w = z' @ y" by auto
  hence "balanced n w" using balanced_append L R by blast
  thus ?thesis by auto
qed
qed
qed
qed


end