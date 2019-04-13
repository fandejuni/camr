theory Unify imports
  Main
begin

(* Assignment 1 *)

datatype ('f , 'v) "term" = Var 'v | Fun 'f "('f, 'v) term list "

fun fv :: "('f , 'v) term \<Rightarrow> 'v set" where
  "fv (Var x) = {x}"
| "fv (Fun f l) = fold (\<union>) (map fv l) {}"

value "fv (Fun (1 :: nat) [Var (0 :: nat), Var 1, Fun 2 [Var 2, Fun 3 [Var 5]]])"

type_synonym ('f, 'v) subst = "'v \<Rightarrow> ('f, 'v) term"

fun sapply :: "('f, 'v) subst \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term" (infixr "·" 67)
  where
  "sapply s (Fun f l) = Fun f (map (sapply s) l)"
| "sapply s (Var x) = s x"

lemma fv_sapply: "fv (\<sigma> · t) = (\<Union> x \<in> (fv t). fv (\<sigma> x))"
proof (induction t)
  case (Var y)
  have "fv (\<sigma> · Var y) = fv (\<sigma> y)" by simp
  also have "... = (\<Union>x \<in> {y} .fv (\<sigma> x))" by simp
  also have "... = (\<Union>x \<in> fv (Var y) .fv (\<sigma> x))" by simp
  then show ?case by simp
next
  case (Fun x1a x2)
  then have "fv (\<sigma> · Fun x1a x2) = fold (\<union>) (map (fv \<circ> (sapply \<sigma>)) x2) {}" by simp
  also have "... = (\<Union>y\<in>(set x2).((fv \<circ> (sapply \<sigma>)) y))" by (metis Sup_set_fold set_map)
  also have "... = (\<Union>y\<in>(set x2).(fv (\<sigma> · y)))" by simp
  also have "... =  (\<Union>y\<in>(set x2). (\<Union>yy\<in>fv y. fv (\<sigma> yy)))" using Fun.IH by simp
  also have "... = (\<Union>x\<in>fv (Fun x1a x2). fv (\<sigma> x))"
    by (metis Sup_set_fold UN_UN_flatten fv.simps(2) set_map)
  also have "fv (\<sigma> · Fun x1a x2) = (\<Union>x\<in>fv (Fun x1a x2). fv (\<sigma> x))"
    using calculation by blast
  then show ?case by simp
qed

lemma sapply_cong:
  assumes "\<And>x. x \<in> fv t \<Longrightarrow> \<sigma> x = \<tau> x"
  shows "\<sigma> · t = \<tau> · t"
  using assms
  apply (induction t)
   apply auto
  apply (metis Sup_set_fold UnI1 Union_insert insert_absorb list.map(2) list.set(2) set_map)
  done

(*
Tentative of Isar proof
proof (induction t)
  have "\<forall>x. \<sigma> · (Var x) = \<tau> · (Var x)"
  proof (rule allI)
    fix x
    show "\<sigma> · (Var x) = \<tau> · (Var x)"
    proof -
      assume "t = Var x"
      have "\<sigma> · (Var x) = \<sigma> x" by simp
      moreover have "x \<in> fv (Var x)" by simp
      also have "\<sigma> x = \<tau> x" using \<open>t = Var x\<close> assms by auto
      also have "\<tau> x = \<tau>  · (Var x)" by simp
      also have "\<sigma> · (Var x) =  \<tau>  · (Var x)"
        using \<open>\<sigma> x = \<tau> x\<close> \<open>\<sigma> · Var x = \<sigma> x\<close> \<open>\<tau> x = \<tau> · Var x\<close> \<open>t = Var x\<close> by presburger
      then show "\<sigma> · Var x = \<tau> · Var x" by simp
next
  case (Fun f l)
  then show ?thesis sorry
qed
*)

fun scomp :: "('f, 'v) subst \<Rightarrow> ('f, 'v) subst \<Rightarrow> ('f, 'v) subst" (infixl "\<circ>s" 75)
  where
  "scomp \<sigma> \<tau> = (\<lambda> x. \<sigma> · \<tau>(x))"

lemma scomp_sapply: "(\<sigma> \<circ>s \<tau> ) x = \<sigma> ·(\<tau> x)"
  by simp

lemma sapply_scomp_distrib: "(\<sigma> \<circ>s \<tau> ) · t = \<sigma> · (\<tau> · t)"
  apply (induction t)
   apply simp_all
  done

lemma scomp_assoc: "(\<sigma> \<circ>s \<tau> ) \<circ>s q = \<sigma> \<circ>s (\<tau> \<circ>s q)"
proof (rule ext)
  show "(\<sigma> \<circ>s \<tau> \<circ>s q) x = (\<sigma> \<circ>s (\<tau> \<circ>s q)) x" for x
    using sapply_scomp_distrib by simp
qed

lemma scomp_Var [simp]: "\<sigma> \<circ>s Var = \<sigma>"
proof (rule ext)
  show "(\<sigma> \<circ>s Var) x = \<sigma> x" for x
    by simp
qed

thm term.induct

lemma Var_id: "Var · t = t"
proof (induction t)
  case (Var x)
then show ?case by simp
next
  case (Fun x1a x2)
  then show ?case
    by (simp add: map_idI)
qed

lemma Var_scomp [simp]: "Var \<circ>s \<sigma> = \<sigma>"
  by (simp add: Var_id)

(* 1. (d) *)

fun sdom :: "('f , 'v) subst \<Rightarrow> 'v set"
  where
  "sdom \<sigma> = {x. \<sigma> x \<noteq> Var x}"

thm sorted_list_of_set

definition set_to_list :: "'a set \<Rightarrow> 'a list"
  where "set_to_list s = (SOME l. set l = s)"

lemma  set_set_to_list:
   "finite s \<Longrightarrow> set (set_to_list s) = s"
unfolding set_to_list_def by (metis (mono_tags) finite_list some_eq_ex)

fun sran :: "('f, 'v) subst \<Rightarrow> ('f, 'v) term set"
  where
"sran \<sigma> = (\<Union>x\<in>sdom \<sigma>. {\<sigma> x})"

fun svran:: "('f , 'v) subst \<Rightarrow> 'v set"
  where
"svran \<sigma> = (\<Union>t\<in>(sran \<sigma>).(fv t))"

lemma sdom_Var [simp]: "sdom Var = {}"
  by simp

lemma svran_Var [simp]: "svran Var = {}"
  by simp

lemma sdom_single_non_trivial [simp]:
  assumes "t \<noteq> Var x"
  shows "sdom (Var(x:=t)) = {x}"
  using assms by simp

lemma svran_single_non_trivial [simp]:
  assumes "t \<noteq> Var x"
  shows "svran (Var(x:=t)) = fv t"
  using assms by simp

lemma fv_sapply_sdom_svran:
  assumes "x \<in> fv (\<sigma> · t)"
  shows "x \<in> (fv t - sdom \<sigma>) \<union> svran \<sigma>"
  using assms
  apply (induction t)
   apply auto
     apply force
    apply (metis empty_iff fv.simps(1) insert_iff)
  sorry

lemma sdom_scomp: "sdom (\<sigma> \<circ>s \<tau> ) \<subseteq> sdom \<sigma> \<union> sdom \<tau>"
  by auto

lemma svran_scomp: "svran (\<sigma> \<circ>s \<tau> ) \<subseteq> svran \<sigma> \<union> svran \<tau>"
  apply (auto simp add: sdom_scomp)
  sorry

end