theory Unify imports
  Main
begin

(*
--------------------------------------------------
Assignment 1
--------------------------------------------------
*)

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

lemma fv_sapply[simp]: "fv (\<sigma> · t) = (\<Union> x \<in> (fv t). fv (\<sigma> x))"
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

lemma scomp_sapply[simp]: "(\<sigma> \<circ>s \<tau> ) x = \<sigma> ·(\<tau> x)"
  by simp

lemma sapply_scomp_distrib[simp]: "(\<sigma> \<circ>s \<tau> ) · t = \<sigma> · (\<tau> · t)"
  apply (induction t)
   apply simp_all
  done

lemma scomp_assoc[simp]: "(\<sigma> \<circ>s \<tau> ) \<circ>s q = \<sigma> \<circ>s (\<tau> \<circ>s q)"
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

lemma fold_union_map[simp]:
  assumes "x \<in> (fold (\<union>) (map f l) {})"
  shows "x \<in> (\<Union>y\<in>(set l).f y)"
  using assms by (metis Sup_set_fold set_map)

lemma fv_fun[simp]: "fv (Fun f l) = (\<Union> x \<in> (set l). fv x)"
  by (metis Sup_set_fold fv.simps(2) set_map)

lemma fv_sapply_sdom_svran[simp]:
  assumes "x \<in> fv (\<sigma> · t)"
  shows "x \<in> (fv t - sdom \<sigma>) \<union> svran \<sigma>"
  using assms
proof (induction t)
  case (Var y)
  then show ?case
  proof (cases "y \<in> sdom \<sigma>")
    case True
    then have "\<sigma> y \<in> sran \<sigma>" by auto
    then have "fv (\<sigma> y) \<subseteq> svran \<sigma>" by auto
    then have "fv (\<sigma> · (Var y)) \<subseteq> svran \<sigma>" by simp
    then show ?thesis using Var.prems by blast
  next
    case False
    then show ?thesis using Var.prems by auto
  qed
next
  case (Fun x1a x2)
  have "x \<in> (\<Union>x2a \<in> (set x2). fv (\<sigma> · x2a))"
    by (metis (no_types, lifting) Fun.prems SUP_UNION Sup.SUP_cong fv_fun fv_sapply)
  also obtain x2a where "x2a \<in> (set x2) \<and> x \<in> fv (\<sigma> · x2a)"
    using calculation by blast
  then show ?case
    by (metis Diff_iff Fun.IH UN_I UnE UnI1 UnI2 fv_fun)
qed

lemma sdom_scomp[simp]: "sdom (\<sigma> \<circ>s \<tau> ) \<subseteq> sdom \<sigma> \<union> sdom \<tau>"
  by auto

lemma svran_scomp[simp]: "svran (\<sigma> \<circ>s \<tau> ) \<subseteq> svran \<sigma> \<union> svran \<tau>"
  apply (auto simp add: singleton_iff)
  by (metis fv.simps(1) sapply.simps(2) singletonD)

(*
--------------------------------------------------
Assignment 2
--------------------------------------------------
*)

type_synonym ('f, 'v) equation = "('f, 'v) term \<times> ('f, 'v) term"
type_synonym ('f, 'v) eq_system = "('f, 'v) equation list"

fun fv_eq :: "('f , 'v) equation \<Rightarrow> 'v set" where
  "fv_eq eq = (fv (fst eq)) \<union> (fv (snd eq))"

fun fv_eq_system :: "('f, 'v) eq_system \<Rightarrow> 'v set" where
  "fv_eq_system l = fold (\<union>) (map fv_eq l) {}"

fun sapply_eq :: "('f, 'v) subst \<Rightarrow> ('f, 'v) equation \<Rightarrow> ('f, 'v) equation" (infixr "·" 67)
  where
  "sapply_eq \<sigma> eq = (sapply \<sigma> (fst eq), sapply \<sigma> (snd eq))"

fun sapply_eq_system :: "('f, 'v) subst \<Rightarrow> ('f, 'v) eq_system \<Rightarrow> ('f, 'v) eq_system" (infixr "·" 67)
  where
"sapply_eq_system \<sigma> l = map (sapply_eq \<sigma>) l"

lemma fv_sapply_eq[simp]: "fv_eq (\<sigma> · eq) = (\<Union> x \<in> (fv_eq eq). fv (\<sigma> x))"
  by simp

lemma fv_sapply_eq_system[simp]: "fv_eq_system (\<sigma> · s) = (\<Union> x \<in> (fv_eq_system s). fv (\<sigma> x))"
proof (induction s)
  case Nil
  then show ?case by simp
next
  case (Cons eq s)
  have "fv_eq_system (\<sigma> · (eq # s)) = fold (\<union>) (map fv_eq (\<sigma> · (eq # s))) {}" by simp
  also have "... = (\<Union>y\<in>(set (\<sigma> · (eq # s))). fv_eq y)" by (metis Sup_set_fold set_map)
  also have "... = (\<Union>y\<in>(set (\<sigma> · s)). fv_eq y) \<union> (\<Union>y\<in>(set (\<sigma> · [eq])). fv_eq y)" by (simp add: inf_sup_aci(5))
  have "(\<Union>y\<in>(set (\<sigma> · s)). fv_eq y) = fv_eq_system (\<sigma> · s)"
    by (metis Sup_set_fold fv_eq_system.elims set_map)
  have "... = (\<Union> x \<in> (fv_eq_system s). fv (\<sigma> x))" using Cons.IH by blast
  have "(\<Union>y\<in>(set (\<sigma> · [eq])). fv_eq y) =  (\<Union>x\<in>(fv_eq_system [eq]). fv (\<sigma> x))"
    by auto
  also have "fv_eq_system (\<sigma> · (eq # s)) =
             (\<Union> x \<in> (fv_eq_system s). fv (\<sigma> x)) \<union> (\<Union>x\<in>(fv_eq_system [eq]). fv (\<sigma> x))"
    using Cons.IH \<open>(\<Union>y\<in>set (\<sigma> · s). fv_eq y) = fv_eq_system (\<sigma> · s)\<close> calculation by auto
  also have "... = (\<Union> x \<in> (fv_eq_system (eq # s)). fv (\<sigma> x))"
    by (metis (no_types, lifting) Sup_set_fold UN_Un UN_insert Union_image_empty empty_set fv_eq_system.elims inf_sup_aci(5) list.simps(15) set_map)
  then show ?case
    using \<open>fv_eq_system (\<sigma> · (eq # s)) = (\<Union>x\<in>fv_eq_system s. fv (\<sigma> x)) \<union> (\<Union>x\<in>fv_eq_system [eq]. fv (\<sigma> x))\<close> by auto
qed

lemma sapply_scomp_distrib_eq[simp]: "(\<sigma> \<circ>s \<tau>) · (eq :: ('f, 'v) equation) = \<sigma> · (\<tau> · eq)"
  apply auto
  using sapply_scomp_distrib apply force+
  done

lemma sapply_scomp_distrib_eq_system[simp]: "(\<sigma> \<circ>s \<tau>) · (s :: ('f, 'v) eq_system) = \<sigma> · (\<tau> · s)"
  apply auto
  using sapply_scomp_distrib apply force+
  done

end