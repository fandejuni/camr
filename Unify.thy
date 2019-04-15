theory Unify imports
  Main
begin

(*
--------------------------------------------------
Assignment 1
--------------------------------------------------
*)

datatype ('f , 'v) "term" = Var 'v | Fun 'f "('f, 'v) term list"

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
  then show ?thesis ? ? ?
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

lemma fold_union_map[intro]:
  "\<lbrakk> x \<in> (fold (\<union>) (map f l) {}) \<rbrakk> \<Longrightarrow> x \<in> (\<Union>y\<in>(set l).f y)"
  by (metis Sup_set_fold set_map)

lemma fold_union_map_rev[elim]:
  "\<lbrakk> x \<in> (\<Union>y\<in>(set l).f y) \<rbrakk> \<Longrightarrow>  x \<in> (fold (\<union>) (map f l) {})"
  by (metis Sup_set_fold set_map)

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
type_synonym ('f, 'v) equations = "('f, 'v) equation list"

fun fv_eq :: "('f , 'v) equation \<Rightarrow> 'v set" where
  "fv_eq eq = (fv (fst eq)) \<union> (fv (snd eq))"

fun fv_eq_system :: "('f, 'v) equations \<Rightarrow> 'v set" where
  "fv_eq_system l = fold (\<union>) (map fv_eq l) {}"

fun sapply_eq :: "('f, 'v) subst \<Rightarrow> ('f, 'v) equation \<Rightarrow> ('f, 'v) equation" (infixr "·" 67)
  where
  "sapply_eq \<sigma> eq = (sapply \<sigma> (fst eq), sapply \<sigma> (snd eq))"

fun sapply_eq_system :: "('f, 'v) subst \<Rightarrow> ('f, 'v) equations \<Rightarrow> ('f, 'v) equations" (infixr "·" 67)
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
  have "fv_eq_system (\<sigma> · (eq # s)) =
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

lemma sapply_scomp_distrib_eq_system[simp]: "(\<sigma> \<circ>s \<tau>) · (s :: ('f, 'v) equations) = \<sigma> · (\<tau> · s)"
  apply auto
  using sapply_scomp_distrib apply force+
  done

(* 2. (b) *)

inductive unifies :: "('f, 'v) subst \<Rightarrow> ('f, 'v) equation \<Rightarrow> bool" where
  unifies_eq: "(\<sigma> · u = \<sigma> · t) \<Longrightarrow> unifies \<sigma> (u, t)"

inductive unifiess :: "('f, 'v) subst \<Rightarrow> ('f, 'v) equations \<Rightarrow> bool" where
  unifiess_empty: "unifiess \<sigma> []"
| unifiess_rec:   "(unifiess \<sigma> s) \<and> (unifies \<sigma> eq) \<Longrightarrow> unifiess \<sigma> (eq # s)"

fun is_mgu :: "('f, 'v) subst \<Rightarrow> ('f, 'v) equations \<Rightarrow> bool" where
  "is_mgu \<sigma> U = (\<forall>\<tau>. unifiess \<tau> U \<longrightarrow> (\<exists>\<rho> . \<tau> = \<rho> \<circ>s \<sigma>))"

(* 2. (c) *)

lemma unifies_sapply_eq[simp]: "unifies \<sigma> (sapply_eq \<tau> eq) \<longleftrightarrow> unifies (\<sigma> \<circ>s \<tau> ) eq"
proof -
  have "unifies \<sigma> (sapply_eq \<tau> eq) \<longleftrightarrow> \<sigma> · (fst (sapply_eq \<tau> eq)) = \<sigma> · (snd (sapply_eq \<tau> eq))"
    by (simp add: unifies.simps)
  also have "... \<longleftrightarrow> \<sigma> · (\<tau>  · (fst eq)) = \<sigma> · (\<tau>  · (snd eq))" by simp
  also have "... \<longleftrightarrow> (\<sigma> \<circ>s \<tau>)  · (fst eq) = (\<sigma> \<circ>s \<tau>)  · (snd eq)" by (metis sapply_scomp_distrib)
  also have "... \<longleftrightarrow> unifies (\<sigma> \<circ>s \<tau> ) eq" using unifies.simps by force
  then show ?thesis using calculation by blast
qed

lemma unifies_sapply_eq_sys: "unifiess \<sigma> (sapply_eq_system \<tau> U) \<longleftrightarrow> unifiess (\<sigma> \<circ>s \<tau> ) U"
  apply (induction U)
   apply (simp add: unifiess_empty)
  apply auto
     apply (metis (no_types, lifting) list.discI list.sel(1) prod.sel(1) prod.sel(2) sapply_cong sapply_scomp_distrib scomp.simps unifies.simps unifiess.simps)
    apply (metis (no_types, lifting) list.discI list.sel(1) prod.sel(1) prod.sel(2) sapply_cong sapply_scomp_distrib scomp.simps unifies.simps unifiess.simps)
  using unifiess.cases apply auto[1]
  using le_boolD ord_eq_le_trans unifiess.simps by blast

(*
--------------------------------------------------
Assignment 3
--------------------------------------------------
*)

fun lifted_comp :: "('f, 'v) subst option \<Rightarrow> ('f, 'v) subst \<Rightarrow> ('f, 'v) subst option"
  where
  "lifted_comp None \<tau> = None"
| "lifted_comp (Some \<sigma>) \<tau> = Some (\<sigma> \<circ>s \<tau>)"

fun get_equations :: "('f, 'v) term list \<Rightarrow> ('f, 'v) term list \<Rightarrow> ('f, 'v) equations"
  where
  "get_equations [] v = []"
| "get_equations u [] = []"
| "get_equations (h1 # q1) (h2 # q2) = (h1, h2) # (get_equations q1 q2)"

fun size_term :: "('f, 'v) term \<Rightarrow> nat" where
  "size_term (Var x) = 0"
| "size_term (Fun f l) = fold (+) (map size_term l) 1"

lemma size_term_sound: "size_term (Fun f l) > fold (+) (map size_term l) 0"
  by (simp add: fold_plus_sum_list_rev)

lemma [simp]: "0 < size_term t \<or> size_term t = 0"
  by auto

fun k2 :: "('f, 'v) equations \<Rightarrow> nat" where
  "k2 [] = 0"
| "k2 (eq # U) = size_term (fst eq) + k2 U"

lemma k2_def: "k2 U = fold (+) (map (size_term \<circ> fst) U) 0"
  apply (induction U)
   apply simp
  by (simp add: fold_plus_sum_list_rev)

lemma fold_union_basic: "fold (\<union>) l s = (fold (\<union>) l {}) \<union> s"
proof -
  have "fold (\<union>) l s = (\<Union>x\<in>(set l).x) \<union> s"
    by (metis Sup_insert Sup_set_fold fold_simps(2) image_ident list.simps(15) sup_bot.right_neutral sup_commute)
  also have "... = (fold (\<union>) l {}) \<union> s" by (simp add: Sup_set_fold)
  then show ?thesis by (simp add: calculation)
qed

lemma finite_fv: "finite (fv t)"
proof (induction t)
  case (Var x)
  then show ?case by auto
next
  case (Fun x1a x2)
  have "fv (Fun x1a x2) = (\<Union>x2a\<in>(set x2). fv x2a)" by (meson fv_fun)
  then show ?case by (simp add: Fun.IH)
qed

lemma finite_fv_eq: "finite (fv_eq eq)"
  by (simp add: finite_fv)

lemma finite_fold_fv:
  assumes "finite s" 
  shows "finite (fold (\<union>) (map fv_eq U) s)"
  using assms
proof (induction U)
  case Nil
  then show ?case by simp
next
  case (Cons a U)
  then show ?case
    by (metis Sup_set_fold UN_insert Un_infinite finite_UnI finite_fv_eq fold_union_basic list.set(2) set_map)
qed

lemma prelim_unify_equations:
  assumes "x \<notin> fv t"
  shows "x \<notin> fv_eq_system (sapply_eq_system (Var(x := t)) U)"
proof (induction U)
  case Nil
  then show ?case by auto
next
  case (Cons a U)
  have "fv_eq_system (Var(x := t) · (a # U)) = (fv_eq_system (Var(x := t) · U)) \<union> (fv_eq (Var(x := t) · a))"
    by (metis fold_simps(2) fold_union_basic fv_eq_system.elims list.simps(9) sapply_eq_system.elims sup_bot.right_neutral)
  moreover have "x \<notin> fv_eq_system (Var(x := t) · U)"
    using Cons.IH by blast
  moreover have "x \<notin> (fv_eq (Var(x := t) · a))" by (simp add: assms)
  then show ?case by (metis Cons.IH UnE calculation(1))
qed

lemma prelim_unify_2:
  assumes "x \<notin> fv t"
  shows "(fold (\<union>) (map (fv_eq \<circ> (·) (Var(x := t))) U) {}) \<subseteq> (fold (\<union>) (map fv_eq U) (insert x (fv t)))"
proof (rule subsetI)
  fix y
  assume "y \<in> fold (\<union>) (map (fv_eq \<circ> (·) (Var(x := t))) U) {}"
  thus "y \<in> fold (\<union>) (map fv_eq U) (insert x (fv t))"
  proof (induction U)
    case Nil
    then show ?case by simp
  next
    case (Cons a U)
    then show ?case
    proof (cases "y \<in> fold (\<union>) (map (fv_eq \<circ> (·) (Var(x := t))) (U)) {}")
      case True
      then show ?thesis
        by (metis (no_types, lifting) Cons.IH UnCI UnE fold_map fold_simps(2) fold_union_basic)
    next
      case False
      have "y \<in> fv_eq (sapply_eq (Var(x := t)) a)"
      proof -
        have "\<forall>ps p f. fold (\<union>) (map f ps) (f (p::('b, 'a) Unify.term \<times> ('b, 'a) Unify.term)) = fold (\<union>) (map f (p # ps)) ({}::'a set)"
          by simp
        then show ?thesis
          by (metis Cons.prems False UnE comp_apply fold_union_basic)
      qed
      then show ?thesis
        by (smt UN_iff UnCI comp_apply fold_map fold_simps(2) fold_union_basic fun_upd_other fun_upd_same fv.simps(1) fv_sapply_eq insertI2 singletonD)
    qed
  qed
qed

lemma measure_unify:
  assumes "x \<notin> fv t"
  shows "card (fold (\<union>) (map (fv_eq \<circ> (·) (Var(x := t))) U) {})
       < card (fold (\<union>) (map fv_eq U) (insert x (fv t)))"
  (is "card (?s1) < card (?s2)")
  using assms
proof -
  have "?s1 \<subseteq> ?s2"
    by (simp add: assms prelim_unify_2)
  moreover have "x \<notin> ?s1"
    using assms prelim_unify_equations by fastforce
  moreover have "x \<in> ?s2"
    using fold_union_basic by fastforce
  have "?s1 \<subset> ?s2"
    using \<open>x \<in> fold (\<union>) (map fv_eq U) (insert x (fv t))\<close> calculation(1) calculation(2) by blast
  moreover have "finite ?s2" by (simp add: finite_fold_fv finite_fv)
  then show ?thesis by (simp add: calculation(3) psubset_card_mono)
qed

lemma measure_simp:
  assumes "x \<in> fv t" and "Var x = t"
  shows "card (fold (\<union>) (map fv_eq U) {}) < card (fold (\<union>) (map fv_eq U) (fv t)) \<or>
           card (fold (\<union>) (map fv_eq U) {}) = card (fold (\<union>) (map fv_eq U) (fv t))"
  using assms
  by (metis card.insert card_eq_0_iff card_mono empty_iff finite_Un fold_union_basic fv.simps(1) le_neq_trans nat.simps(3) sup_ge1)

lemma zip_fst:
  assumes "length u = length v"
  shows "(\<Union>x\<in>(set (zip u v)). (fv (fst x))) =  (\<Union>x\<in>(set u). (fv x))"
proof -
  have "(\<Union>x\<in>(set (zip u v)). (fv (fst x))) = fold (\<union>) (map (fv \<circ> fst) (zip u v)) {}"
    by (metis (mono_tags, lifting) Sup.SUP_cong Sup_set_fold comp_apply set_map)
  also have "... = fold (\<union>) (map fv (map fst (zip u v))) {}" by simp
  also have "... = fold (\<union>) (map fv u) {}" by (simp add: assms)
  then show ?thesis by (metis Sup_set_fold calculation set_map)
qed

lemma zip_snd:
  assumes "length u = length v"
  shows "(\<Union>x\<in>(set (zip u v)). (fv (snd x))) =  (\<Union>x\<in>(set v). (fv x))"
proof -
  have "(\<Union>x\<in>(set (zip u v)). (fv (snd x))) = fold (\<union>) (map (fv \<circ> snd) (zip u v)) {}"
    by (metis (mono_tags, lifting) Sup.SUP_cong Sup_set_fold comp_apply set_map)
  also have "... = fold (\<union>) (map fv (map snd (zip u v))) {}" by simp
  also have "... = fold (\<union>) (map fv v) {}" by (simp add: assms)
  then show ?thesis by (metis Sup_set_fold calculation set_map)
qed

lemma measure_fun:
  assumes "f = g" and "length u = length v"
  shows "card (fold (\<union>) (map fv_eq U) (fold (\<union>) (map fv_eq (zip u v)) {}))
       = card (fold (\<union>) (map fv_eq U) (fold (\<union>) (map fv u) {} \<union> fold (\<union>) (map fv v) {})) \<and>
       k2 (zip u v @ U) < fold (+) (map Unify.size_term u) (Suc 0) + k2 U"
  using assms
proof -
  have "fold (\<union>) (map fv_eq (zip u v)) {} = (\<Union>x\<in>(set (zip u v)). (fv_eq x))"
    by (metis Sup_set_fold set_map)
  also have "... = (\<Union>x\<in>(set (zip u v)). (fv (fst x) \<union> fv (snd x)))" by auto
  also have "... = (\<Union>x\<in>(set (zip u v)). (fv (fst x))) \<union>
                   (\<Union>x\<in>(set (zip u v)). (fv (snd x)))" by blast
  also have "... = (\<Union>x\<in>(set u). (fv x)) \<union> (\<Union>x\<in>(set v). (fv x))"
    by (simp add: assms(2) zip_fst zip_snd)
  also have "... = fold (\<union>) (map fv u) {} \<union> fold (\<union>) (map fv v) {}"
    by (metis Sup_set_fold image_set)
  have "card (fold (\<union>) (map fv_eq U) (fold (\<union>) (map fv_eq (zip u v)) {}))
       = card (fold (\<union>) (map fv_eq U) (fold (\<union>) (map fv u) {} \<union> fold (\<union>) (map fv v) {}))"
    by (simp add: \<open>(\<Union>x\<in>set u. fv x) \<union> (\<Union>x\<in>set v. fv x) = fold (\<union>) (map fv u) {} \<union> fold (\<union>) (map fv v) {}\<close> calculation)
  moreover have "k2 (zip u v @ U) = (fold (+) (map (size_term \<circ> fst) (zip u v)) 0) + k2 U"
    by (simp add: fold_plus_sum_list_rev k2_def)
  have "... = (fold (+) (map size_term u) 0) + k2 U"
    by (metis assms(2) map_fst_zip map_map)
  then show ?thesis
    by (simp add: \<open>k2 (zip u v @ U) = fold (+) (map (Unify.size_term \<circ> fst) (zip u v)) 0 + k2 U\<close>
        calculation(2) fold_plus_sum_list_rev)
qed

function (sequential) unify :: "('f, 'v) equations \<Rightarrow> ('f, 'v) subst option"
  where
  "unify [] = Some Var"
| "unify ((Var x, t) # U) = (
  if (x \<notin> fv t) then
    lifted_comp (unify((Var(x := t)) · U)) (Var(x := t))
   else (
     if Var x = t then unify(U) else None
    )
  )"
| "unify ((u, Var y) # U) = unify ((Var y, u) # U)"
| "unify ((Fun f u, Fun g v) # U) =
  (if (f = g \<and> length u = length v) then
    unify(append (zip u v) U)
  else
    None)"
  by pat_completeness auto
termination
  apply(relation "measures [\<lambda>U. card (fv_eq_system U), k2, length]")
      apply simp
     apply (simp add: measure_unify)
  apply simp
    apply (simp add: measure_simp)
   apply (simp add: fold_plus_sum_list_rev)
  apply simp
  apply (simp add: measure_fun)
  done

value "(Var((2 :: nat) := (Var 1))) · [(Var 1, Var 1), (Fun (10 :: nat) [], Fun (10 :: nat) [])]"

(* TODO *)

(*
--------------------------------------------------
Assignment 4
--------------------------------------------------
*)

inductive wf_term :: "('f \<Rightarrow> nat) \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" where
  "wf_term ar (Var x)"
| "(length l = ar f) \<and> (\<forall>t\<in>(set l). wf_term ar t) \<Longrightarrow> wf_term ar (Fun f l)"

definition wf_subst :: "('f \<Rightarrow> nat) \<Rightarrow> ('f, 'v) subst \<Rightarrow> bool" where
  "wf_subst ar \<sigma> = (\<forall>x. wf_term ar (\<sigma> x))"

definition wf_eq :: "('f \<Rightarrow> nat) \<Rightarrow> ('f, 'v) equation \<Rightarrow> bool" where
  "wf_eq ar eq \<equiv> (wf_term ar (fst eq)) \<and> (wf_term ar (snd eq))"

inductive wf_eqs :: "('f \<Rightarrow> nat) \<Rightarrow> ('f, 'v) equations \<Rightarrow> bool" where
  "wf_eqs ar []"
| "(wf_eqs ar U) \<and> (wf_equation ar eq) \<Longrightarrow> wf_eqs ar (eq # U)"

(* 4. (b) *)

lemma wf_term_sapply[simp]:
"\<lbrakk> wf_term arity t; wf_subst arity \<sigma> \<rbrakk> \<Longrightarrow> wf_term arity (\<sigma> · t)"
proof (induction t)
case (Var x)
  then show ?case by (simp add: wf_subst_def)
next
  case (Fun x1a x2)
  have "length x2 = arity x1a" using Fun.prems(1) wf_term.simps by fastforce
  moreover have "\<forall>t\<in>(set x2). wf_term arity t" using Fun.prems(1) wf_term.cases by auto
  then show ?case by (simp add: Fun.IH Fun.prems(2) calculation wf_term.intros(2))
qed

lemma wf_subst_scomp[simp]:
"\<lbrakk> wf_subst arity \<sigma>; wf_subst arity \<tau> \<rbrakk> \<Longrightarrow> wf_subst arity (\<sigma> \<circ>s \<tau> )"
  by (simp add: wf_subst_def)

lemma wf_subst_unify:
"\<lbrakk> unify eqs = Some \<sigma>; wf_eqs arity eqs \<rbrakk> \<Longrightarrow> wf_subst arity \<sigma>"
  apply (induction eqs)
  sorry

end