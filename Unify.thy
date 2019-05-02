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
(* | "fv (Fun f l) = (\<Union>x\<in>(set l).(fv x))" *)

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

lemma prelim_prelim_unify:
  assumes "y \<in> fv_eq (Var(x := t) · a)"
  shows "y \<in> fold (\<union>) (map fv_eq (a # U)) (insert x (fv t))"
  using assms
  apply (auto simp add: Sup_set_fold UnI1 UnI2 assms fun_upd_other fun_upd_same insertI1 insertI2 list.simps(15) singletonD)
  apply (metis (mono_tags, hide_lams) Sup_set_fold Un_iff Un_insert_right fold_union_basic fv.simps(1) fv_eq.simps inf_sup_aci(5) insert_iff singleton_iff)+
  done

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
      then show ?thesis by (meson prelim_prelim_unify)
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
      apply (simp add: measure_unify measure_simp)+
   apply (simp add: fold_plus_sum_list_rev measure_fun)
  apply (simp add: measure_fun)
  done

(* 3. (b) *)

lemma alternative_definition_unifiess:
 "unifiess \<tau> U \<longleftrightarrow> (\<forall>eq\<in>(set U). unifies \<tau> eq)"
proof (induction U)
  case Nil
  then show ?case using unifiess_empty by auto
next
  case (Cons a U)
  have "unifiess \<tau> (a # U) \<longleftrightarrow> (\<forall>eq\<in>set (a # U). unifies \<tau> eq)"
  proof (rule iffI)
    assume "unifiess \<tau> (a # U)"
    show "\<forall>eq\<in>set (a # U). unifies \<tau> eq"
      by (metis Cons.IH \<open>unifiess \<tau> (a # U)\<close> list.discI list.sel(3) set_ConsD unifiess.simps)
  next
    assume "\<forall>eq\<in>set (a # U). unifies \<tau> eq"
    show  "unifiess \<tau> (a # U)"
      by (simp add: Cons.IH \<open>\<forall>eq\<in>set (a # U). unifies \<tau> eq\<close> unifiess_rec)
  qed
  then show ?case by blast
qed

lemma separate_unifiess:
  "unifiess \<tau> (U @ V) \<longleftrightarrow> (unifiess \<tau> U) \<and> (unifiess \<tau> V)"
proof (rule iffI)
  assume "unifiess \<tau> (U @ V)"
  show "(unifiess \<tau> U) \<and> (unifiess \<tau> V)"
  proof -
    have "unifiess \<tau> (U @ V) = (\<forall>eq\<in>set (U @ V). unifies \<tau> eq)"
    by (simp add: alternative_definition_unifiess)
  also have "... = (\<forall>eq\<in>set U. unifies \<tau> eq) \<and> (\<forall>eq\<in>set V. unifies \<tau> eq)"
    using \<open>unifiess \<tau> (U @ V)\<close> calculation by auto
  also have "... = (unifiess \<tau> U) \<and> (unifiess \<tau> V)"
    using \<open>unifiess \<tau> (U @ V)\<close> alternative_definition_unifiess calculation by blast
  then show ?thesis
    using alternative_definition_unifiess calculation by blast
qed
next
  assume "(unifiess \<tau> U) \<and> (unifiess \<tau> V)"
  show "unifiess \<tau> (U @ V)"
  proof -
    have "unifiess \<tau> (U @ V) = (\<forall>eq\<in>set (U @ V). unifies \<tau> eq)"
    by (simp add: alternative_definition_unifiess)
  also have "... = (\<forall>eq\<in>set U. unifies \<tau> eq) \<and> (\<forall>eq\<in>set V. unifies \<tau> eq)"
    using \<open>unifiess \<tau> U \<and> unifiess \<tau> V\<close> alternative_definition_unifiess by fastforce
  also have "... = (unifiess \<tau> U) \<and> (unifiess \<tau> V)"
    using \<open>unifiess \<tau> U \<and> unifiess \<tau> V\<close> alternative_definition_unifiess by blast
  then show ?thesis
    using alternative_definition_unifiess calculation by blast
qed
qed

lemma case_unify:
  assumes h1: "\<And>\<sigma>. \<lbrakk>x \<notin> fv t; unify (Var(x := t) · U) = Some \<sigma>\<rbrakk> \<Longrightarrow> unifiess \<sigma> (Var(x := t) · U)"
    and h2: "\<And>\<sigma>. \<lbrakk>\<not> x \<notin> fv t; Var x = t; unify U = Some \<sigma>\<rbrakk> \<Longrightarrow> unifiess \<sigma> U"
    and h3: "unify ((Var x, t) # U) = Some \<sigma>"
  shows "unifiess \<sigma> ((Var x, t) # U)"
  using assms
proof (cases "x \<in> fv t")
  case True
  then show ?thesis
    by (metis assms(2) assms(3) option.discI unifies_eq unifiess_rec unify.simps(2))
next
  case False
  obtain \<tau> where "Some \<tau> = lifted_comp (unify (Var(x := t) · U)) (Var(x := t))"
    using False h3 by auto
  also obtain \<sigma> where "(Some \<sigma>) = (unify (Var(x := t) · U))"
    by (metis calculation lifted_comp.elims)
  have "\<tau> =  \<sigma> \<circ>s (Var(x := t))"
    by (metis False \<open>Some \<sigma> = unify (Var(x := t) · U)\<close> calculation h3 lifted_comp.simps(2) map_upd_eqD1 sapply_eq_system.simps unify.simps(2))
  have "\<tau> · (Var x) = (\<sigma> \<circ>s (Var(x := t))) · (Var x)"
    by (simp add: \<open>\<tau> = \<sigma> \<circ>s Var(x := t)\<close>)
  have "... = \<sigma> · t"
    by simp
  moreover have "... = (\<sigma> \<circ>s (Var(x := t))) · t"
    by (metis (mono_tags, lifting) False fun_upd_other sapply_cong scomp.elims scomp_Var)
  moreover have "... = \<tau> · t"
    by (simp add: \<open>\<tau> = \<sigma> \<circ>s Var(x := t)\<close>)
  then show ?thesis
    by (metis False \<open>Some \<sigma> = unify (Var(x := t) · U)\<close> \<open>\<sigma> \<circ>s Var(x := t) · Var x = \<sigma> · t\<close> \<open>\<sigma> · t = \<sigma> \<circ>s Var(x := t) · t\<close> \<open>\<tau> = \<sigma> \<circ>s Var(x := t)\<close> calculation h1 h3 option.inject unifies_eq unifies_sapply_eq_sys unifiess_rec unify.simps(2))
qed

lemma unifiess_zip_simple_2:
  assumes "unifiess \<sigma> (zip u v @ U)"
  and "length u = length v"
  shows "unifiess \<sigma> U"
  using assms
proof (induction u arbitrary: v)
  case Nil
  then show ?case by simp
next
  case (Cons a u)
  obtain b and vv where "v = b # vv"
    by (metis Cons.prems(2) Suc_length_conv)
  then show ?case
    using Cons.IH Cons.prems(1) Cons.prems(2) unifiess.simps by auto
qed

lemma unifiess_zip_simple_4:
  assumes "unifiess \<sigma> (U @ V)"
  shows "unifiess \<sigma> U"
  using assms
proof (induction U)
  case Nil
  then show ?case
  by (simp add: unifiess_empty)
next
  case (Cons a U)
  then show ?case
    by (metis (no_types, lifting) append_is_Nil_conv hd_append2 list.sel(1) list.sel(3) tl_append2 unifiess.simps)
qed

lemma test:
  assumes "unifiess \<sigma> u"
  shows "map (sapply \<sigma>) (map fst u) = map (sapply \<sigma>) (map snd u)"
  using assms
proof (induction u)
  case (unifiess_empty \<sigma>)
  then show ?case
    by simp
next
  case (unifiess_rec \<sigma> s eq)
  then show ?case
    using unifies.simps by force
qed
  
lemma case_fun:
  assumes " \<lbrakk>f = g \<and> length u = length v; unify (zip u v @ U) = Some \<sigma>\<rbrakk> \<Longrightarrow> unifiess \<sigma> (zip u v @ U)"
and "unify ((Fun f u, Fun g v) # U) = Some \<sigma>"
shows "unifiess \<sigma> ((Fun f u, Fun g v) # U)"
  using assms
proof -
  obtain "f = g" and "length u = length v"
    using assms(2) option.discI by fastforce
  have "unify (zip u v @ U) = Some \<sigma>"
    using \<open>f = g\<close> \<open>length u = length v\<close> assms(2) by auto
  have "unifiess \<sigma> (zip u v @ U)"
    by (simp add: \<open>f = g\<close> \<open>length u = length v\<close> \<open>unify (zip u v @ U) = Some \<sigma>\<close> assms(1))
  have "unifiess \<sigma> U"
    using \<open>length u = length v\<close> \<open>unifiess \<sigma> (zip u v @ U)\<close> unifiess_zip_simple_2 by blast
  have "unifiess \<sigma> (zip u v)"
    using \<open>unifiess \<sigma> (zip u v @ U)\<close> unifiess_zip_simple_4 by blast
  have "unifies \<sigma> (Fun f u, Fun g v)"
    by (metis \<open>f = g\<close> \<open>length u = length v\<close> \<open>unifiess \<sigma> (zip u v)\<close> map_fst_zip map_snd_zip sapply.simps(1) test unifies_eq)
  then show ?thesis
    by (simp add: \<open>unifiess \<sigma> U\<close> unifiess_rec)
qed

theorem soundness1:
  assumes "unify U = Some \<sigma>"
  shows "unifiess \<sigma> U"
  using assms
  apply (induction arbitrary: \<sigma> rule: unify.induct)
     apply (simp add: unifiess_empty)
    apply (meson case_unify)
  apply (metis list.discI list.sel(1) list.sel(3) prod.sel(1) prod.sel(2) unifies.simps unifiess.simps unify.simps(3))
  by (simp add: case_fun)

(*

Hint: Split the proof into two parts and prove them separately by computational induction.
(i) If unify returns a substitution, it is a unifier.
(ii) If unify returns a substitution \<sigma> and there is another unifier \<tau> , then
\<tau> = \<rho> ◦s \<sigma> for some \<rho>.

*)

lemma unifies_fv_same:
  assumes "\<tau> · Var x = \<tau> · t"
  and "x \<notin> fv t"
  shows "sapply (\<tau> \<circ>s (Var(x := t))) = sapply \<tau>"
proof (rule ext)
  show "sapply (\<tau> \<circ>s Var(x := t)) xa = sapply \<tau> xa" for xa
  proof (induction xa rule: term.induct)
    case (Var y)
    then show ?case
      using assms(1) by auto
  next
    case (Fun x1a x2)
    then show ?case by auto
  qed
qed

lemma unifies_equal_sapply:
  assumes "unifiess \<sigma> U"
  and "sapply \<sigma> = sapply \<tau>"
shows "unifiess \<tau> U"
  by (metis alternative_definition_unifiess assms(1) assms(2) unifies.simps)

lemma sapply_equal:
  assumes "sapply \<sigma> = sapply \<tau>"
  shows "\<sigma> = \<tau>"
proof (rule ext)
  show "\<sigma> x = \<tau> x" for x
  proof -
    have "\<sigma> x = sapply \<sigma> (Var x)" by (metis assms sapply.simps(2))
    also have "... = sapply \<tau> (Var x)" by (simp add: assms)
    also have "... = \<tau> x" by simp
    then show ?thesis by (simp add: calculation)
  qed
qed

lemma case_mgu_unify:
  fixes \<sigma>
  assumes "\<And>\<sigma>2 \<tau>. \<lbrakk>x \<notin> fv t; unify (Var(x := t) · U) = Some \<sigma>2; unifiess \<tau> (Var(x := t) · U)\<rbrakk> \<Longrightarrow> \<exists>\<rho>. \<tau> = \<rho> \<circ>s \<sigma>2"
and "\<And>\<sigma>2 \<tau>. \<lbrakk>\<not> x \<notin> fv t; Var x = t; unify U = Some \<sigma>2; unifiess \<tau> U\<rbrakk> \<Longrightarrow> \<exists>\<rho>. \<tau> = \<rho> \<circ>s \<sigma>2"
and "unify ((Var x, t) # U) = Some \<sigma>"
and "unifiess \<tau> ((Var x, t) # U)"
shows "\<exists>\<rho>. \<tau> = \<rho> \<circ>s \<sigma>"
proof (cases "x \<in> fv t")
  case True
  then show ?thesis
    by (metis assms(2) assms(3) assms(4) list.discI list.sel(3) option.discI unifiess.simps unify.simps(2))
next
  case False
  obtain \<sigma>2 where "unify (Var(x := t) · U) = Some \<sigma>2"
    using False assms(3) by fastforce
  also have "\<sigma> = \<sigma>2 \<circ>s (Var(x := t))"
    using False assms(3) calculation by auto
  have "\<tau> · (Var x) = \<tau> · t"
    by (metis assms(4) list.discI list.sel(1) prod.sel(1) prod.sel(2) unifies.simps unifiess.simps)
  have "\<forall>(u,w)\<in>(set U). \<tau> · u = \<tau> · w"
    by (metis (mono_tags, lifting) alternative_definition_unifiess assms(4) case_prodI2 insert_iff list.set(2) prod.sel(1) prod.sel(2) unifies.simps)
  have "unifiess \<tau> (Var(x := t) · U)"
    by (metis False \<open>\<tau> · Var x = \<tau> · t\<close> assms(4) list.discI list.sel(3) unifies_equal_sapply unifies_fv_same unifies_sapply_eq_sys unifiess.simps)
  obtain \<rho> where "\<tau> = \<rho> \<circ>s \<sigma>2"
    using False \<open>unifiess \<tau> (Var(x := t) · U)\<close> assms(1) calculation by auto
  moreover have "sapply (\<tau> \<circ>s (Var(x := t))) = sapply \<tau>"
    by (meson False \<open>\<tau> · Var x = \<tau> · t\<close> unifies_fv_same)
  moreover have "\<tau> = \<rho> \<circ>s \<sigma>" by (metis \<open>sapply (\<tau> \<circ>s Var(x := t)) = (·) \<tau>\<close> \<open>\<sigma> = \<sigma>2 \<circ>s Var(x := t)\<close> calculation(2) sapply_equal scomp_assoc)
  then show ?thesis
    by blast
qed

lemma useful_1:
  assumes "unifies \<tau> (Fun f (map fst (a # u)), Fun g (map snd (a # u)))"
  shows "unifies \<tau> (Fun f (map fst u), Fun g (map snd u))"
proof -
  have "map (sapply \<tau>) (map fst (a # u)) = map (sapply \<tau>) (map snd (a # u))"
    by (metis assms prod.sel(1) prod.sel(2) sapply.simps(1) term.inject(2) unifies.simps)
  also have "map (sapply \<tau>) ((fst a) # (map fst u)) = map (sapply \<tau>) ((snd a) # (map snd u))"
    using calculation by auto
  moreover have "map (sapply \<tau>) (map fst u) = map (sapply \<tau>) (map snd u)"
    using \<open>map ((·) \<tau>) (fst a # map fst u) = map ((·) \<tau>) (snd a # map snd u)\<close> by auto
  then show ?thesis
    by (metis (no_types, lifting) assms prod.sel(1) prod.sel(2) sapply.simps(1) term.inject(2) unifies.simps)
qed

lemma useful_2:
  assumes "unifies \<tau> (Fun f (map fst (a # u)), Fun g (map snd (a # u)))"
  shows "unifies \<tau> (fst a, snd a)"
proof -
  have "map (sapply \<tau>) (map fst (a # u)) = map (sapply \<tau>) (map snd (a # u))"
    by (metis assms prod.sel(1) prod.sel(2) sapply.simps(1) term.inject(2) unifies.simps)
  moreover have "map (sapply \<tau>) ((fst a) # (map fst u)) = map (sapply \<tau>) ((snd a) # (map snd u))"
    using calculation by auto
  moreover have "map (sapply \<tau>) [fst a] = map (sapply \<tau>) [snd a]"
    using \<open>map ((·) \<tau>) (fst a # map fst u) = map ((·) \<tau>) (snd a # map snd u)\<close> by auto
  then show ?thesis
    using unifies_eq by fastforce
qed

lemma unifies_fun_args:
  assumes "unifies \<tau> (Fun f (map fst u), Fun g (map snd u))"
  shows "unifiess \<tau> u"
  using assms
proof (induction u)
  case Nil
  then show ?case
    by (simp add: unifiess_empty)
next
  case (Cons a u)
  then show ?case
    by (metis prod.collapse unifiess_rec useful_1 useful_2)
qed

lemma case_mgu_fun:
  assumes " \<lbrakk>f = g \<and> length u = length v; unify (zip u v @ U) = Some \<sigma>; unifiess \<tau> (zip u v @ U)\<rbrakk>
        \<Longrightarrow> \<exists>\<rho>. \<tau> = \<rho> \<circ>s \<sigma>"
and "unify ((Fun f u, Fun g v) # U) = Some \<sigma>"
and "unifiess \<tau> ((Fun f u, Fun g v) # U)"
shows "\<exists>\<rho>. \<tau> = \<rho> \<circ>s \<sigma>"
  using assms
proof -
  obtain "f = g" and "length u = length v"
    using assms(2) by fastforce
  moreover have "unify (zip u v @ U) = Some \<sigma>"
    using \<open>f = g\<close> \<open>length u = length v\<close> assms(2) by auto
  moreover have "unifiess \<tau> (zip u v @ U)"
  proof -
    have "unifiess \<tau> U"
      by (metis assms(3) list.discI list.sel(3) unifiess.simps)
    moreover have "unifies \<tau> (Fun f u, Fun g v)"
      by (metis assms(3) list.discI list.sel(1) unifiess.simps)
    moreover have "unifiess \<tau> (zip u v)"
      by (metis \<open>\<And>thesis. (\<lbrakk>f = g; length u = length v\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> \<open>unifies \<tau> (Fun f u, Fun g v)\<close> map_fst_zip map_snd_zip unifies_fun_args)
    then show ?thesis
      by (simp add: calculation separate_unifiess)
  qed
  then show ?thesis
    using assms(1) calculation(1) calculation(2) calculation(3) by blast
qed

theorem soundness2:
  assumes "unify U = Some \<sigma>"
  and "unifiess \<tau> U"
shows "\<exists>\<rho>. \<tau> = \<rho> \<circ>s \<sigma>"
  using assms
proof (induction arbitrary: \<sigma> \<tau> rule: unify.induct)
  case 1
  then show ?case by simp
next
  case (2 x t U)
  then show ?case
    by (metis (no_types, lifting) case_mgu_unify)
next
  case (3 v va y U)
  then show ?case
    by (metis list.discI list.sel(1) list.sel(3) prod.sel(1) prod.sel(2) unifies.simps unifiess.simps unify.simps(3))
next
  case (4 f u g v U)
then show ?case
  by (meson case_mgu_fun)
qed

theorem soundness:
  "unify U = Some \<sigma> \<Longrightarrow> is_mgu \<sigma> U"
  using is_mgu.simps soundness2 by blast















(* (c). Formalize theorem 3 *)



fun sum_liste :: "nat list \<Rightarrow> nat" where
  "sum_liste [] = 0"
| "sum_liste (t # q) = t + sum_liste q"

lemma sum_liste_fold:
  "fold (+) (map f l) 0 = sum_liste (map f l)"
proof (induction l)
  case Nil
  then show ?case
    by simp
next
  case (Cons a l)
  then show ?case
    by (simp add: fold_plus_sum_list_rev)
qed

lemma increasing_sum_liste:
 "xa \<in> (set x2) \<Longrightarrow> sum_liste (map size_term (map (sapply \<tau>) x2))  \<ge>
sum_liste (map size_term (map (sapply \<tau>) [xa]))"
proof (induction x2)
  case Nil
  then show ?case by auto
next
  case (Cons a x2)
  then show ?case using list.simps(8) set_ConsD by auto
qed

lemma size_term_fun:
  assumes "xa \<in> (set x2)"
  shows "size_term (sapply \<tau> xa) \<le> size_term (sapply \<tau> (Fun x1a x2))"
  using assms
proof -
  have "sapply \<tau> (Fun x1a x2) = Fun x1a (map (sapply \<tau>) x2)" by simp
  also have "size_term (Fun x1a (map (sapply \<tau>) x2)) \<ge>
            fold (+) (map size_term (map (sapply \<tau>) x2)) 0"
    by (meson less_imp_le_nat size_term_sound)
  also have "fold (+) (map size_term (map (sapply \<tau>) x2)) 0 = sum_liste (map size_term (map (sapply \<tau>) x2))"
    by (simp add: sum_liste_fold)
  also have "... \<ge> sum_liste (map size_term (map (sapply \<tau>) [xa]))"
    using assms increasing_sum_liste by auto
  have "sum_liste (map size_term (map (sapply \<tau>) [xa])) = size_term (sapply \<tau> xa)" by simp
  then show ?thesis
    using \<open>sum_liste (map Unify.size_term (map ((·) \<tau>) [xa])) \<le> sum_liste (map Unify.size_term (map ((·) \<tau>) x2))\<close> calculation by linarith
qed

lemma size_term_subterm_prelim:
  "x \<in> fv t \<Longrightarrow> size_term (sapply \<tau> (Var x)) \<le> size_term (sapply \<tau> t)"
proof (induction t)
  case (Var y)
  then show ?case
    by simp
next
  case (Fun x1a x2)
  obtain xa where "xa \<in> (set x2)" and "x \<in> fv xa"
    by (metis Fun.prems UN_E fv_fun)
  also have "size_term (sapply \<tau> (Var x)) \<le> size_term (sapply \<tau> xa)"
    using Fun.IH calculation by auto
  have "size_term (sapply \<tau> xa) \<le> size_term (sapply \<tau> (Fun x1a x2))"
    using calculation(1) size_term_fun by auto
  then show ?case
    using \<open>Unify.size_term (\<tau> · Var x) \<le> Unify.size_term (\<tau> · xa)\<close> dual_order.trans by blast
qed

lemma size_term_subset:
  "xa \<in> (set l) \<Longrightarrow> size_term (sapply \<tau> (Fun f l)) \<ge> 1 + size_term (sapply \<tau> xa)"
proof (induction l)
  case Nil
  then show ?case by auto
next
  case (Cons a ll)
  then show ?case
  proof (cases "xa = a")
    case True
    have "size_term (sapply \<tau> (Fun f (xa # ll))) =
          size_term ((sapply \<tau>) xa) + (size_term (sapply \<tau> (Fun f ll)))"
      by (simp add: fold_plus_sum_list_rev)
    then show ?thesis
      by (simp add: True fold_plus_sum_list_rev)
  next
    case False
    have "xa \<in> (set ll)" using Cons.prems False by auto
    also have "size_term (sapply \<tau> (Fun f ll)) \<ge> 1 + size_term (sapply \<tau> xa)"
      using Cons.IH calculation by auto
    have "size_term (\<tau> · Fun f (a # ll)) = size_term (Fun f (map (sapply \<tau>) (a # ll)))"
      by simp
    have "... = size_term ((sapply \<tau>) a) + size_term (Fun f (map (sapply \<tau>) ll))"
      by (simp add: fold_plus_sum_list_rev)
    then show ?thesis
      using \<open>1 + Unify.size_term (\<tau> · xa) \<le> Unify.size_term (\<tau> · Fun f ll)\<close> by auto
  qed
qed

lemma size_term_subterm:
  assumes "x \<in> fv t"
  and "\<not> (Var x = t)"
shows "size_term (sapply \<tau> (Var x)) < size_term (sapply \<tau> t)"
proof -
  obtain f and l where "t = Fun f l"
    by (metis (full_types) Unify.term.simps(17) assms(1) assms(2) fv.elims term.set_cases(2))
  also obtain xa where "(xa \<in> (set l)) \<and> x \<in> fv xa"
    by (metis UN_E assms(1) calculation fv_fun)
  have "size_term (sapply \<tau> (Var x)) \<le> size_term (sapply \<tau> xa)"
    by (meson \<open>xa \<in> set l \<and> x \<in> fv xa\<close> size_term_subterm_prelim)
  moreover have "size_term (sapply \<tau> t) > size_term (sapply \<tau> xa)"
    by (metis (no_types, lifting) \<open>xa \<in> set l \<and> x \<in> fv xa\<close> calculation(1) le_less_trans lessI linorder_neqE_nat order.asym plus_1_eq_Suc size_term_subset)
  then show ?thesis
    using calculation(2) le_less_trans by blast
qed

lemma lemma2:
  assumes "\<exists>\<tau>. unifiess \<tau> U"
  shows "\<not>(unify U = None)"
  using assms
proof (induction rule: unify.induct)
case 1
  then show ?case by simp
next
  case (2 x t U)
  then show ?case
  proof (cases "x \<in> fv t")
    case True
    have "Var x = t"
    proof (rule ccontr)
      assume "\<not> (Var x = t)"
      show "False"
      proof -
        obtain \<tau> where "unifiess \<tau> ((Var x, t) # U)"
          using "2.prems" by blast
        also have "sapply \<tau> (Var x) = sapply \<tau> t"
          by (metis calculation list.discI list.sel(1) prod.sel(1) prod.sel(2) unifies.simps unifiess.simps)
        have "size_term (sapply \<tau> (Var x)) = size_term (sapply \<tau> t)"
          using \<open>\<tau> · Var x = \<tau> · t\<close> by auto
        have "size_term (sapply \<tau> (Var x)) < size_term (sapply \<tau> t)"
          by (meson True \<open>Var x \<noteq> t\<close> size_term_subterm)
        then show ?thesis
          using \<open>Unify.size_term (\<tau> · Var x) = Unify.size_term (\<tau> · t)\<close> nat_neq_iff by blast
      qed
    qed
    then show ?thesis
      by (metis "2.IH"(2) "2.prems" fv.simps(1) insert_iff list.discI list.sel(3) unifiess.simps unify.simps(2))
  next
    case False
    (* UNIFY case *)
    obtain \<tau> where "unifiess \<tau> ((Var x, t) # U)"
      using "2.prems" by blast
    also have "sapply \<tau> (Var x) = sapply \<tau> t"
      by (metis calculation list.discI list.sel(1) prod.sel(1) prod.sel(2) unifies.simps unifiess.simps)
    have "sapply (\<tau> \<circ>s (Var(x := t))) = sapply \<tau>"
      by (meson False \<open>\<tau> · Var x = \<tau> · t\<close> unifies_fv_same)
    have "unifiess (\<tau> \<circ>s (Var(x := t))) U"
      by (metis \<open>sapply (\<tau> \<circ>s Var(x := t)) = sapply \<tau>\<close> calculation list.distinct(1) list.sel(3) unifies_equal_sapply unifiess.cases)
    then show ?thesis
      using "2.IH"(1) False unifies_sapply_eq_sys by fastforce
  qed
next
case (3 v va y U)
  then show ?case
  by (metis list.discI list.sel(1) list.sel(3) prod.sel(1) prod.sel(2) unifies.simps unifiess.simps unify.simps(3))
next
  case (4 f u g v U)
  obtain "f = g" and "length u = length v"
    by (metis (no_types, lifting) "4.prems" length_map list.discI list.sel(1) prod.sel(1) prod.sel(2) sapply.simps(1) term.inject(2) unifies.simps unifiess.simps)
  then show ?case
    by (metis (no_types, lifting) "4.IH" "4.prems" list.discI list.sel(1) list.sel(3) map_fst_zip map_snd_zip separate_unifiess unifies_fun_args unifiess.simps unify.simps(4))
qed

theorem completeness:
  assumes "\<exists>\<tau>. unifiess \<tau> U"
  shows "\<exists>\<sigma>. unify U = Some \<sigma> \<and> unifiess \<sigma> U"
  using assms lemma2 soundness1 by fastforce













(* (d). Lemma 3 *)

lemma simple_fv_eq_system_double_var:
  "fv_eq_system ((Var x, Var y) # U) = (fv_eq_system U) \<union> {x, y}" (is "?A = ?B")
proof -
  have "?A \<subseteq> ?B"
  proof (rule subsetI)
    fix xa assume "xa \<in> ?A" then show "xa \<in> ?B"
    proof (cases "xa \<in> fv_eq_system U")
      case True
      then show ?thesis by simp
    next
      case False
      have "xa = x \<or> xa = y"
        by (metis (no_types, lifting) False Sup_set_fold UN_insert UnE UnI2 \<open>xa \<in> fv_eq_system ((Var x, Var y) # U)\<close> fold_union_basic fv.simps(1) fv_eq.elims fv_eq_system.elims insert_iff list.simps(15) prod.sel(1) prod.sel(2) set_map)
      then show ?thesis by blast
    qed
  qed
  moreover have "?B \<subseteq> ?A"
  proof (rule subsetI)
    fix xa assume "xa \<in> ?B" then show "xa \<in> ?A"
    proof (cases "xa \<in> {x, y}")
      case True
      then show ?thesis
        by (metis (no_types, lifting) Sup_set_fold UN_insert \<open>xa \<in> fv_eq_system U \<union> {x, y}\<close> fv.simps(1) fv_eq.elims fv_eq_system.elims inf_sup_aci(5) insert_is_Un list.simps(15) prod.sel(1) prod.sel(2) set_map)
    next
      case False
      then show ?thesis
        by (metis (no_types, lifting) Sup_set_fold UN_insert \<open>xa \<in> fv_eq_system U \<union> {x, y}\<close> fv.simps(1) fv_eq.elims fv_eq_system.elims inf_sup_aci(5) insert_is_Un list.simps(15) prod.sel(1) prod.sel(2) set_map)
    qed
  qed
  then show ?thesis using calculation by blast
qed

lemma simple_fv_apply:
  "fv_eq_system (\<sigma> · ((Var x, Var y) # U)) = fv (\<sigma> x) \<union> fv (\<sigma> y) \<union> fv_eq_system (\<sigma> · U)"
  apply (auto simp add: SUP_union simple_fv_eq_system_double_var sup_assoc sup_left_commute)
     apply (metis UnE fold_union_basic)
  using fold_union_basic apply fastforce+
  done

lemma simple_fold_map_first_elem:
  "fold (\<union>) (map f (t # q)) {} = (f t) \<union> fold (\<union>) (map f q) {}"
  by (metis Sup_set_fold UN_insert list.simps(15) set_map)

lemma fv_fun_simple:
  "fv_eq (Fun f (map fst U), Fun g (map snd U)) = fv_eq_system U"
proof (induction U)
  case Nil
  have "fv_eq (Fun f (map fst []), Fun g (map snd [])) = fv_eq (Fun f [], Fun g [])" by auto
  also have "... = (fold (\<union>) (map fv []) {}) \<union> (fold (\<union>) (map fv []) {})" by simp
  have "(fold (\<union>) (map fv []) {}) = {}" by simp
  have "fv_eq_system [] = {}" by auto
  then show ?case by simp
next
  case (Cons a U)
  have "fv_eq (Fun f ((fst a) # (map fst U)), Fun g ((snd a) # (map snd U))) =
  (fold (\<union>) (map fv ((fst a) # (map fst U))) {}) \<union> (fold (\<union>) (map fv ((snd a) # (map snd U))) {})" by auto
  also have "... = (fv (fst a)) \<union> (fold (\<union>) (map fv (map fst U)) {}) \<union> (fv (snd a)) \<union> (fold (\<union>) (map fv (map snd U)) {})"
    by (metis (no_types, lifting) simple_fold_map_first_elem sup_assoc)
  also have "... = (fv_eq a) \<union> (fold (\<union>) (map fv (map fst U)) {}) \<union> (fold (\<union>) (map fv (map snd U)) {})" by auto
  have "(fold (\<union>) (map fv (map fst U)) {}) \<union> (fold (\<union>) (map fv (map snd U)) {}) = fv_eq (Fun f (map fst U), Fun g (map snd U))" by simp
  have "fv_eq (Fun f (map fst U), Fun g (map snd U)) = fv_eq_system U" using Cons.IH by blast
  then show ?case
    by (metis \<open>fold (\<union>) (map fv (map fst U)) {} \<union> fold (\<union>) (map fv (map snd U)) {} = fv_eq (Fun f (map fst U), Fun g (map snd U))\<close> \<open>fv (fst a) \<union> fold (\<union>) (map fv (map fst U)) {} \<union> fv (snd a) \<union> fold (\<union>) (map fv (map snd U)) {} = fv_eq a \<union> fold (\<union>) (map fv (map fst U)) {} \<union> fold (\<union>) (map fv (map snd U)) {}\<close> calculation fv_eq_system.elims list.simps(9) simple_fold_map_first_elem sup_assoc)
qed

lemma fv_fun_simple_alternative:
  assumes "length u = length v"
  shows "fv_eq (Fun f u, Fun g v) = fv_eq_system (zip u v)"
  by (metis assms fv_fun_simple map_fst_zip map_snd_zip)

lemma fv_union:
  "(fv_eq_system U) \<union> (fv_eq_system V) = fv_eq_system (U @ V)"
proof (induction U)
  case Nil
  then show ?case by auto
next
  case (Cons a U)
  then show ?case
    by (metis (no_types, lifting) append_Cons fv_eq_system.elims inf_sup_aci(5) simple_fold_map_first_elem sup_left_commute)
qed

lemma fv_eq_fun_lists:
  assumes "length u = length v"
  shows "fv_eq_system (zip u v @ U) = fv_eq_system ((Fun f u, Fun g v) # U)"
proof -
  have "fv_eq_system ((Fun f u, Fun g v) # U) = (fv_eq (Fun f u, Fun g v)) \<union> (fv_eq_system U)"
    by (metis (no_types, lifting) Sup_set_fold UN_insert fv_eq_system.elims list.simps(15) set_map)
  have "fv_eq (Fun f u, Fun g v) = fv_eq_system (zip u v)" using assms fv_fun_simple_alternative by auto
  also have "fv_eq_system (zip u v) \<union> (fv_eq_system U) = fv_eq_system (zip u v @ U)" by (meson fv_union)
  then show ?thesis
    using \<open>fv_eq_system ((Fun f u, Fun g v) # U) = fv_eq (Fun f u, Fun g v) \<union> fv_eq_system U\<close> calculation by blast
qed

lemma lemma_3_i_iii:
  "\<forall>U. unify U = Some \<sigma> \<Longrightarrow> fv_eq_system (\<sigma> · U) \<subseteq> fv_eq_system U \<and> sdom \<sigma> \<subseteq> fv_eq_system U \<and> svran \<sigma> \<subseteq> fv_eq_system U"
proof (induction U arbitrary: \<sigma> rule: unify.induct)
  case 1
  then show ?case
    by (metis empty_iff list.simps(8) option.inject sapply_eq_system.elims sdom_Var subsetI svran_Var unify.simps(1))
next
  case (2 x t U)
  then show ?case
  proof (cases "x \<in> fv t")
    case True
    have "Var x = t"
    proof (rule ccontr)
      assume "\<not> (Var x = t)"
      show "False"
      proof -
        show ?thesis using "2"(3) True \<open>Var x \<noteq> t\<close>
          by (metis lemma2 unifiess_empty unify.simps(1) unify.simps(2))
      qed
    qed

  (* SIMP CASE *)

    have "unify U = unify ((Var x, t) # U)" using \<open>Var x = t\<close> by auto
    have "fv_eq_system (\<sigma> · U) \<subseteq> fv_eq_system U \<and> sdom \<sigma> \<subseteq> fv_eq_system U \<and> svran \<sigma> \<subseteq> fv_eq_system U"
      using "2"(2) "2.prems" True \<open>Var x = t\<close> \<open>unify U = unify ((Var x, t) # U)\<close> by auto
    also have "fv_eq_system ((Var x, t) # U) = (fv_eq_system U) \<union> {x}"
      by (metis \<open>Var x = t\<close> insert_absorb2 simple_fv_eq_system_double_var)
    moreover have "fv_eq_system (\<sigma> · ((Var x, t) # U)) = fv (\<sigma> x) \<union> fv_eq_system (\<sigma> · U)"
      using \<open>Var x = t\<close> simple_fv_apply by fastforce
    have "fv (\<sigma> x) \<subseteq> {x} \<union> fv_eq_system ((Var x, t) # U)"
    proof -
      have "fv (\<sigma> x) \<subseteq> (fv (Var x) - sdom \<sigma>) \<union> svran \<sigma>"
        by (metis fv.simps(1) fv_sapply_sdom_svran sapply.simps(2) subsetI)
      have "(fv (Var x) - sdom \<sigma>) \<union> svran \<sigma> \<subseteq> (fv (Var x) - sdom \<sigma>) \<union> fv_eq_system U"
        using calculation(1) by fastforce
      moreover have "(fv (Var x) - sdom \<sigma>) \<subseteq> {x} \<union> fv_eq ((Var x, t))" by auto
      also have "fv_eq ((Var x, t)) \<subseteq> fv_eq_system ((Var x, t) # U)"
        using \<open>Var x = t\<close> \<open>fv_eq_system ((Var x, t) # U) = fv_eq_system U \<union> {x}\<close> fv_eq.elims by auto
      moreover have "fv_eq_system U \<subseteq> fv_eq_system ((Var x, t) # U)"
        using \<open>fv_eq_system ((Var x, t) # U) = fv_eq_system U \<union> {x}\<close> by auto
      then show ?thesis
        using \<open>Var x = t\<close> \<open>fv (\<sigma> x) \<subseteq> fv (Var x) - sdom \<sigma> \<union> svran \<sigma>\<close> calculation(1) by fastforce
    qed
    moreover have "sdom \<sigma> \<subseteq> fv_eq_system ((Var x, t) # U)"
      using calculation(1) calculation(2) by blast
    moreover have "svran \<sigma> \<subseteq> fv_eq_system ((Var x, t) # U)"
      using calculation(1) calculation(2) by blast
    then show ?thesis
      using \<open>fv_eq_system (\<sigma> · ((Var x, t) # U)) = fv (\<sigma> x) \<union> fv_eq_system (\<sigma> · U)\<close> calculation(1) calculation(2) calculation(3) by auto
  next
    case False

(* CASE UNIFY *)

    obtain \<sigma>2 where "unify (Var(x := t) · ((Var x, t) # U)) = Some \<sigma>2"
      by (metis (no_types, hide_lams) "2.prems" False completeness lifted_comp.elims option.discI soundness1 unifies_sapply_eq_sys unify.simps(2))
    have "\<sigma> = \<sigma>2 \<circ>s (Var(x := t))"
      by (metis "2.prems" False \<open>unify (Var(x := t) · ((Var x, t) # U)) = Some \<sigma>2\<close> lifted_comp.simps(2) option.inject unify.simps(2))
    have "fv_eq_system (Var(x := t) · U) \<subseteq> fv(t) \<union> fv_eq_system(U)"
      by (metis "2.prems" False Var_scomp \<open>\<sigma> = \<sigma>2 \<circ>s Var(x := t)\<close> \<open>unify (Var(x := t) · ((Var x, t) # U)) = Some \<sigma>2\<close> fun_upd_same fv.simps(1) option.inject singletonI unify.simps(1))
    obtain "fv_eq_system (\<sigma> · Var(x := t) · U) \<subseteq> fv_eq_system (Var(x := t) · U) \<and> sdom \<sigma> \<subseteq> fv_eq_system (Var(x := t) · U) \<and> svran \<sigma> \<subseteq> fv_eq_system (Var(x := t) · U)"
      using "2.IH"(1) "2.prems" False by blast
    have "fv_eq_system (\<sigma>2 · (Var(x := t) · U)) \<subseteq> fv(t) \<union> fv_eq_system(U)"
      using "2.prems" \<open>\<And>thesis. (fv_eq_system (\<sigma> · Var(x := t) · U) \<subseteq> fv_eq_system (Var(x := t) · U) \<and> sdom \<sigma> \<subseteq> fv_eq_system (Var(x := t) · U) \<and> svran \<sigma> \<subseteq> fv_eq_system (Var(x := t) · U) \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> \<open>fv_eq_system (Var(x := t) · U) \<subseteq> fv t \<union> fv_eq_system U\<close> \<open>unify (Var(x := t) · ((Var x, t) # U)) = Some \<sigma>2\<close> by auto
    have "sdom \<sigma>2 \<subseteq> fv t \<union> fv_eq_system U"
      using "2.prems" \<open>\<And>thesis. (fv_eq_system (\<sigma> · Var(x := t) · U) \<subseteq> fv_eq_system (Var(x := t) · U) \<and> sdom \<sigma> \<subseteq> fv_eq_system (Var(x := t) · U) \<and> svran \<sigma> \<subseteq> fv_eq_system (Var(x := t) · U) \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> \<open>fv_eq_system (Var(x := t) · U) \<subseteq> fv t \<union> fv_eq_system U\<close> \<open>unify (Var(x := t) · ((Var x, t) # U)) = Some \<sigma>2\<close> by auto
    have "fv_eq_system ((Var x, t) # U) = (fv t) \<union> (fv_eq_system U) \<union> {x}"
      by (metis (no_types, lifting) Un_insert_left Un_insert_right fv.simps(1) fv_eq.elims fv_eq_system.elims insert_is_Un prod.sel(1) prod.sel(2) simple_fold_map_first_elem sup_bot.right_neutral)
    have "fv_eq_system (\<sigma> · ((Var x, t) # U)) = fv_eq_system ((\<sigma>2 \<circ>s (Var(x := t))) · ((Var x, t) # U))"
      by (metis \<open>\<sigma> = (\<sigma>2 \<circ>s Var(x := t))\<close>)
    also have "... = fv (\<sigma>2 · t) \<union> fv_eq_system (\<sigma>2 · (Var(x := t) · U))"
      by (metis "2.prems" False Var_id \<open>\<sigma> = \<sigma>2 \<circ>s Var(x := t)\<close> \<open>unify (Var(x := t) · ((Var x, t) # U)) = Some \<sigma>2\<close> fun_upd_same fv.simps(1) option.inject scomp_sapply singletonI unify.simps(1))
  then show ?thesis
    by (metis "2.prems" False Var_scomp \<open>\<sigma> = \<sigma>2 \<circ>s Var(x := t)\<close> \<open>unify (Var(x := t) · ((Var x, t) # U)) = Some \<sigma>2\<close> fun_upd_same fv.simps(1) option.inject singletonI unify.simps(1))
  qed
next
  case (3 v va y U)
  then show ?case by (simp add: inf_sup_aci(5) unify.simps(3))
next
  case (4 f u g v U)
  have "f = g \<and> length u = length v" using "4.prems" option.discI by (metis unify.simps(4))
  have "unify (zip u v @ U) = Some \<sigma>" using "4.prems" \<open>f = g \<and> length u = length v\<close> by auto
  obtain "fv_eq_system (\<sigma> · (zip u v @ U)) \<subseteq> fv_eq_system (zip u v @ U)"
    and "sdom \<sigma> \<subseteq> fv_eq_system (zip u v @ U)"
    and "svran \<sigma> \<subseteq> fv_eq_system (zip u v @ U)"
    using "4.IH" \<open>f = g \<and> length u = length v\<close> \<open>unify (zip u v @ U) = Some \<sigma>\<close> "4.prems" by blast
  have "svran \<sigma> \<subseteq> fv_eq_system ((Fun f u, Fun g v) # U)"
    using \<open>f = g \<and> length u = length v\<close> \<open>svran \<sigma> \<subseteq> fv_eq_system (zip u v @ U)\<close> fv_eq_fun_lists by fastforce
  moreover have "sdom \<sigma> \<subseteq> fv_eq_system ((Fun f u, Fun g v) # U)"
    using \<open>f = g \<and> length u = length v\<close> \<open>sdom \<sigma> \<subseteq> fv_eq_system (zip u v @ U)\<close> fv_eq_fun_lists by fastforce
  moreover have "fv_eq_system (\<sigma> · ((Fun f u, Fun g v) # U)) \<subseteq> fv_eq_system ((Fun f u, Fun g v) # U)"
    by (metis \<open>f = g \<and> length u = length v\<close> \<open>fv_eq_system (\<sigma> · (zip u v @ U)) \<subseteq> fv_eq_system (zip u v @ U)\<close> fv_eq_fun_lists fv_sapply_eq_system)
  then show ?case using calculation(1) calculation(2) by blast
qed

lemma lemma_3_iv:
  "\<forall>U. unify U = Some \<sigma> \<Longrightarrow> {} \<subseteq> fv_eq_system U \<and> sdom \<sigma> \<inter> svran \<sigma> = {}"
proof (induction U arbitrary: \<sigma> rule: unify.induct)
case 1
  then show ?case
    by (metis empty_subsetI inf_bot_right option.inject svran_Var unify.simps(1))
next
  case (2 x t U)
  then show ?case
  proof (cases "x \<in> fv t")
    case True
    then show ?thesis
      by (metis "2.prems" empty_subsetI inf_bot_right option.inject svran_Var unify.simps(1))
  next

  (* CASE UNIFY *)

    case False
    then show ?thesis
      using "2.IH"(1) "2.prems" False by blast
  qed
next
case (3 v va y U)
  then show ?case
    by simp
next
  case (4 f u g v U)
  then show ?case
    by (metis empty_subsetI inf_bot_right option.inject svran_Var unify.simps(1))
qed
















(*
--------------------------------------------------
Assignment 4
--------------------------------------------------
*)

(* 4. (a) *)

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
   apply (simp add: wf_subst_def wf_term.intros(1))
  oops

end