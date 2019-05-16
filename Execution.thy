theory Execution imports
  Main Deduction
begin

(* 9. (a) *)

fun "fold_option" :: "('a \<Rightarrow> 'b option) \<Rightarrow> 'a list \<Rightarrow> 'b option" where
  "fold_option f [] = None"
| "fold_option f (a # as) = (case f a of Some b \<Rightarrow> Some b | None \<Rightarrow> fold_option f as)"

lemma "fold_option_cong"[fundef_cong]: "xs = ys \<Longrightarrow> (\<And>a. a \<in> set xs \<Longrightarrow> f a = f' a) \<Longrightarrow> fold_option f xs = fold_option f' ys"
proof (induction xs arbitrary: ys)
  case (Cons a as)
  then obtain a' as' where "ys = a' # as'"
    by blast
  then show ?case
    by (metis Cons.IH Cons.prems(1) Cons.prems(2) fold_option.simps(2) list.set_intros(1) list.set_intros(2))
qed simp

lemma "fold_option_exists":
  assumes "fold_option f as = Some b"
  shows "\<exists>a \<in> set as. f a = Some b"
  using assms
  apply (induction as)
   apply simp_all
  by (metis option.case_eq_if option.collapse)

lemma "exists_fold_option":
  assumes "\<exists>a \<in> set as. \<not>Option.is_none (f a)"
  shows "\<not>Option.is_none (fold_option f as)"
  using assms
  apply (induction as)
   apply simp_all
  by (simp add: Option.is_none_def option.case_eq_if)

lemma "maps_exists":
  assumes "b \<in> set (List.maps f as)"
  shows "\<exists>a \<in> set as. b \<in> set (f a)"
  using assms
  apply (induction as)
   apply (simp add: maps_simps(2))
  by (metis Un_iff list.set_intros(1) list.set_intros(2) maps_simps(1) set_append)

lemma "exists_maps":
  assumes "\<exists>a \<in> set as. b \<in> set (f a)"
  shows "b \<in> set (List.maps f as)"
  using assms
  apply (induction as)
   apply simp
  by (metis Un_iff maps_simps(1) set_ConsD set_append)

fun c_unify :: "constraint \<Rightarrow> (constraint_system \<times> m_subst) list" where
  "c_unify (M | A \<triangleright> (Var _)) = []"
| "c_unify (M | A \<triangleright> t) = List.maps (\<lambda>u. case m_unify [(t, u)] of Some \<sigma> \<Rightarrow> [([], \<sigma>)] | None \<Rightarrow> []) (M @ A)"

lemma "c_unify_rer1":
  assumes "(cs, \<sigma>) \<in> set (c_unify (M | A \<triangleright> t))"
  shows "rer1 (M | A \<triangleright> t) \<sigma> cs"
  proof -
    have "not_is_var": "\<not>is_var t"
      using assms is_var.simps
      by auto
    obtain u where "u \<in> set (M @ A)" and "(cs, \<sigma>) \<in> set (case m_unify [(t, u)] of Some \<sigma> \<Rightarrow> [([], \<sigma>)] | None \<Rightarrow> [])"
      using assms maps_exists
      apply (cases t)
      by force+
    then show ?thesis
      using not_is_var
      by fastforce
  qed

fun c_comp :: "constraint \<Rightarrow> (constraint_system \<times> m_subst) list" where
  "c_comp (M | A \<triangleright> Hash t) = [([M | A \<triangleright> t], Var)]"
| "c_comp (M | A \<triangleright> Pair t1 t2) = [([M | A \<triangleright> t1, M | A \<triangleright> t2], Var)]"
| "c_comp (M | A \<triangleright> Sym_encrypt m k) = [([M | A \<triangleright> m, M | A \<triangleright> k], Var)]"
| "c_comp (M | A \<triangleright> Public_key_encrypt m k) = [([M | A \<triangleright> m, M | A \<triangleright> k], Var)]"
| "c_comp (M | A \<triangleright> Signature t (Cons i)) = (if i = \<iota> then [([M | A \<triangleright> t], Var)] else [])"
| "c_comp (M | A \<triangleright> _) = []"

lemma "c_comp_rer1":
  assumes "(cs, \<sigma>) \<in> set (c_comp (M | A \<triangleright> t))"
  shows "rer1 (M | A \<triangleright> t) \<sigma> cs"
  using assms
proof (cases t)
  case (Signature t k)
  then show ?thesis
    using assms
    proof (cases k)
      case (Cons i)
      then show ?thesis
        using Signature assms intruder_def
        by auto
    qed auto
  qed force+

fun "c_dec_term" :: "constraint \<Rightarrow> msg \<Rightarrow> (constraint_system \<times> m_subst) list" where
  "c_dec_term (M | A \<triangleright> t) (Pair u v) = (let M' = removeAll (Pair u v) M in [([(u # v # M') | (Pair u v # A) \<triangleright> t], Var)])"
| "c_dec_term (M | A \<triangleright> t) (Sym_encrypt u k) = (let M' = removeAll (Sym_encrypt u k) M in [([(u # M') | (Sym_encrypt u k # A) \<triangleright> t, M' | (Sym_encrypt u k # A) \<triangleright> k], Var)])"
| "c_dec_term (M | A \<triangleright> t) (Public_key_encrypt u (Cons i)) = (if i = \<iota> then let M' = removeAll (Public_key_encrypt u intruder) M in [([(u # M') | (Public_key_encrypt u intruder # A) \<triangleright> t], Var)] else [])"
| "c_dec_term (M | A \<triangleright> t) (Public_key_encrypt u (Var x)) = (let \<sigma> = Var(x := intruder) in [([c_sapply \<sigma> (M | A \<triangleright> t)], \<sigma>)])"
| "c_dec_term (M | A \<triangleright> t) _ = []"

lemma "c_dec_term_rer1":
  assumes "(cs, \<sigma>) \<in> set (c_dec_term (M | A \<triangleright> t) m)" and "m \<in> set M"
  shows "rer1 (M | A \<triangleright> t) \<sigma> cs"
  using assms
proof (cases m)
  case (Sym_encrypt m k)
  then show ?thesis
    using assms
    apply auto
    by (metis empty_set fst_conv list.set(2) rer1.Sdec singletonD snd_conv)
next
  case (Public_key_encrypt u k)
  then show ?thesis
    using assms
    proof (cases k)
      case (Cons i)
      then show ?thesis
        using intruder_def Public_key_encrypt assms(1) assms(2)
        by auto
    next
      case (Var x)
      then show ?thesis
        using assms Ksub Public_key_encrypt
        by (metis c_dec_term.simps(4) Pair_inject empty_set list.set(2) singletonD)
    qed auto
qed auto

fun "c_dec" :: "constraint \<Rightarrow> (constraint_system \<times> m_subst) list" where
  "c_dec (M | A \<triangleright> t) = List.maps (c_dec_term (M | A \<triangleright> t)) M"

lemma "c_dec_rer1":
  assumes "(cs, \<sigma>) \<in> set (c_dec (M | A \<triangleright> t))"
  shows "rer1 (M | A \<triangleright> t) \<sigma> cs"
proof -
  obtain m where "m \<in> set M" and "(cs, \<sigma>) \<in> set (c_dec_term (M | A \<triangleright> t) m)"
    using assms maps_exists
    by force
  then show ?thesis
    using c_dec_term_rer1
    by simp
qed

definition "c_succ" :: "constraint \<Rightarrow> (constraint_system \<times> m_subst) list" where
  "c_succ c = c_unify c @ c_comp c @ c_dec c"

lemma "c_succ_rer1":
  assumes "(cs, \<sigma>) \<in> set (c_succ c)"
  shows "rer1 c \<sigma> cs"
proof -
  obtain M A t where "c = M | A \<triangleright> t"
    using assms c_derives.cases by blast
  then show ?thesis
    using assms c_unify_rer1 c_comp_rer1 c_dec_rer1 c_succ_def by auto
qed

fun "cs_succ_aux" :: "constraint_system \<Rightarrow> constraint_system \<Rightarrow> (constraint_system \<times> m_subst) list" where
  "cs_succ_aux _ [] = []"
| "cs_succ_aux cs' (c # cs'') = map (\<lambda>(cs, \<sigma>). (cs_sapply \<sigma> cs' @ cs @ cs_sapply \<sigma> cs'', \<sigma>)) (c_succ c)
                              @ cs_succ_aux (cs' @ [c]) cs''"

lemma "cs_succ_aux_rer":
  assumes "(ocs, \<sigma>) \<in> set (cs_succ_aux pcs ics)"
  shows "rer (pcs @ ics) \<sigma> ocs"
  using assms
proof (induction ics arbitrary: pcs)
  case (Cons c ics)
  then show ?case
    proof (cases "(ocs, \<sigma>) \<in> set (cs_succ_aux (pcs @ [c]) ics)")
      case False
      then obtain cs where "(cs, \<sigma>) \<in> set (c_succ c)" and "ocs_def": "ocs = cs_sapply \<sigma> pcs @ cs @ cs_sapply \<sigma> ics"
        using Cons False
        by auto
      then show ?thesis
        by (simp add: Context c_succ_rer1)
    qed fastforce
qed simp

definition "cs_succ" :: "constraint_system \<Rightarrow> (constraint_system \<times> m_subst) list" where
  "cs_succ cs = cs_succ_aux [] cs"

lemma "cs_succ_rer": "(cs, \<sigma>) \<in> set (cs_succ ics) \<Longrightarrow> rer ics \<sigma> cs"
  unfolding cs_succ_def
  using cs_succ_aux_rer by fastforce

(* 9. (b) *)

lemma "cs_succ_rer_any": "(cs, \<sigma>) \<in> set (cs_succ ics) \<Longrightarrow> rer_any cs ics"
  using cs_succ_rer rer_any.intros
  by blast

function search :: "constraint_system \<Rightarrow> (constraint_system \<times> m_subst) option" where
  "search ics = (if cs_simple ics then Some (ics, Var)
                 else fold_option (\<lambda>(cs, \<sigma>). case search cs of Some (cs', \<sigma>') \<Rightarrow> Some (cs', m_scomp \<sigma>' \<sigma>) | None \<Rightarrow> None) (cs_succ ics))"
  by pat_completeness auto
termination
  apply (relation "{(x, y). rer_any x y}")
  using rer_any_wf wfP_def apply blast
  using cs_succ_rer_any by auto

(* 9. (c) *)

value "search [[Cons ''a'', Cons ''b'', intruder] | [] \<triangleright> Pair (Var ''A0'') (Var ''B0''),
               [Public_key_encrypt (Pair (Cons ''k0'') (Signature (Cons ''k0'') (Var ''A0''))) (Cons ''b''), Cons ''a'', Cons ''b'', intruder] | [] \<triangleright> Public_key_encrypt (Pair (Var ''K1'') (Signature (Var ''K1'') (Cons ''a''))) (Cons ''b''),
               [Sym_encrypt (Cons ''m1'') (Var ''K1''), Public_key_encrypt (Pair (Cons ''k0'') (Signature (Cons ''k0'') (Var ''A0''))) (Cons ''b''), Cons ''a'', Cons ''b'', intruder] | [] \<triangleright> Sym_encrypt (Var ''Z0'') (Cons ''k0''),
               [Sym_encrypt (Cons ''m1'') (Var ''K1''), Public_key_encrypt (Pair (Cons ''k0'') (Signature (Cons ''k0'') (Var ''A0''))) (Cons ''b''), Cons ''a'', Cons ''b'', intruder] | [] \<triangleright> Pair (Var ''K1'') (Cons ''m1'')]"

value "search [[Cons ''a'', Cons ''b'', intruder] | [] \<triangleright> Pair (Var ''A0'') (Var ''B0''),
               [Public_key_encrypt (Pair (Cons ''na0'') (Var ''A0'')) (Var ''B0''), Cons ''a'', Cons ''b'', intruder] | [] \<triangleright> Public_key_encrypt (Pair (Var ''NA1'') (Cons ''a'')) (Cons ''b''),
               [Public_key_encrypt (Pair (Var ''NA1'') (Cons ''nb1'')) (Cons ''a''), Public_key_encrypt (Pair (Cons ''na0'') (Var ''A0'')) (Var ''B0''), Cons ''a'', Cons ''b'', intruder] | [] \<triangleright> Public_key_encrypt (Pair (Cons ''na0'') (Var ''NB0'')) (Var ''A0''),
               [Public_key_encrypt (Var ''NB0'') (Var ''B0''), Public_key_encrypt (Pair (Var ''NA1'') (Cons ''nb1'')) (Cons ''a''), Public_key_encrypt (Pair (Cons ''na0'') (Var ''A0'')) (Var ''B0''), Cons ''a'', Cons ''b'', intruder] | [] \<triangleright> Public_key_encrypt (Cons ''nb1'') (Cons ''b''),
               [Public_key_encrypt (Var ''NB0'') (Var ''B0''), Public_key_encrypt (Pair (Var ''NA1'') (Cons ''nb1'')) (Cons ''a''), Public_key_encrypt (Pair (Cons ''na0'') (Var ''A0'')) (Var ''B0''), Cons ''a'', Cons ''b'', intruder] | [] \<triangleright> Pair (Var ''NA1'') (Cons ''nb1'')]"

(* 10. (a) *)

lemma "search_sound":
  assumes "search ics = Some (cs', \<sigma>'')"
  shows "cs_simple cs' \<and> rer_star ics \<sigma>'' cs'"
  using assms
  apply (induction ics arbitrary: cs' \<sigma>'' rule: search.induct)
  subgoal premises prems for ics cs' \<sigma>''
    using prems
    proof (cases "cs_simple ics")
      case False
      then have "search ics = fold_option (\<lambda>(cs, \<sigma>). case search cs of Some (cs', \<sigma>') \<Rightarrow> Some (cs', m_scomp \<sigma>' \<sigma>) | None \<Rightarrow> None) (cs_succ ics)"
        by simp
      then have "fold_option (\<lambda>(cs, \<sigma>). case search cs of Some (cs', \<sigma>') \<Rightarrow> Some (cs', m_scomp \<sigma>' \<sigma>) | None \<Rightarrow> None) (cs_succ ics) = Some (cs', \<sigma>'')"
        using prems(2)
        by simp
      then obtain cs \<sigma> where $: "(cs, \<sigma>) \<in> set (cs_succ ics)" and "(case search cs of Some (cs', \<sigma>') \<Rightarrow> Some (cs', m_scomp \<sigma>' \<sigma>) | None \<Rightarrow> None) = Some (cs', \<sigma>'')"
        using fold_option_exists[of "(\<lambda>(cs, \<sigma>). case search cs of Some (cs', \<sigma>') \<Rightarrow> Some (cs', m_scomp \<sigma>' \<sigma>) | None \<Rightarrow> None)" "(cs_succ ics)" "(cs', \<sigma>'')"]
        by auto
      then obtain \<sigma>' where "search cs = Some (cs', \<sigma>')" and "m_scomp_sigma": "\<sigma>'' = m_scomp \<sigma>' \<sigma>"
        by (cases "search cs") auto
      then have "sub": "cs_simple cs' \<and> rer_star cs \<sigma>' cs'"
        using prems(1) False $
        by blast
      have "rer ics \<sigma> cs"
        using $
        by (simp add: cs_succ_rer)
      then show ?thesis
        using m_scomp_sigma sub Trans
        by blast
    qed (simp add: Refl)
    done

(* 10. (b) *)

lemma "search_complete":
  assumes "cs_simple cs'" and "rer_star cs \<sigma> cs'"
  shows "search cs = Some x"
  sorry

end