theory Execution imports
  Main Deduction
begin

(* 9. (a) *)

fun c_unify :: "constraint \<Rightarrow> (constraint_system \<times> m_subst) list" where
  "c_unify (M | A \<triangleright> t) = List.maps (\<lambda>u. case m_unify [(t, u)] of Some \<sigma> \<Rightarrow> [([], \<sigma>)] | _ \<Rightarrow> []) (M @ A)"

lemma "c_unify_rer1": "(cs, \<sigma>) \<in> set (c_unify c) \<Longrightarrow> rer1 c \<sigma> cs"
  sorry

fun c_comp :: "constraint \<Rightarrow> (constraint_system \<times> m_subst) list" where
  "c_comp (M | A \<triangleright> Hash t) = [([M | A \<triangleright> t], Var)]"
| "c_comp (M | A \<triangleright> Pair t1 t2) = [([M | A \<triangleright> t1], Var), ([M | A \<triangleright> t2], Var)]"
| "c_comp (M | A \<triangleright> Sym_encrypt m k) = [([M | A \<triangleright> m], Var), ([M | A \<triangleright> k], Var)]"
| "c_comp (M | A \<triangleright> Public_key_encrypt m k) = [([M | A \<triangleright> m], Var), ([M | A \<triangleright> k], Var)]"
| "c_comp (M | A \<triangleright> Signature t k) = (if k = intruder then [([M | A \<triangleright> t], Var)] else [])"
| "c_comp (M | A \<triangleright> _) = []"

lemma "c_comp_rer1": "(cs, \<sigma>) \<in> set (c_comp c) \<Longrightarrow> rer1 c \<sigma> cs"
  sorry

fun "c_dec_term" :: "constraint \<Rightarrow> msg \<Rightarrow> (constraint_system \<times> m_subst) list" where
  "c_dec_term (M | A \<triangleright> t) (Pair u v) = (let M' = removeAll (Pair u v) M in [([(u # v # M') | (Pair u v # A) \<triangleright> t], Var)])"
| "c_dec_term (M | A \<triangleright> t) (Sym_encrypt u k) = (let M' = removeAll (Sym_encrypt u k) M in [([(u # M') | (Sym_encrypt u k # A) \<triangleright> t, M' | (Sym_encrypt u k # A) \<triangleright> k], Var)])"
| "c_dec_term (M | A \<triangleright> t) (Public_key_encrypt u (Var x)) = (let \<sigma> = Var(x := intruder) in [([c_sapply \<sigma> (M | A \<triangleright> t)], \<sigma>)])"
| "c_dec_term (M | A \<triangleright> t) (Public_key_encrypt u k) = (if k = intruder then let M' = removeAll (Public_key_encrypt u intruder) M in [([(u # M') | (Public_key_encrypt u intruder # A) \<triangleright> t], Var)] else [])"
| "c_dec_term (M | A \<triangleright> t) _ = []"

fun "c_dec" :: "constraint \<Rightarrow> (constraint_system \<times> m_subst) list" where
  "c_dec (M | A \<triangleright> t) = List.maps (c_dec_term (M | A \<triangleright> t)) M"

lemma "c_dec_rer1": "(cs, \<sigma>) \<in> set (c_dec c) \<Longrightarrow> rer1 c \<sigma> cs"
  sorry

definition "c_succ" :: "constraint \<Rightarrow> (constraint_system \<times> m_subst) list" where
  "c_succ c = c_unify c @ c_comp c @ c_dec c"

lemma "c_suc_rer1": "(cs, \<sigma>) \<in> set (c_succ c) \<Longrightarrow> rer1 c \<sigma> cs"
  unfolding c_succ_def
  using c_comp_rer1 c_dec_rer1 c_unify_rer1 by auto

fun "cs_succ_aux" :: "constraint_system \<Rightarrow> constraint_system \<Rightarrow> (constraint_system \<times> m_subst) list" where
  "cs_succ_aux _ [] = []"
| "cs_succ_aux cs' (c # cs'') = (let css = c_succ c in map (\<lambda>(cs, \<sigma>). (cs_sapply \<sigma> cs' @ cs @ cs_sapply \<sigma> cs'', \<sigma>)) css @
                                cs_succ_aux (cs' @ [c]) cs'')"

lemma "cs_succ_aux_rer": "(ocs, \<sigma>) \<in> set (cs_succ_aux pcs ics) \<Longrightarrow> rer (pcs @ ics) \<sigma> ocs"
  apply (induction ics arbitrary: pcs)
   apply simp
  subgoal for c ics pcs
    apply (cases "(ocs, \<sigma>) \<in> set (cs_succ_aux (pcs @ [c]) ics)")
     apply fastforce
    subgoal premises prems
    proof -
      obtain cs where "rer1 c \<sigma> cs" and "ocs = cs_sapply \<sigma> pcs @ cs @ cs_sapply \<sigma> ics"
        using c_suc_rer1 prems
        by auto
      then show ?thesis using prems
        using Context
        by blast
    qed
    done
  done

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
  "search ics = (if cs_simple ics then Some (ics, Var) else List.fold (combine_options (\<lambda>a _. a)) (map (\<lambda>(cs, \<sigma>). case search cs of Some (cs', \<sigma>') \<Rightarrow> Some (cs', m_scomp \<sigma> \<sigma>') | _ \<Rightarrow> None) (cs_succ ics)) None)"
  by pat_completeness auto
termination
  apply (relation "{(x, y). rer_any x y}")
  using rer_any_wf wfP_def apply blast
  using cs_succ_rer_any by auto

end