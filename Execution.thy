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

definition "cs_succ" :: "constraint_system \<Rightarrow> (constraint_system \<times> m_subst) list" where
  "cs_succ ics = List.maps (\<lambda>c. let (css, cs') = (c_succ c, removeAll c ics) in map (\<lambda>(cs, \<sigma>). (cs @ cs_sapply \<sigma> cs', \<sigma>)) css) ics"

lemma "cs_succ_rer": "(cs, \<sigma>) \<in> set (cs_succ ics) \<Longrightarrow> rer ics \<sigma> cs"
  unfolding cs_succ_def
  sorry

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