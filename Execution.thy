theory Execution imports
  Main HOL.String Deduction
begin

(* 9. (a) *)

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

(* successors of a constraint using Unif rule of rer1 *)
fun c_unify :: "constraint \<Rightarrow> (constraint_system \<times> m_subst) list" where
  "c_unify (M | A \<triangleright> (Var _)) = []"
| "c_unify (M | A \<triangleright> t) = List.maps (\<lambda>u. case m_unify [(t, u)] of Some \<sigma> \<Rightarrow> [([], \<sigma>)] | None \<Rightarrow> []) (M @ A)"

(* soundness of c_unify *)
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

(* successors of a constraint using Comp rules of rer1 *)
fun c_comp :: "constraint \<Rightarrow> (constraint_system \<times> m_subst) list" where
  "c_comp (M | A \<triangleright> Hash t) = [([M | A \<triangleright> t], Var)]"
| "c_comp (M | A \<triangleright> Pair t1 t2) = [([M | A \<triangleright> t1, M | A \<triangleright> t2], Var)]"
| "c_comp (M | A \<triangleright> Sym_encrypt m k) = [([M | A \<triangleright> m, M | A \<triangleright> k], Var)]"
| "c_comp (M | A \<triangleright> Public_key_encrypt m k) = [([M | A \<triangleright> m, M | A \<triangleright> k], Var)]"
| "c_comp (M | A \<triangleright> Signature t (Cons i)) = (if i = \<iota> then [([M | A \<triangleright> t], Var)] else [])"
| "c_comp (M | A \<triangleright> _) = []"

(* soundness of c_comp *)
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

(* helper function for Analysis rules of rer1 providing successors of analyzing one message from M *)
fun "c_dec_term" :: "constraint \<Rightarrow> msg \<Rightarrow> (constraint_system \<times> m_subst) list" where
  "c_dec_term (M | A \<triangleright> t) (Pair u v) = (let M' = removeAll (Pair u v) M in [([(u # v # M') | (Pair u v # A) \<triangleright> t], Var)])"
| "c_dec_term (M | A \<triangleright> t) (Sym_encrypt u k) = (let M' = removeAll (Sym_encrypt u k) M in [([(u # M') | (Sym_encrypt u k # A) \<triangleright> t, M' | (Sym_encrypt u k # A) \<triangleright> k], Var)])"
| "c_dec_term (M | A \<triangleright> t) (Public_key_encrypt u (Cons i)) = (if i = \<iota> then let M' = removeAll (Public_key_encrypt u intruder) M in [([(u # M') | (Public_key_encrypt u intruder # A) \<triangleright> t], Var)] else [])"
| "c_dec_term (M | A \<triangleright> t) (Public_key_encrypt u (Var x)) = (let \<sigma> = Var(x := intruder) in [([c_sapply \<sigma> (M | A \<triangleright> t)], \<sigma>)])"
| "c_dec_term (M | A \<triangleright> t) _ = []"

(* soundness of c_dec_term *)
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

(* successors of a constraint using Analysis rules of rer1 *)
fun "c_dec" :: "constraint \<Rightarrow> (constraint_system \<times> m_subst) list" where
  "c_dec (M | A \<triangleright> t) = List.maps (c_dec_term (M | A \<triangleright> t)) M"

(* soundness of c_dec *)
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

(* successors of a constraint under rer1 *)
definition "c_succ" :: "constraint \<Rightarrow> (constraint_system \<times> m_subst) list" where
  "c_succ c = c_unify c @ c_comp c @ c_dec c"

(* soundness of c_succ *)
lemma "c_succ_rer1":
  assumes "(cs, \<sigma>) \<in> set (c_succ c)"
  shows "rer1 c \<sigma> cs"
proof -
  obtain M A t where "c = M | A \<triangleright> t"
    using assms c_derives.cases by blast
  then show ?thesis
    using assms c_unify_rer1 c_comp_rer1 c_dec_rer1 c_succ_def by auto
qed

(* completeness of c_succ w.r.t. rer1 *)
lemma "c_rer1_succ": "rer1 c \<sigma> cs \<Longrightarrow> (cs, \<sigma>) \<in> set (c_succ c)"
proof (induction rule: rer1.induct)
  case (Unif t M A \<sigma>)
  then obtain u where "u \<in> set (M @ A)" and "m_unify [(t, u)] = Some \<sigma>"
    by auto
  then have "([], \<sigma>) \<in> set (List.maps (\<lambda>u. case m_unify [(t, u)] of Some \<sigma> \<Rightarrow> [([], \<sigma>)] | None \<Rightarrow> []) (M @ A))"
    using exists_maps[of "M @ A" "([], \<sigma>)" "(\<lambda>u. case m_unify [(t, u)] of Some \<sigma> \<Rightarrow> [([], \<sigma>)] | None \<Rightarrow> [])"]
    by force
  then have "([], \<sigma>) \<in> set (c_unify (M | A \<triangleright> t))"
    using Unif(1) is_var.intros
    apply (cases t)
    by force+
  then show ?case
    by (simp add: c_succ_def)
next
  case (Proj u v M M' A t)
  then have "c_dec_term (M | A \<triangleright> t) (Pair u v) = [([(u # v # M') | (Pair u v # A) \<triangleright> t], Var)]"
    by simp
  then have "([(u # v # M') | (Pair u v # A) \<triangleright> t], Var) \<in> set (c_dec (M | A \<triangleright> t))"
    using exists_maps
    by (metis (full_types) Proj.hyps(1) c_dec.simps list.set_intros(1))
  then show ?case
    by (simp add: c_succ_def)
next
  case (Sdec u k M M' A t)
  then have "c_dec_term (M | A \<triangleright> t) (Sym_encrypt u k) = [([(u # M') | (Sym_encrypt u k # A) \<triangleright> t, M' | (Sym_encrypt u k # A) \<triangleright> k], Var)]"
    using c_dec_term.simps(2)
    by metis
  then have "([(u # M') | (Sym_encrypt u k # A) \<triangleright> t, M' | (Sym_encrypt u k # A) \<triangleright> k], Var) \<in> set (c_dec (M | A \<triangleright> t))"
    using exists_maps
    by (metis (full_types) Sdec.hyps(1) c_dec.simps list.set_intros(1))
  then show ?case
    by (simp add: c_succ_def)
next
  case (Adec u M M' A t)
  then have "c_dec_term (M | A \<triangleright> t) (Public_key_encrypt u (Cons \<iota>)) = [([(u # M') | (Public_key_encrypt u intruder # A) \<triangleright> t], Var)]"
    by simp
  then have "([(u # M') | (Public_key_encrypt u intruder # A) \<triangleright> t], Var) \<in> set (c_dec (M | A \<triangleright> t))"
    using exists_maps
    by (metis (full_types) Adec.hyps(1) c_dec.simps intruder_def list.set_intros(1))
  then show ?case
    by (simp add: c_succ_def)
next
  case (Ksub u x M \<sigma> A t)
  then have "c_dec_term (M | A \<triangleright> t) (Public_key_encrypt u (Var x)) = [([c_sapply \<sigma> (M | A \<triangleright> t)], \<sigma>)]"
    using c_dec_term.simps(4)
    by metis
  then have "([c_sapply \<sigma> (M | A \<triangleright> t)], \<sigma>) \<in> set (c_dec (M | A \<triangleright> t))"
    using exists_maps
    by (metis (full_types) Ksub.hyps(1) c_dec.simps list.set_intros(1))
  then show ?case
    by (simp add: c_succ_def)
qed (simp add: c_succ_def intruder_def)+

(* successors of a constraint system under rer, i.e., using rule Context *)
fun "cs_succ_aux" :: "constraint_system \<Rightarrow> constraint_system \<Rightarrow> (constraint_system \<times> m_subst) list" where
  "cs_succ_aux _ [] = []"
| "cs_succ_aux cs' (c # cs'') = map (\<lambda>(cs, \<sigma>). (cs_sapply \<sigma> cs' @ cs @ cs_sapply \<sigma> cs'', \<sigma>)) (c_succ c)
                              @ cs_succ_aux (cs' @ [c]) cs''"

(* helper lemma for soundness of cs_succ_aux_rer *)
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

(* helper lemma for completeness of cs_succ_aux w.r.t. rer1 *)
lemma "cs_rer_succ_aux":
  assumes "rer1 c \<sigma> cs"
  shows "(cs_sapply \<sigma> (pcs @ cs') @ cs @ cs_sapply \<sigma> cs'', \<sigma>) \<in> set (cs_succ_aux pcs (cs' @ [c] @ cs''))"
proof (induction cs' arbitrary: pcs)
  case Nil
  have "(cs, \<sigma>) \<in> set (c_succ c)"
    using assms c_rer1_succ
    by simp
  then show ?case
    using Nil
    by auto
next
  case (Cons a cs')
  then show ?case
    using Cons[of "pcs @ [a]"]
    by simp
qed

(* successors of a constraint system under rer *)
definition "cs_succ" :: "constraint_system \<Rightarrow> (constraint_system \<times> m_subst) list" where
  "cs_succ cs = cs_succ_aux [] cs"

(* soundness of cs_succ *)
lemma "cs_succ_rer": "(cs, \<sigma>) \<in> set (cs_succ ics) \<Longrightarrow> rer ics \<sigma> cs"
  unfolding cs_succ_def
  using cs_succ_aux_rer by fastforce

(* completeness of cs_succ w.r.t. rer *)
lemma "cs_rer_succ": "rer ics \<sigma> cs \<Longrightarrow> (cs, \<sigma>) \<in> set (cs_succ ics)"
  unfolding cs_succ_def
  apply (induction rule: rer.induct)
  subgoal for c \<sigma> cs cs' cs''
    using cs_rer_succ_aux[of c \<sigma> cs "[]" cs' cs'']
    by simp
  done

(* needed for termination proof of search *)
lemma "cs_succ_rer_any": "(cs, \<sigma>) \<in> set (cs_succ ics) \<Longrightarrow> rer_any cs ics"
  using cs_succ_rer rer_any.intros
  by blast

(* 9. (b) *)

(* map a list until an element is mapped to Some _ and return it *)
fun "fold_option" :: "('a \<Rightarrow> 'b option) \<Rightarrow> 'a list \<Rightarrow> 'b option" where
  "fold_option f [] = None"
| "fold_option f (a # as) = (case f a of Some b \<Rightarrow> Some b | None \<Rightarrow> fold_option f as)"

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

lemma "fold_option_cong": "xs = ys \<Longrightarrow> (\<And>a. a \<in> set xs \<Longrightarrow> f a = f' a) \<Longrightarrow> fold_option f xs = fold_option f' ys"
proof (induction xs arbitrary: ys)
  case (Cons a as)
  then obtain a' as' where "ys = a' # as'"
    by blast
  then show ?case
    by (metis Cons.IH Cons.prems(1) Cons.prems(2) fold_option.simps(2) list.set_intros(1) list.set_intros(2))
qed simp

context notes fold_option_cong[fundef_cong] begin
(* main search function *)
function search :: "constraint_system \<Rightarrow> (constraint_system \<times> m_subst) option" where
  "search ics = (if cs_simple ics then Some (ics, Var)
                 else fold_option id (map (\<lambda>(cs, \<sigma>). case search cs of Some (cs', \<sigma>') \<Rightarrow> Some (cs', m_scomp \<sigma>' \<sigma>) | None \<Rightarrow> None) (cs_succ ics)))"
  by pat_completeness auto
termination
  apply (relation "{(x, y). rer_any x y}")
  using rer_any_wf wfP_def apply blast
  using cs_succ_rer_any by auto
end

lemma "fold_option_map": "fold_option id (map f xs) = fold_option f xs"
  apply (induction xs)
   apply simp
  by (metis fold_option.simps(2) id_apply list.simps(9))

(* define fast search code equation for search *)
lemmas search_code[code] = search.simps[unfolded fold_option_map]
(* slow search function *)
definition "search_slow = search"
lemmas search_slow_code[code] = search.simps[folded search_slow_def]

(* 9. (c) *)

(* Key transport protocol *)
definition ktp :: "constraint_system" where
  "ktp = [[Cons ''a'', Cons ''b'', intruder] | [] \<triangleright> Pair (Var ''A0'') (Var ''B0''),
               [Public_key_encrypt (Pair (Cons ''k0'') (Signature (Cons ''k0'') (Var ''A0''))) (Var ''B0''), Cons ''a'', Cons ''b'', intruder] | [] \<triangleright> Public_key_encrypt (Pair (Var ''K1'') (Signature (Var ''K1'') (Cons ''a''))) (Cons ''b''),
               [Sym_encrypt (Cons ''m1'') (Var ''K1''), Public_key_encrypt (Pair (Cons ''k0'') (Signature (Cons ''k0'') (Var ''A0''))) (Var ''B0''), Cons ''a'', Cons ''b'', intruder] | [] \<triangleright> Sym_encrypt (Var ''Z0'') (Cons ''k0''),
               [Sym_encrypt (Cons ''m1'') (Var ''K1''), Public_key_encrypt (Pair (Cons ''k0'') (Signature (Cons ''k0'') (Var ''A0''))) (Var ''B0''), Cons ''a'', Cons ''b'', intruder] | [] \<triangleright> Pair (Var ''K1'') (Cons ''m1'')]"
definition ktp_vars :: "string list" where
  "ktp_vars = [''A0'', ''B0'', ''K1'', ''Z0'']"

(* Needham-Schroeder Public-Key protocol *)
definition nspk :: "constraint_system" where
  "nspk = [[Cons ''a'', Cons ''b'', intruder] | [] \<triangleright> Pair (Var ''A0'') (Var ''B0''),
               [Public_key_encrypt (Pair (Cons ''na0'') (Var ''A0'')) (Var ''B0''), Cons ''a'', Cons ''b'', intruder] | [] \<triangleright> Public_key_encrypt (Pair (Var ''NA1'') (Cons ''a'')) (Cons ''b''),
               [Public_key_encrypt (Pair (Var ''NA1'') (Cons ''nb1'')) (Cons ''a''), Public_key_encrypt (Pair (Cons ''na0'') (Var ''A0'')) (Var ''B0''), Cons ''a'', Cons ''b'', intruder] | [] \<triangleright> Public_key_encrypt (Pair (Cons ''na0'') (Var ''NB0'')) (Var ''A0''),
               [Public_key_encrypt (Var ''NB0'') (Var ''B0''), Public_key_encrypt (Pair (Var ''NA1'') (Cons ''nb1'')) (Cons ''a''), Public_key_encrypt (Pair (Cons ''na0'') (Var ''A0'')) (Var ''B0''), Cons ''a'', Cons ''b'', intruder] | [] \<triangleright> Public_key_encrypt (Cons ''nb1'') (Cons ''b''),
               [Public_key_encrypt (Var ''NB0'') (Var ''B0''), Public_key_encrypt (Pair (Var ''NA1'') (Cons ''nb1'')) (Cons ''a''), Public_key_encrypt (Pair (Cons ''na0'') (Var ''A0'')) (Var ''B0''), Cons ''a'', Cons ''b'', intruder] | [] \<triangleright> Pair (Var ''NA1'') (Cons ''nb1'')]"
definition nspk_vars :: "string list" where
  "nspk_vars = [''A0'', ''B0'', ''NA1'', ''NB0'']"

(* pretty-print functions for exporting the code *)
definition print_list :: "('a \<Rightarrow> string) \<Rightarrow> 'a list \<Rightarrow> string" where
  "print_list f M = ''['' @ foldl (\<lambda>out m. out @ (if out = [] then [] else '', '')  @ f m) [] M @ '']''"

fun print_msg :: "msg \<Rightarrow> string" where
  "print_msg (Cons s) = ''(Cons '' @ s @ '')''"
| "print_msg (Var s) = ''(Var '' @ s @ '')''"
| "print_msg (Hash m) = ''(Hash '' @ print_msg m @ '')''"
| "print_msg (Pair u v) = ''(Pair '' @ print_msg u @ '' '' @ print_msg v @ '')''"
| "print_msg (Sym_encrypt m k) = ''(Sym_encrypt '' @ print_msg m @ '' '' @ print_msg k @ '')''"
| "print_msg (Public_key_encrypt m k) = ''(Public_key_encrypt '' @ print_msg m @ '' '' @ print_msg k @ '')''"
| "print_msg (Signature m k) = ''(Signature '' @ print_msg m @ '' '' @ print_msg k @ '')''"

fun print_c :: "constraint \<Rightarrow> string" where
  "print_c (M | A \<triangleright> t) = ''('' @ print_list print_msg M @ '' | '' @ print_list print_msg A @ '' --> '' @ print_msg t @ '')''"

fun print_search_result :: "(constraint list \<times> (char list \<times> msg) list) option \<Rightarrow> string" where
  "print_search_result None = ''No solution.''"
| "print_search_result (Some (cs, \<sigma>)) = ''Simple constraints: '' @ print_list print_c cs @ ''; Substitutions: '' @ print_list (\<lambda>(s, m). ''('' @ s @ '' --> '' @ print_msg m @ '')'') \<sigma>"

definition print_search :: "string list \<Rightarrow> constraint_system \<Rightarrow> String.literal" where
  "print_search ns cs = String.implode (print_search_result (map_option (\<lambda>(cs, \<sigma>). (cs, map (\<lambda>v. (v, \<sigma> v)) ns)) (search cs)))"

definition print_search_slow :: "string list \<Rightarrow> constraint_system \<Rightarrow> String.literal" where
  "print_search_slow ns cs = String.implode (print_search_result (map_option (\<lambda>(cs, \<sigma>). (cs, map (\<lambda>v. (v, \<sigma> v)) ns)) (search_slow cs)))"

definition "print_search_KTP = print_search ktp_vars ktp"
definition "print_search_slow_KTP = print_search_slow ktp_vars ktp"

definition "print_search_NSPK = print_search nspk_vars nspk"
definition "print_search_slow_NSPK = print_search_slow nspk_vars nspk"

value "print_search_KTP"
(* value "print_search_slow_KTP" *)

value "print_search_NSPK"
(* value "print_search_slow_NSPK" *)

export_code print_search_KTP print_search_slow_KTP print_search_NSPK print_search_slow_NSPK in Haskell module_name Search file "./ghc"
export_code print_search print_search_slow ktp_vars ktp nspk_vars nspk in SML module_name Search file "./sml/Search.sml"

(* 10. (a) *)

(* soundness of search *)
lemma "search_sound":
  assumes "search ics = Some (cs', \<sigma>'')"
  shows "rer_star ics \<sigma>'' cs' \<and> cs_simple cs'"
  using assms
  apply (induction arbitrary: cs' \<sigma>'' rule: search.induct)
  subgoal premises prems for ics cs' \<sigma>''
    using prems
    proof (cases "cs_simple ics")
      case False
      then have "search ics = fold_option (\<lambda>(cs, \<sigma>). case search cs of Some (cs', \<sigma>') \<Rightarrow> Some (cs', m_scomp \<sigma>' \<sigma>) | None \<Rightarrow> None) (cs_succ ics)"
        by (simp add: fold_option_map)
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

(* completeness of search w.r.t. rer_star *)
lemma "search_complete":
  assumes "rer_star ics \<sigma>'' cs'" and "cs_simple cs'"
  shows "\<exists>x. search ics = Some x"
  using assms
  apply (induction rule: rer_star.induct)
   apply simp
  subgoal premises prems for ics \<sigma> cs \<sigma>' cs'
    using prems
    proof (cases "cs_simple ics")
      case False
      have $: "(cs, \<sigma>) \<in> set (cs_succ ics)"
        using prems(1)
        by (simp add: cs_rer_succ)
      obtain css' \<sigma>s' where "search cs = Some (css', \<sigma>s')"
        using prems
        by auto
      then have "\<exists>x \<in> set (cs_succ ics). \<not>Option.is_none ((\<lambda>(cs, \<sigma>). case search cs of Some (cs', \<sigma>') \<Rightarrow> Some (cs', m_scomp \<sigma>' \<sigma>) | None \<Rightarrow> None) x)"
        using $
        by force
      then have "\<exists>z. z \<noteq> None \<and> search ics = z"
        using False exists_fold_option[of "(cs_succ ics)" "(\<lambda>(cs, \<sigma>). case search cs of Some (cs', \<sigma>') \<Rightarrow> Some (cs', m_scomp \<sigma>' \<sigma>) | None \<Rightarrow> None)"]
        by (simp add: Option.is_none_def fold_option_map)
      then show ?thesis
        by blast
    qed simp
  done

end