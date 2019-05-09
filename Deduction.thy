theory Deduction imports
  Main Term
begin

(* 6. (a) *)

definition intruder :: msg where
  "intruder = Cons ''intruder''"

inductive deduce :: "msg set \<Rightarrow> msg \<Rightarrow> bool" (infix "\<turnstile>" 72) where
  Ax[intro]: "u \<in> T \<Longrightarrow> T \<turnstile> u"
| Proj1[intro]: "T \<turnstile> Pair u1 u2 \<Longrightarrow> T \<turnstile> u1"
| Proj2[intro]: "T \<turnstile> Pair u1 u2 \<Longrightarrow> T \<turnstile> u2"
| Hash[intro]: "T \<turnstile> u \<Longrightarrow> T \<turnstile> Hash u"
| Pair[intro]: "T \<turnstile> u1 \<Longrightarrow> T \<turnstile> u2 \<Longrightarrow> T \<turnstile> Pair u1 u2"
| Senc[intro]: "T \<turnstile> m \<Longrightarrow> T \<turnstile> k \<Longrightarrow> T \<turnstile> Sym_encrypt m k"
| Aenc[intro]: "T \<turnstile> m \<Longrightarrow> T \<turnstile> k \<Longrightarrow> T \<turnstile> Public_key_encrypt m k"
| Sig[intro]: "T \<turnstile> m \<Longrightarrow> T \<turnstile> Signature m intruder"
| Sdec[intro]: "T \<turnstile> Sym_encrypt m k \<Longrightarrow> T \<turnstile> k \<Longrightarrow> T \<turnstile> m"
| Adec[intro]: "T \<turnstile> Public_key_encrypt m intruder \<Longrightarrow> T \<turnstile> m"

lemma "{Sym_encrypt m x, x} \<turnstile> m"
  by auto
lemma "{Pair u1 u2} \<turnstile> Hash (Pair u2 u1)"
  apply(rule Hash)
    by(rule Pair) auto
lemma "{Sym_encrypt m k, Public_key_encrypt k intruder} \<turnstile> Pair m (Signature m intruder)"
  apply (rule Pair)
   apply (rule Sdec)
    prefer 2 apply (rule Adec)
    prefer 3 apply (rule Sig)
    apply (rule Sdec)
     prefer 2 apply (rule Adec)
  by auto

(* 6. (b) *)

lemma deduce_weaken:
  assumes "G \<turnstile> t" and "G \<subseteq> H"
  shows "H \<turnstile> t"
  using assms
  by (induction rule: deduce.induct) auto

lemma deduce_cut_aux:
  assumes "T \<turnstile> u" and "H \<turnstile> t" and "T = insert t H"
  shows "H \<turnstile> u"
  using assms
  by (induction rule: deduce.induct) auto

lemma deduce_cut:
  assumes "insert t H \<turnstile> u" and "H \<turnstile> t"
  shows "H \<turnstile> u"
  using assms deduce_cut_aux by blast

(* 7. (a) *)

datatype constraint = Constraint "msg list" "msg list" "msg" ("((2_/|_)/\<triangleright>_)" [67,67,67]66)
type_synonym constraint_system = "constraint list"

fun c_fv :: "constraint \<Rightarrow> string set" where
  "c_fv (Constraint ms ms' msg) = \<Union>(m_fv ` (set ms \<union> set ms' \<union> {msg}))"

lemma "c_fv_finite": "finite (c_fv c)"
  apply (cases c)
  by (simp add: m_fv_finite)

fun c_sapply :: "m_subst \<Rightarrow> constraint \<Rightarrow> constraint" where
  "c_sapply \<sigma> (Constraint ms ms' msg) = Constraint (map (m_sapply \<sigma>) ms) (map (m_sapply \<sigma>) ms') (m_sapply \<sigma> msg)"

lemma "c_sapply_id": "c_sapply Var = id"
  apply (rule ext)
  subgoal for c
    apply (cases c)
    using m_sapply_id
    by simp
  done

fun c_derives :: "constraint \<Rightarrow> bool" where
  "c_derives (Constraint ms ms' msg) = (set ms \<union> set ms') \<turnstile> msg"

lemma "c_sapply_comp": "c_sapply \<tau> (c_sapply \<sigma> c) = c_sapply (\<tau> \<circ>m \<sigma>) c"
  using m_sapply_comp
  by (cases c) simp

definition cs_fv :: "constraint_system \<Rightarrow> string set" where
  "cs_fv cs = \<Union>(c_fv ` set cs)"

lemma "cs_fv_finite": "finite (cs_fv cs)"
  by (simp add: c_fv_finite cs_fv_def)

definition cs_sapply :: "m_subst \<Rightarrow> constraint_system \<Rightarrow> constraint_system" where
  "cs_sapply \<sigma> cs = map (c_sapply \<sigma>) cs"

lemma "cs_sapply_id": "cs_sapply Var = id"
  apply (rule ext)
  subgoal for cs
    unfolding cs_sapply_def
    by (simp add: c_sapply_id)
  done

definition cs_derives :: "constraint_system \<Rightarrow> bool" where
  "cs_derives cs = list_all c_derives cs"

(* 7. (b) *)

type_synonym sol_set = "m_subst set"
definition sol :: "constraint_system \<Rightarrow> sol_set" where
  "sol cs = {\<sigma> | \<sigma>. cs_derives (cs_sapply \<sigma> cs)}"

lemma "sol_cs_union": "sol (cs @ cs') = (sol cs) \<inter> (sol cs')"
  unfolding sol_def cs_sapply_def cs_derives_def
  by (rule set_eqI) auto

lemma "sol_c_sapply": "\<tau> \<in> sol [c_sapply \<sigma> c] \<Longrightarrow> \<tau> \<circ>m \<sigma> \<in> sol [c]"
  unfolding sol_def cs_sapply_def cs_derives_def
  by (simp add: c_sapply_comp)

lemma "sol_cs_sapply": "\<tau> \<in> sol (cs_sapply \<sigma> cs) \<Longrightarrow> \<tau> \<circ>m \<sigma> \<in> sol cs"
  unfolding sol_def cs_sapply_def cs_derives_def
  by (simp add: c_sapply_comp list_all_length)

lemma "sol_sapply": "(m_sapply \<tau> ` (set M \<union> set A) \<turnstile> m_sapply \<tau> t) = (\<tau> \<in> sol [M | A \<triangleright> t])"
  unfolding sol_def cs_derives_def cs_sapply_def
  apply (rule iffI)
   apply auto
   by (simp add: image_Un)+

lemma "sol_fst": "\<tau> \<in> sol [c1, c2] \<Longrightarrow> \<tau> \<in> sol [c1]"
  using sol_cs_union
  by fastforce

lemma "sol_snd": "\<tau> \<in> sol [c1, c2] \<Longrightarrow> \<tau> \<in> sol [c2]"
  using sol_cs_union
  by (metis (full_types) IntE append_Cons append_Nil)

(* 7. (c) *)

inductive rer1 :: "constraint \<Rightarrow> m_subst \<Rightarrow> constraint_system \<Rightarrow> bool" ("_/\<leadsto>\<^sub>1[_]/_" [64,64,64]63) where
  Unif: "\<not>is_var t \<Longrightarrow> \<exists>u \<in> set M \<union> set A. m_unify [(t, u)] = Some \<sigma>  \<Longrightarrow> rer1 (M | A \<triangleright> t) \<sigma> []"
| Comp_Hash: "rer1 (M | A \<triangleright> Hash t) Var [M | A \<triangleright> t]"
| Comp_Pair: "rer1 (M | A \<triangleright> Pair t1 t2) Var [M | A \<triangleright> t1, M | A \<triangleright> t2]"
| Comp_Sym_encrypt: "rer1 (M | A \<triangleright> Sym_encrypt m k) Var [M | A \<triangleright> m, M | A \<triangleright> k]"
| Comp_Public_key_encrypt: "rer1 (M | A \<triangleright> Public_key_encrypt m k) Var [M | A \<triangleright> m, M | A \<triangleright> k]"
| Comp_Signature: "rer1 (M | A \<triangleright> Signature t intruder) Var [M | A \<triangleright> t]"
| Proj: "Pair u v \<in> set M \<Longrightarrow> M' = removeAll (Pair u v) M \<Longrightarrow> rer1 (M | A \<triangleright> t) Var [(u # v # M') | (Pair u v # A) \<triangleright> t]"
| Sdec: "Sym_encrypt u k \<in> set M \<Longrightarrow> M' = removeAll (Sym_encrypt u k) M \<Longrightarrow> rer1 (M | A \<triangleright> t) Var [(u # M') | (Sym_encrypt u k # A) \<triangleright> t, M' | (Sym_encrypt u k # A) \<triangleright> k]"
| Adec: "Public_key_encrypt u intruder \<in> set M \<Longrightarrow> M' = removeAll (Public_key_encrypt u intruder) M \<Longrightarrow> rer1 (M | A \<triangleright> t) Var [(u # M') | (Public_key_encrypt u intruder # A) \<triangleright> t]"
| Ksub: "Public_key_encrypt u (Var x) \<in> set M \<Longrightarrow> \<sigma> = Var(x := intruder) \<Longrightarrow> rer1 (M | A \<triangleright> t) \<sigma> [c_sapply \<sigma> (M | A \<triangleright> t)]"

inductive rer :: "constraint_system \<Rightarrow> m_subst \<Rightarrow> constraint_system \<Rightarrow> bool" ("_/\<leadsto>[_]/_" [73,73,73]72) where
  Context: "rer1 c \<sigma> cs \<Longrightarrow> c \<notin> set cs' \<Longrightarrow> rer (c # cs') \<sigma> (cs @ cs_sapply \<sigma> cs')"

inductive rer_star :: "constraint_system \<Rightarrow> m_subst \<Rightarrow> constraint_system \<Rightarrow> bool" ("_/\<leadsto>*[_]/_" [73,73,73]72) where
  Refl: "rer_star cs Var cs"
| Trans: "rer cs \<sigma> cs' \<Longrightarrow> rer_star cs' \<tau> cs'' \<Longrightarrow> rer_star cs (\<tau> \<circ>m \<sigma>) cs''"

(* 7. (d) *)

inductive c_simple :: "constraint \<Rightarrow> bool" where
  "c_simple (M | A \<triangleright> (Var _))"

definition cs_simple :: "constraint_system \<Rightarrow> bool" where
  "cs_simple cs = list_all c_simple cs"

definition red :: "constraint_system \<Rightarrow> m_subst set" where
  "red cs = {m_scomp \<tau> \<sigma> | \<tau> \<sigma>. \<exists>cs'. rer_star cs \<sigma> cs' \<and> cs_simple cs' \<and> \<tau> \<in> sol cs'}"

(* 8. (a) *)

lemma "m_subst_intruder": "m_sapply \<tau> intruder = intruder"
  unfolding intruder_def
  by simp

lemma "rer1_sound": "rer1 c \<sigma> cs \<Longrightarrow> \<tau> \<in> sol cs \<Longrightarrow> \<tau> \<circ>m \<sigma> \<in> sol [c]"
proof (induction rule: rer1.induct)
  case (Unif t M A \<sigma>)
  then obtain "u" where u_in_M_A: "u \<in> set M \<union> set A" and "m_unify [(t, u)] = Some \<sigma>" by auto
  then have "m_sapply \<sigma> t = m_sapply \<sigma> u" using m_soundness1 m_unifiess.cases m_unifies.cases by blast
  then have "m_sapply (\<tau> \<circ>m \<sigma>) t = m_sapply (\<tau> \<circ>m \<sigma>) u" using m_sapply_comp by metis
  then have "m_sapply (\<tau> \<circ>m \<sigma>) ` {u} \<turnstile> m_sapply (\<tau> \<circ>m \<sigma>) t" using Ax by simp
  then have "m_sapply (\<tau> \<circ>m \<sigma>) ` (set M \<union> set A) \<turnstile> m_sapply (\<tau> \<circ>m \<sigma>) t" using u_in_M_A deduce_weaken by auto
  then show ?case unfolding sol_def cs_derives_def cs_sapply_def by (simp add: image_Un)
next
  case (Comp_Hash M A t)
  then show ?case
    unfolding sol_def cs_derives_def cs_sapply_def
    by auto
next
  case (Comp_Pair M A t1 t2)
  then show ?case
    unfolding sol_def cs_derives_def cs_sapply_def
    by auto
next
  case (Comp_Sym_encrypt M A m k)
  then show ?case
    unfolding sol_def cs_derives_def cs_sapply_def
    by auto
next
  case (Comp_Public_key_encrypt M A m k)
  then show ?case
    unfolding sol_def cs_derives_def cs_sapply_def
    by auto
next
  case (Comp_Signature M A t)
  then show ?case
    unfolding sol_def cs_derives_def cs_sapply_def
    using m_subst_intruder
    by auto
next
  case (Proj u v M M' A t)
  then have "rem": "set M' \<union> set (Pair u v # A) = set M \<union> set A"
    by auto
  have "tau_t": "m_sapply \<tau> ` (set (u # v # M') \<union> set (Pair u v # A)) \<turnstile> m_sapply \<tau> t"
    using Proj.prems sol_sapply by blast
  have "m_sapply \<tau> ` (set (v # M') \<union> set (Pair u v # A)) \<turnstile> m_sapply \<tau> u"
    by auto
  then have "tau_t'": "m_sapply \<tau> ` (set (v # M') \<union> set (Pair u v # A)) \<turnstile> m_sapply \<tau> t"
    by (metis Un_insert_left deduce_cut_aux image_insert list.simps(15) tau_t)
  have "m_sapply \<tau> ` (set M' \<union> set (Pair u v # A)) \<turnstile> m_sapply \<tau> v"
    by auto
  then have "m_sapply \<tau> ` (set M' \<union> set (Pair u v # A)) \<turnstile> m_sapply \<tau> t"
    by (metis Un_insert_left deduce_cut image_insert list.simps(15) tau_t')
  then show ?case
    by (metis cs_sapply_id id_apply rem sol_sapply sol_cs_sapply)
next
  case (Sdec u k M M' A t)
  then have "rem": "set M' \<union> set (Sym_encrypt u k # A) = set M \<union> set A"
    by auto
  have "tau_t": "m_sapply \<tau> ` (set (u # M') \<union> set (Sym_encrypt u k # A)) \<turnstile> m_sapply \<tau> t"
    using Sdec.prems sol_fst sol_sapply by blast
  have "m_sapply \<tau> ` (set M' \<union> set (Sym_encrypt u k # A)) \<turnstile> m_sapply \<tau> k"
    using Sdec.prems sol_sapply sol_snd by blast
  then have "m_sapply \<tau> ` (set M' \<union> set (Sym_encrypt u k # A)) \<turnstile> m_sapply \<tau> u"
    by auto
  then have "m_sapply \<tau> ` (set M \<union> set A) \<turnstile> m_sapply \<tau> t"
    by (metis Un_insert_left deduce_cut_aux image_insert list.simps(15) rem tau_t)
  then show ?case
    by (simp add: sol_sapply)
next
  case (Adec u M M' A t)
  then have "rem": "set (Public_key_encrypt u intruder # M') \<union> set A = set M \<union> set A"
    by auto
  have "tau_t": "m_sapply \<tau> ` (set (u # M') \<union> set (Public_key_encrypt u intruder # A)) \<turnstile> m_sapply \<tau> t"
    using Adec.prems sol_sapply by blast
  have "m_sapply \<tau> ` (set (Public_key_encrypt u intruder # M') \<union> set A) \<turnstile> m_sapply \<tau> u"
    by (simp add: Ax deduce.Adec m_subst_intruder)
  then have "m_sapply \<tau> ` (set M \<union> set A) \<turnstile> m_sapply \<tau> t"
    by (metis (no_types, lifting) Un_commute Un_insert_left deduce_cut_aux image_insert list.simps(15) rem tau_t)
  then show ?case
    by (simp add: sol_sapply)
next
  case (Ksub u x M \<sigma> A t)
  then show ?case
    using sol_c_sapply
    by blast
qed

lemma "rer_sound": "rer cs \<sigma> cs' \<Longrightarrow> \<tau> \<in> sol cs' \<Longrightarrow> \<tau> \<circ>m \<sigma> \<in> sol cs"
  apply (induction rule: rer.induct)
  using sol_cs_union sol_cs_sapply rer1_sound
  by (metis (full_types) IntE IntI append_Cons append_Nil)

lemma "rer_star_sound": "rer_star cs \<sigma> cs' \<Longrightarrow> cs_simple cs' \<Longrightarrow> \<tau> \<in> sol cs' \<Longrightarrow> \<tau> \<circ>m \<sigma> \<in> sol cs"
  using rer_sound m_sapply_comp
  apply -
  by (induction rule: rer_star.induct) auto

theorem "cs_sound": "red cs \<subseteq> sol cs"
  unfolding red_def
  using rer_star_sound
  by auto

(* 8. (b) *)

fun \<Theta> :: "msg \<Rightarrow> nat" where
  "\<Theta> (Hash t) = \<Theta> t + 1"
| "\<Theta> (Pair u v) = \<Theta> u + \<Theta> v + 1"
| "\<Theta> (Sym_encrypt m k) = \<Theta> m + \<Theta> k + 1"
| "\<Theta> (Public_key_encrypt m k) = \<Theta> m + \<Theta> k + 1"
| "\<Theta> (Signature m k) = (if k = intruder then \<Theta> m + \<Theta> k + 1 else 1)"
| "\<Theta> _ = 1"

fun \<chi> :: "msg \<Rightarrow> nat" where
  "\<chi> (Hash t) = \<chi> t + 1"
| "\<chi> (Pair u v) = \<chi> u * \<chi> v + 1"
| "\<chi> (Sym_encrypt m k) = \<chi> m + \<Theta> k + 1"
| "\<chi> (Public_key_encrypt m k) = \<chi> m + 1"
| "\<chi> (Signature m k) = \<chi> m + 1"
| "\<chi> _ = 1"

definition \<chi>' :: "msg set \<Rightarrow> nat" where
  "\<chi>' M = (\<Prod>m \<in> M. \<chi> m)"

fun w :: "constraint \<Rightarrow> nat" where
  "w (M | A \<triangleright> t) = \<chi>' (set M) * \<Theta> t"

definition \<eta>1 :: "constraint_system \<Rightarrow> nat" where
  "\<eta>1 cs = card (cs_fv cs)"

definition \<eta>2 :: "constraint_system \<Rightarrow> nat" where
  "\<eta>2 cs = (\<Sum>c \<in> set cs. w c)"

lemma "rer1_fv_sub": "rer1 c \<sigma> cs \<Longrightarrow> cs_fv (cs @ cs_sapply \<sigma> cs') \<subseteq> cs_fv (c # cs')"
  sorry

lemma "rer1_fv_neq": "rer1 c \<sigma> cs \<Longrightarrow> \<sigma> \<noteq> Var \<Longrightarrow> cs_fv (cs @ cs_sapply \<sigma> cs') \<noteq> cs_fv (c # cs')"
  sorry

lemma "rer1_measure_lt": "rer1 c Var cs \<Longrightarrow> \<eta>2 cs < w c"
  sorry

definition "term_rel" :: "(constraint_system \<times> constraint_system) set" where
  "term_rel = \<eta>1 <*mlex*> measure \<eta>2"

lemma "term_rel_wf": "wf term_rel"
  unfolding term_rel_def
  by (simp add: wf_mlex)

inductive "rer_any" :: "constraint_system \<Rightarrow> constraint_system \<Rightarrow> bool" where
  "rer cs \<sigma> cs' \<Longrightarrow> rer_any cs' cs"

lemma "rer1_\<eta>1": "rer cs \<sigma> cs' \<Longrightarrow> \<eta>1 cs' \<le> \<eta>1 cs"
  unfolding \<eta>1_def
  by (metis card_mono cs_fv_finite rer.simps rer1_fv_sub)

lemma "rer1_\<eta>1'": "rer cs \<sigma> cs' \<Longrightarrow> \<sigma> \<noteq> Var \<Longrightarrow> \<eta>1 cs' < \<eta>1 cs"
  unfolding \<eta>1_def
  by (metis cs_fv_finite le_neq_trans psubset_card_mono rer.simps rer1_fv_neq rer1_fv_sub)

lemma "rer1_\<eta>2": "rer cs \<sigma> cs' \<Longrightarrow> \<sigma> = Var \<Longrightarrow> \<eta>2 cs' < \<eta>2 cs"
  unfolding \<eta>2_def
proof (induction rule: rer.induct)
  case (Context c \<sigma> cs cs')
  then have eq: "sum w (set (c # cs')) = w c + sum w (set cs')"
    by auto
  have "cs_sapply \<sigma> cs' = cs'"
    by (simp add: Context.prems cs_sapply_id)
  then have "sum w (set (cs @ cs_sapply \<sigma> cs')) \<le> sum w (set cs) + sum w (set cs')"
    by (metis List.finite_set le_add1 set_append sum.union_inter)
  then show ?case
    using Context.hyps(1) Context.prems(1) \<eta>2_def eq rer1_measure_lt
    by fastforce
qed

lemma "rer_any_term": "rer_any cs' cs \<Longrightarrow> (cs', cs) \<in> term_rel"
  unfolding term_rel_def
  by (metis in_measure mlex_leq mlex_less rer1_\<eta>1 rer1_\<eta>1' rer1_\<eta>2 rer_any.cases)

theorem "rer_any_wf": "wfP rer_any"
  by (metis rer_any_term term_rel_wf wfE_min wfP_eq_minimal)

end