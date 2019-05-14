theory Deduction imports
  Main Term
begin

(* 6. (a) *)

definition \<iota> :: string where
  "\<iota> = ''intruder''"

definition intruder :: msg where
  "intruder = Cons \<iota>"

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
  apply (rule Hash)
    by (rule Pair) auto
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

lemma "c_fv_sapply_sdom_svran":
  assumes "x \<in> c_fv (c_sapply \<sigma> c)"
  shows "x \<in> (c_fv c - m_sdom \<sigma>) \<union> m_svran \<sigma>"
  using assms m_fv_sapply_sdom_svran
  apply (cases c)
  by simp blast

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

lemma "cs_fv_sapply_sdom_svran":
  assumes "x \<in> cs_fv (cs_sapply \<sigma> cs)"
  shows "x \<in> (cs_fv cs - m_sdom \<sigma>) \<union> m_svran \<sigma>"
proof -
  obtain "c" where "x \<in> c_fv (c_sapply \<sigma> c)" and $: "c \<in> set cs"
    using assms
    unfolding cs_fv_def cs_sapply_def
    by auto
  then have "x \<in> (c_fv c - m_sdom \<sigma>) \<union> m_svran \<sigma>"
    using c_fv_sapply_sdom_svran
    by blast
  then show ?thesis
    using $ cs_fv_def by auto
qed

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
  Context: "rer1 c \<sigma> cs \<Longrightarrow> rer (cs' @ (c # cs'')) \<sigma> (cs_sapply \<sigma> cs' @ cs @ cs_sapply \<sigma> cs'')"

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

lemma "\<Theta>_pos": "\<Theta> m \<ge> 1"
  by (induction m) auto

fun \<chi> :: "msg \<Rightarrow> nat" where
  "\<chi> (Hash t) = \<chi> t + 1"
| "\<chi> (Pair u v) = \<chi> u * \<chi> v + 1"
| "\<chi> (Sym_encrypt m k) = \<chi> m + \<Theta> k + 1"
| "\<chi> (Public_key_encrypt m k) = \<chi> m + 1"
| "\<chi> (Signature m k) = \<chi> m + 1"
| "\<chi> _ = 1"

lemma "\<chi>_pos": "\<chi> m \<ge> 1"
  by (induction m) auto

definition \<chi>' :: "msg list \<Rightarrow> nat" where
  "\<chi>' M = prod_list (map \<chi> M)"

lemma "\<chi>'_pos": "\<chi>' M \<ge> 1"
  unfolding \<chi>'_def
  apply (induction M)
   apply simp_all
  using One_nat_def \<chi>_pos by presburger

lemma "\<chi>'_incl": "m \<in> set M \<Longrightarrow> M' = removeAll m M \<Longrightarrow> \<chi>' (m # M') \<le> \<chi>' M"
  unfolding \<chi>'_def
  apply (induction M arbitrary: M')
   apply simp
  subgoal premises prems for a M M'
  proof (cases "m = a")
    case True
    then have "M' = removeAll m M" using prems(3) by simp
    then have "prod_list (map \<chi> M') \<le> prod_list (map \<chi> M)" by (metis \<chi>'_def \<chi>'_pos less_le_trans list.simps(8) list.simps(9) mult.commute mult.right_neutral nat_mult_le_cancel_disj not_le prems(1) prod_list.Cons prod_list.Nil removeAll_id)
    then show ?thesis
      using True
      by simp
  next
    case False
    then have "m \<in> set M" using prems False by simp
    then have "prod_list (map \<chi> (m # a # (removeAll m M))) \<le> prod_list (map \<chi> (a # M))" using prems by auto
    then show ?thesis
      using False prems(3)
      by simp
  qed
  done

lemma "\<chi>'_pref": "\<chi>' P < \<chi>' P' \<Longrightarrow> \<chi>' (P @ M) < \<chi>' (P' @ M)"
  unfolding "\<chi>'_def"
  apply (induction M)
   apply simp_all
  using \<chi>_pos less_le_trans by auto

fun w :: "constraint \<Rightarrow> nat" where
  "w (M | A \<triangleright> t) = \<chi>' M * \<Theta> t"

lemma "w_pos": "w c \<ge> 1"
  using \<chi>'_pos \<Theta>_pos
  by (metis (full_types) c_derives.cases less_one mult_is_0 not_less w.simps)

definition \<eta>1 :: "constraint_system \<Rightarrow> nat" where
  "\<eta>1 cs = card (cs_fv cs)"

definition \<eta>2 :: "constraint_system \<Rightarrow> nat" where
  "\<eta>2 cs = sum_list (map w cs)"

lemma "m_fv_intruder_sub": "\<sigma> = Var(x := intruder) \<Longrightarrow> m_fv (m_sapply \<sigma> m) \<subseteq> m_fv m"
  unfolding intruder_def
  by (induction m) auto

lemma "c_fv_intruder_sub": "\<sigma> = Var(x := intruder) \<Longrightarrow> c_fv (c_sapply \<sigma> c) \<subseteq> c_fv c"
  apply (cases c)
  using m_fv_intruder_sub by fastforce+

lemma "rer1_fv_sub_cs_aux": "rer1 c \<sigma> cs \<Longrightarrow> cs_fv cs \<subseteq> cs_fv (c # cs'')"
  unfolding cs_fv_def cs_sapply_def
  using c_fv_intruder_sub
  apply -
proof (induction rule: rer1.induct)
  case (Ksub u x M \<sigma> A t)
  then show ?case
    apply safe
    by (metis Union_iff image_iff list.distinct(1) list.set_cases list.set_intros(1) set_ConsD subsetCE)
qed auto

lemma "rer1_fv_sub_cs": "rer1 c \<sigma> cs \<Longrightarrow> cs_fv cs \<subseteq> cs_fv (cs' @ (c # cs''))"
  using rer1_fv_sub_cs_aux
  using cs_fv_def by fastforce

lemma "rer1_fv_sub_cs'": "rer1 c \<sigma> cs \<Longrightarrow> cs_fv (cs_sapply \<sigma> cs' @ cs_sapply \<sigma> cs'') \<subseteq> cs_fv (cs' @ (c # cs''))"
  unfolding cs_fv_def cs_sapply_def
  using cs_sapply_id c_sapply_id
  apply -
proof (induction rule: rer1.induct)
  case (Unif t M A \<sigma>)
  then obtain "u" where $: "u \<in> set M \<union> set A" and "m_unify [(t, u)] = Some \<sigma>"
    by auto
  then have "m_svran \<sigma> \<subseteq> m_fv_eq (t, u)"
    using m_lemma_3 m_fv_eqs.simps
    by blast
  then have "m_svran \<sigma> \<subseteq> c_fv (M | A \<triangleright> t)"
    using $
    by auto
  then have "cs_fv (cs_sapply \<sigma> (cs' @ cs'')) \<subseteq> cs_fv (cs' @ cs'') \<union> c_fv (M | A \<triangleright> t)"
    using cs_fv_sapply_sdom_svran
    by blast
  then show ?case
    unfolding cs_fv_def cs_sapply_def
    by auto
next
  case (Ksub u x M \<sigma> A t)
  show ?case
    apply (rule subsetI)
    apply simp
    using Ksub.hyps(2) c_fv_intruder_sub by blast
qed auto

lemma "rer1_fv_sub": "rer1 c \<sigma> cs \<Longrightarrow> cs_fv (cs_sapply \<sigma> cs' @ cs @ cs_sapply \<sigma> cs'') \<subseteq> cs_fv (cs' @ (c # cs''))"
  using rer1_fv_sub_cs rer1_fv_sub_cs'
  unfolding cs_fv_def
  by auto

lemma "rer1_fv_neq": "rer1 c \<sigma> cs \<Longrightarrow> \<sigma> \<noteq> Var \<Longrightarrow> cs_fv (cs_sapply \<sigma> cs' @ cs @ cs_sapply \<sigma> cs'') \<noteq> cs_fv (cs' @ (c # cs''))"
proof (induction rule: rer1.induct)
  case (Unif t M A \<sigma>)
  then obtain "u" "x" where $: "u \<in> set M \<union> set A" and "m_un": "m_unify [(t, u)] = Some \<sigma>" and "x_m_sdom": "x \<in> m_sdom \<sigma>"
    by force
  then have "m_sdom \<sigma> \<subseteq> m_fv_eq (t, u)"
    using m_fv_eqs.simps m_lemma_3 by blast
  then have "m_sdom \<sigma> \<subseteq> c_fv (M | A \<triangleright> t)"
    using $
    by auto
  then have "x_cs_fv": "x \<in> cs_fv (cs' @ (M | A \<triangleright> t) # cs'')"
    unfolding cs_fv_def
    using "x_m_sdom"
    by auto
  have "cs_sub": "cs_fv (cs_sapply \<sigma> cs' @ cs_sapply \<sigma> cs'') \<subseteq> cs_fv (cs' @ cs'') - m_sdom \<sigma> \<union> m_svran \<sigma>"
    using cs_fv_sapply_sdom_svran
    by (simp add: cs_sapply_def subsetI)
  have "m_sdom \<sigma> \<inter> m_svran \<sigma> = {}"
    using m_lemma_3 m_un
    by blast
  then have "x \<notin> cs_fv (cs_sapply \<sigma> cs' @ [] @ cs_sapply \<sigma> cs'')"
    using cs_fv_sapply_sdom_svran cs_sub x_m_sdom
    by auto
  then show ?case
    using "x_cs_fv"
    unfolding cs_fv_def
    by auto
next
  case (Ksub u x M \<sigma> A t)
  then have "x_in_cs_fv": "x \<in> cs_fv (cs' @ (M | A \<triangleright> t # cs''))"
    unfolding cs_fv_def
    by fastforce
  have "x \<in> m_sdom \<sigma> - m_svran \<sigma>"
    using Ksub.hyps
    unfolding intruder_def
    by simp
  then have "x \<notin> cs_fv (cs_sapply \<sigma> (cs' @ (M | A \<triangleright> t) # cs''))"
    using Ksub.hyps cs_fv_sapply_sdom_svran
    unfolding cs_fv_def cs_sapply_def
    by blast
  then show ?case
    using x_in_cs_fv
    unfolding cs_fv_def cs_sapply_def
    by auto
qed auto

lemma "rer1_measure_lt": "rer1 c \<sigma> cs \<Longrightarrow> \<sigma> = Var \<Longrightarrow> \<eta>2 cs < w c"
  unfolding \<eta>2_def
proof (induction rule: rer1.induct)
  case (Unif t M A \<sigma>)
  then have "sum_list (map w []) = 0" by simp
  also have "0 < w (M | A \<triangleright> t)" using less_le_trans w_pos by blast
  finally show ?case by blast
next
  case (Comp_Hash M A t)
  then have "sum_list (map w [M | A \<triangleright> t]) = w (M | A \<triangleright> t)" by simp
  also have "... = \<chi>' M * \<Theta> t" by simp
  also have "... < \<chi>' M * \<Theta> (Hash t)" using \<chi>'_pos less_le_trans by auto
  finally show ?case by auto
next
  case (Comp_Pair M A t1 t2)
  then have "sum_list (map w [M | A \<triangleright> t1, M | A \<triangleright> t2]) = w (M | A \<triangleright> t1) + w (M | A \<triangleright> t2)" by simp
  also have "... = \<chi>' M * \<Theta> t1 + \<chi>' M * \<Theta> t2" by simp
  also have "... < \<chi>' M * \<Theta> (Pair t1 t2)" using \<chi>'_pos add_mult_distrib2 less_le_trans by fastforce
  finally show ?case by auto
next
  case (Comp_Sym_encrypt M A m k)
  then have "sum_list (map w [M | A \<triangleright> m, M | A \<triangleright> k]) = w (M | A \<triangleright> m) + w (M | A \<triangleright> k)" by simp
  also have "... = \<chi>' M * \<Theta> m + \<chi>' M * \<Theta> k" by simp
  also have "... < \<chi>' M * \<Theta> (Sym_encrypt m k)" using \<chi>'_pos add_mult_distrib2 less_le_trans by fastforce
  finally show ?case by auto
next
  case (Comp_Public_key_encrypt M A m k)
  have "sum_list (map w [M | A \<triangleright> m, M | A \<triangleright> k]) = w (M | A \<triangleright> m) + w (M | A \<triangleright> k)" by simp
  also have "... = \<chi>' M * \<Theta> m + \<chi>' M * \<Theta> k" by simp
  also have "... < \<chi>' M * \<Theta> (Public_key_encrypt m k)" using \<chi>'_pos add_mult_distrib2 less_le_trans by fastforce
  finally show ?case by auto
next
  case (Comp_Signature M A t)
  have "sum_list (map w [M | A \<triangleright> t]) = w (M | A \<triangleright> t)" by simp
  also have "... < \<chi>' M * \<Theta> (Signature t intruder)" by (metis (full_types) \<Theta>.simps(5) le_add1 le_less_trans less_add_one mult_less_mono2 nat_0_less_mult_iff not_le w.simps w_pos zero_less_one)
  finally show ?case by auto
next
  case (Proj u v M M' A t)
  have "\<chi>'_pair": "\<chi>' [u, v] < \<chi>' [Pair u v]" unfolding \<chi>'_def by auto
  have "sum_list (map w [(u # v # M') | (msg.Pair u v # A) \<triangleright> t]) = w ((u # v # M') | (msg.Pair u v # A) \<triangleright> t)" by simp
  also have "... = \<chi>' (u # v # M') * \<Theta> t" by simp
  also have "... < \<chi>' (Pair u v # M') * \<Theta> t" using "\<chi>'_pair" "\<chi>'_pref"[of "[u, v]" "[Pair u v]" "M'"] unfolding "\<chi>'_def" by (metis Cons_eq_appendI One_nat_def \<Theta>_pos less_le_trans mult_less_mono1 self_append_conv2 zero_less_Suc)
  also have "... \<le> \<chi>' M * \<Theta> t" by (simp add: Proj.hyps \<chi>'_incl)
  finally show ?case by auto
next
  case (Sdec u k M M' A t)
  then have "sum_list (map w [(u # M') | (Sym_encrypt u k # A) \<triangleright> t, M' | (Sym_encrypt u k # A) \<triangleright> k]) = w ((u # M') | (Sym_encrypt u k # A) \<triangleright> t) + w (M' | (Sym_encrypt u k # A) \<triangleright> k)" by simp
  also have "... = \<chi>' M' * \<chi> u * \<Theta> t + \<chi>' M' * \<Theta> k" by (simp add: \<chi>'_def)
  also have "... < \<chi>' M' * \<chi> u * \<Theta> t + \<chi>' M' * (\<Theta> k + 1) * \<Theta> t" unfolding \<chi>'_def by (metis \<Theta>_pos \<chi>'_def add_strict_left_mono less_add_one less_le_trans mult.right_neutral mult_le_mono2 mult_less_mono2 nat_0_less_mult_iff w.simps w_pos)
  also have "... = \<chi>' M' * (\<chi> u + \<Theta> k + 1) * \<Theta> t" by (simp add: mult.commute semiring_normalization_rules(34))
  also have "... = \<chi>' M' * (\<chi> (Sym_encrypt u k)) * \<Theta> t" by simp
  also have "... \<le> \<chi>' M * \<Theta> t" by (metis Sdec.hyps \<chi>'_def \<chi>'_incl list.simps(9) mult.commute mult_le_mono2 prod_list.Cons)
  finally show ?case by auto
next
  case (Adec u M M' A t)
  then have "sum_list (map w [(u # M') | (Public_key_encrypt u intruder # A) \<triangleright> t]) = w ((u # M') | (Public_key_encrypt u intruder # A) \<triangleright> t)" by simp
  also have "... = \<chi>' M' * \<chi> u * \<Theta> t" by (simp add: \<chi>'_def)
  also have "... < \<chi>' M' * (\<chi> u + 1) * \<Theta> t" using \<Theta>_pos \<chi>'_pos less_le_trans by fastforce
  also have "... = \<chi>' M' * (\<chi> (Public_key_encrypt u intruder)) * \<Theta> t" by simp
  also have "... \<le> \<chi>' M * \<Theta> t" by (metis (full_types) Adec.hyps(1) Adec.hyps(2) \<chi>'_def \<chi>'_incl list.simps(9) mult.commute mult_le_mono2 prod_list.Cons)
  finally show ?case by auto
next
  case (Ksub u x M \<sigma> A t)
  then show ?case unfolding intruder_def by (metis fun_upd_same msg.distinct(1))
qed

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
  then have eq: "sum_list (map w (c # cs')) = w c + sum_list (map w cs')"
    by auto
  then show ?case
    using Context.hyps(1) Context.prems(1) \<eta>2_def eq rer1_measure_lt
    by (simp add: Context.prems cs_sapply_id)
qed

lemma "rer_any_term": "rer_any cs' cs \<Longrightarrow> (cs', cs) \<in> term_rel"
  unfolding term_rel_def
  by (metis in_measure mlex_leq mlex_less rer1_\<eta>1 rer1_\<eta>1' rer1_\<eta>2 rer_any.cases)

theorem "rer_any_wf": "wfP rer_any"
  by (metis rer_any_term term_rel_wf wfE_min wfP_eq_minimal)

end