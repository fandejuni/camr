theory Deduction imports
  Main Term
begin

(* 6. (a) *)

definition intruder :: msg where
  "intruder = Cons ''intruder''"

inductive deduce :: "msg set \<Rightarrow> msg \<Rightarrow> bool " ( infix "\<turnstile>" 72) where
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
lemma "{Pair u1 u2} \<turnstile> Hash (Pair u1 u2)"
  by auto
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
type_synonym constraint_sys = "constraint set"

fun c_fv :: "constraint \<Rightarrow> string set" where
  "c_fv (Constraint ms ms' msg) = \<Union>(m_fv ` (set ms \<union> set ms' \<union> {msg}))"

fun c_sapply :: "m_subst \<Rightarrow> constraint \<Rightarrow> constraint" where
  "c_sapply \<sigma> (Constraint ms ms' msg) = Constraint (map (m_sapply \<sigma>) ms) (map (m_sapply \<sigma>) ms') (m_sapply \<sigma> msg)"

fun c_derives :: "constraint \<Rightarrow> bool" where
  "c_derives (Constraint ms ms' msg) = (set ms \<union> set ms') \<turnstile> msg"

lemma "c_sapply_comp": "c_sapply \<tau> (c_sapply \<sigma> c) = c_sapply (\<tau> \<circ>m \<sigma>) c"
  using m_sapply_comp
  by (cases c) simp

definition cs_fv :: "constraint_sys \<Rightarrow> string set" where
  "cs_fv cs = \<Union>(c_fv ` cs)"

definition cs_sapply :: "m_subst \<Rightarrow> constraint_sys \<Rightarrow> constraint_sys" where
  "cs_sapply \<sigma> cs = c_sapply \<sigma> ` cs"

definition cs_derives :: "constraint_sys \<Rightarrow> bool" where
  "cs_derives cs = (\<forall>c \<in> cs. c_derives c)"

(* 7. (b) *)

type_synonym sol_set = "m_subst set"
definition sol :: "constraint_sys \<Rightarrow> sol_set" where
  "sol cs = {\<sigma> | \<sigma>. cs_derives (cs_sapply \<sigma> cs)}"

lemma "sol_cs_union": "sol (cs \<union> cs') = (sol cs) \<inter> (sol cs')"
  unfolding sol_def cs_sapply_def cs_derives_def
  by (rule set_eqI) auto

lemma "sol_subst_comp": "\<tau> \<in> sol (cs_sapply \<sigma> cs) \<Longrightarrow> \<tau> \<circ>m \<sigma> \<in> sol cs"
  unfolding sol_def cs_sapply_def cs_derives_def
  using c_sapply_comp by auto

(* 7. (c) *)

inductive rer1 :: "constraint \<Rightarrow> m_subst \<Rightarrow> constraint_sys \<Rightarrow> bool" ("_/\<leadsto>\<^sub>1[_]/_" [73,73,73]72) where
  Unif: "\<not>is_var t \<Longrightarrow> \<exists>u \<in> set M \<union> set A. \<sigma> = the (m_unify [(t, u)])  \<Longrightarrow> rer1 (M | A \<triangleright> t) \<sigma> {}"
| Comp_Hash: "rer1 (M | A \<triangleright> Hash t) Var {M | A \<triangleright> t}"
| Comp_Pair: "rer1 (M | A \<triangleright> Pair t1 t2) Var {M | A \<triangleright> t1, M | A \<triangleright> t2}"
| Comp_Sym_encrypt: "rer1 (M | A \<triangleright> Sym_encrypt m k) Var {M | A \<triangleright> m, M | A \<triangleright> k}"
| Comp_Public_key_encrypt: "rer1 (M | A \<triangleright> Public_key_encrypt m k) Var {M | A \<triangleright> m, M | A \<triangleright> k}"
| Comp_Signature: "rer1 (M | A \<triangleright> Signature t intruder) Var {M | A \<triangleright> t}"
| Proj: "rer1 ((Pair u v # M) | A \<triangleright> t) Var {(u # v # M) | (Pair u v # A) \<triangleright> t}"
| Sdec: "rer1 ((Sym_encrypt u k # M) | A \<triangleright> t) Var {(u # M) | (Sym_encrypt u k # A) \<triangleright> t, M | (Sym_encrypt u k # A) \<triangleright> k}"
| Adec: "rer1 ((Public_key_encrypt u intruder # M) | A \<triangleright> t) Var {(u # M) | (Public_key_encrypt u intruder # A) \<triangleright> t}"
| Ksub: "rer1 ((Public_key_encrypt u (Var x) # M) | A \<triangleright> t) (Var(x := intruder)) {c_sapply (Var(x := intruder)) ((Public_key_encrypt u (Var x) # M) | A \<triangleright> t)}"

inductive rer :: "constraint_sys \<Rightarrow> m_subst \<Rightarrow> constraint_sys \<Rightarrow> bool" ("_/\<leadsto>[_]/_" [73,73,73]72) where
  Context: "rer1 c \<sigma> cs \<Longrightarrow> rer ({c} \<union> cs') \<sigma> (cs \<union> cs_sapply \<sigma> cs')"

inductive rer_star :: "constraint_sys \<Rightarrow> m_subst \<Rightarrow> constraint_sys \<Rightarrow> bool" ("_/\<leadsto>*[_]/_" [73,73,73]72) where
  Refl: "rer_star cs \<sigma> cs"
| Trans: "rer cs \<sigma> cs' \<Longrightarrow> rer_star cs' \<sigma> cs'' \<Longrightarrow> rer_star cs \<sigma> cs''"

(* 7. (d) *)

inductive c_simple :: "constraint \<Rightarrow> bool" where
  "c_simple (M | A \<triangleright> (Var _))"

definition cs_simple :: "constraint_sys \<Rightarrow> bool" where
  "cs_simple cs = (\<forall>c \<in> cs. c_simple c)"

definition red :: "constraint_sys \<Rightarrow> m_subst set" where
  "red cs = {m_scomp \<tau> \<sigma> | \<tau> \<sigma>. \<exists>cs'. rer_star cs \<sigma> cs' \<and> cs_simple cs' \<and> \<tau> \<in> sol cs'}"

end