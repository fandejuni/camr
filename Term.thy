theory Term imports
  Main Unify
begin

(*
Hints: Define separate constructors for variables and constants that take the
name of the variable or constant as argument. We suggest to use strings
(type string) as variables and constants and not to use subscripting for keys
in cryptographic operations.
*)

(* 5. (a) *)

datatype msg =
    Cons string
    | Var string
    | Hash msg
    | Pair msg msg
    | Sym_encrypt msg msg
    | Public_key_encrypt msg msg
    | Signature msg msg

inductive is_var :: "msg \<Rightarrow> bool" where
  "is_var (Var _)"

(* 5. (b) *)

datatype symbol =
  SCons string | SHash | SPair | SSym_encrypt | SPublic_key_encrypt | SSignature

fun arity :: "(symbol \<Rightarrow> nat)" where
  "arity (SCons _) = 0"
| "arity SHash = 1"
| "arity _ = 2"

(* 5. (c) *)

fun embed :: "msg \<Rightarrow> (symbol, string) term " where
  "embed (Cons s) = Fun (SCons s) []"
| "embed (Var s) = Unify.Var s"
| "embed (Hash m) = Fun SHash [embed m]"
| "embed (Pair m1 m2) = Fun SPair [embed m1, embed m2]"
| "embed (Sym_encrypt m1 m2) = Fun SSym_encrypt [embed m1, embed m2]"
| "embed (Public_key_encrypt m1 m2) = Fun SPublic_key_encrypt [embed m1, embed m2]"
| "embed (Signature m1 m2) = Fun SSignature [embed m1, embed m2]"

fun msg_of_term :: "(symbol, string) term \<Rightarrow> msg" where
  "msg_of_term (Unify.Var s) = Var s"
| "msg_of_term (Fun (SCons s) []) = Cons s"
| "msg_of_term (Fun SHash [t]) = Hash (msg_of_term t)"
| "msg_of_term (Fun SPair [t1, t2]) = Pair (msg_of_term t1) (msg_of_term t2)"
| "msg_of_term (Fun SSym_encrypt [t1, t2]) = Sym_encrypt (msg_of_term t1) (msg_of_term t2)"
| "msg_of_term (Fun SPublic_key_encrypt [t1, t2]) = Public_key_encrypt (msg_of_term t1) (msg_of_term t2)"
| "msg_of_term (Fun SSignature [t1, t2]) = Signature (msg_of_term t1) (msg_of_term t2)"
| "msg_of_term _ = undefined"

(* Three properties of embedding *)

lemma wf_term_embed [simp]: "wf_term arity (embed msg)"
proof (induction msg)
  case (Cons s)
  have "(length [] = arity (SCons s)) \<and> (\<forall>t\<in>(set []). wf_term arity t)" by simp
  then have "wf_term arity (Fun (SCons s) [])" by (simp add: wf_term.intros(2))
  then show ?case by simp
next
  case (Var x)
  then show ?case by (simp add: wf_term.intros(1))
next
  case (Hash m)
  have "length [embed m] = arity SHash" by simp
  then show ?case using Hash.IH wf_term.simps by fastforce
next
  case (Pair msg1 msg2)
  have "length [embed msg1, embed msg2] = arity SPair" by simp
  then show ?case
    by (metis Pair.IH(1) Pair.IH(2) embed.simps(4) list.discI list.set_cases set_ConsD wf_term.simps)
next
  case (Sym_encrypt msg1 msg2)
  have "length [embed msg1, embed msg2] = arity SSym_encrypt" by simp
  then show ?case
    by (metis Sym_encrypt.IH(1) Sym_encrypt.IH(2) embed.simps(5) list.discI list.set_cases set_ConsD wf_term.simps)
next
  case (Public_key_encrypt msg1 msg2)
  have "length [embed msg1, embed msg2] = arity SPublic_key_encrypt" by simp
  then show ?case
    by (metis Public_key_encrypt.IH(1) Public_key_encrypt.IH(2) embed.simps(6) list.discI list.set_cases set_ConsD wf_term.simps)
next
  case (Signature msg1 msg2)
  have "length [embed msg1, embed msg2] = arity SSignature" by simp
  then show ?case
    by (metis Signature.IH(1) Signature.IH(2) embed.simps(7) list.discI list.set_cases set_ConsD wf_term.simps)
qed

lemma msg_of_term_embed [simp]: "msg_of_term (embed msg) = msg"
  apply (induction msg)
  by simp_all

lemma embed_msg_of_term [simp]:
  "wf_term arity t \<Longrightarrow> embed (msg_of_term t) = t"
proof (induction t)
  case (Var x)
  then show ?case by simp
next
  case (Fun x1a x2)
  then show ?case
  proof (cases x1a)
    case (SCons x1)
    then show ?thesis
      by (metis Fun.prems arity.simps(1) embed.simps(1) length_0_conv msg_of_term.simps(2) term.distinct(1) term.inject(2) wf_term.simps)
  next
    case SHash
    then show ?thesis
      by (metis Fun.IH Fun.prems One_nat_def Suc_length_conv arity.simps(2) embed.simps(3) length_0_conv list.set_intros(1) msg_of_term.simps(3) term.distinct(1) term.inject(2) wf_term.simps)
  next
    case SPair
    have "length x2 = arity SPair" using Fun.prems SPair wf_term.cases by fastforce
    then have "length x2 = 2" by simp
    then obtain x2a x2b where "x2 = [x2a, x2b]"
      by (metis (no_types, lifting) One_nat_def Suc_1 Suc_length_conv length_0_conv)
    then show ?thesis
      by (metis Fun.IH Fun.prems SPair embed.simps(4) insert_iff list.set(2) msg_of_term.simps(4) term.distinct(1) term.inject(2) wf_term.cases)
  next
    case SSym_encrypt
    have "length x2 = arity SSym_encrypt" using Fun.prems SSym_encrypt wf_term.cases by fastforce
    then have "length x2 = 2" by simp
    then obtain x2a x2b where "x2 = [x2a, x2b]"
      by (metis (no_types, lifting) One_nat_def Suc_1 Suc_length_conv length_0_conv)
    then show ?thesis
      by (metis Fun.IH Fun.prems SSym_encrypt embed.simps(5) insert_iff list.set(2) msg_of_term.simps(5) term.distinct(1) term.inject(2) wf_term.cases)
  next
    case SPublic_key_encrypt
    have "length x2 = arity SPublic_key_encrypt" using Fun.prems SPublic_key_encrypt wf_term.cases by fastforce
    then have "length x2 = 2" by simp
    then obtain x2a x2b where "x2 = [x2a, x2b]"
      by (metis (no_types, lifting) One_nat_def Suc_1 Suc_length_conv length_0_conv)
    then show ?thesis
      by (metis Fun.IH Fun.prems SPublic_key_encrypt embed.simps(6) insert_iff list.set(2) msg_of_term.simps(6) term.distinct(1) term.inject(2) wf_term.cases)
  next
    case SSignature
    have "length x2 = arity SSignature" using Fun.prems SSignature wf_term.cases by fastforce
    then have "length x2 = 2" by simp
    then obtain x2a x2b where "x2 = [x2a, x2b]"
      by (metis (no_types, lifting) One_nat_def Suc_1 Suc_length_conv length_0_conv)
    then show ?thesis
      by (metis Fun.IH Fun.prems SSignature embed.simps(7) insert_iff list.set(2) msg_of_term.simps(7) term.distinct(1) term.inject(2) wf_term.cases)
  qed
qed

(* Some properties *)

lemma wf_subst_embed [simp]:
  "wf_subst arity (embed \<circ> \<sigma>)"
  by (simp add: wf_subst_def)

lemma msg_of_term_inject:
  "\<lbrakk> wf_term arity t1; wf_term arity t2 \<rbrakk> \<Longrightarrow> msg_of_term t1 = msg_of_term t2 \<longleftrightarrow> t1 = t2 "
  using embed_msg_of_term by fastforce

(* 5. (d) *)

fun m_fv :: "msg \<Rightarrow> string set" where
  "m_fv (Cons s) = {}"
| "m_fv (Var s) = {s}"
| "m_fv (Hash m) = m_fv m"
| "m_fv (Pair m1 m2) = m_fv m1 \<union> m_fv m2"
| "m_fv (Sym_encrypt m1 m2) = m_fv m1 \<union> m_fv m2"
| "m_fv (Public_key_encrypt m1 m2) = m_fv m1 \<union> m_fv m2"
| "m_fv (Signature m1 m2) = m_fv m1 \<union> m_fv m2"

lemma link_fv:
  "m_fv msg = fv (embed msg)"
  apply (induction msg)
  by simp_all

lemma "m_fv_finite": "finite (m_fv msg)"
  by (induction msg) auto

type_synonym m_subst = "char list \<Rightarrow> msg"
type_synonym m_eq = "msg \<times> msg"
type_synonym m_eqs = "m_eq list"

fun embed_eq :: "m_eq \<Rightarrow> (symbol, string) equation " where
  "embed_eq (m1, m2) = (embed m1, embed m2)"

fun m_eq_of_eq :: "(symbol, string) equation \<Rightarrow> m_eq" where
  "m_eq_of_eq (a, b) = (msg_of_term a, msg_of_term b)"

fun embed_eqs :: "m_eqs \<Rightarrow> (symbol, string) equations" where
  "embed_eqs [] = []"
| "embed_eqs (eq # U) = (embed_eq eq) # (embed_eqs U)"

fun m_eqs_of_eqs :: "(symbol, string) equations \<Rightarrow> m_eqs" where
  "m_eqs_of_eqs [] = []"
| "m_eqs_of_eqs (eq # U) = (m_eq_of_eq eq) # (m_eqs_of_eqs U)"

fun m_sapply :: "m_subst \<Rightarrow> msg \<Rightarrow> msg"
  where
  "m_sapply \<sigma> (Cons s) = Cons s"
| "m_sapply \<sigma> (Var s) =  \<sigma> s"
| "m_sapply \<sigma> (Hash m) = Hash (m_sapply \<sigma> m)"
| "m_sapply \<sigma> (Pair m1 m2) = Pair (m_sapply \<sigma> m1) (m_sapply \<sigma> m2)"
| "m_sapply \<sigma> (Sym_encrypt m1 m2) = Sym_encrypt (m_sapply \<sigma> m1) (m_sapply \<sigma> m2)"
| "m_sapply \<sigma> (Public_key_encrypt m1 m2) = Public_key_encrypt (m_sapply \<sigma> m1) (m_sapply \<sigma> m2)"
| "m_sapply \<sigma> (Signature m1 m2) = Signature (m_sapply \<sigma> m1) (m_sapply \<sigma> m2)"

lemma link_sapply:
  "m_sapply \<sigma> m = msg_of_term (sapply (embed \<circ> \<sigma>) (embed m))"
  apply (induction m)
  by simp_all

lemma "m_sapply_id": "m_sapply Var = id"
proof (rule ext)
  fix msg
  show "m_sapply msg.Var msg = id msg" by (induction msg) auto
qed

fun m_sapply_eq :: "m_subst \<Rightarrow> m_eq \<Rightarrow> m_eq" where
  "m_sapply_eq \<sigma> eq = (m_sapply \<sigma> (fst eq), m_sapply \<sigma> (snd eq))"

lemma link_sapply_eq:
  "m_sapply_eq \<sigma> eq = m_eq_of_eq (sapply_eq (embed \<circ> \<sigma>) (embed_eq eq))"
  by (metis embed_eq.simps fstI link_sapply m_eq_of_eq.simps m_sapply_eq.elims prod.collapse sapply_eq.elims sndI)

fun m_sapply_eqs :: "m_subst \<Rightarrow> m_eqs \<Rightarrow> m_eqs" where
  "m_sapply_eqs \<sigma> [] = []"
| "m_sapply_eqs \<sigma> (eq # U) = (m_sapply_eq \<sigma> eq) # (m_sapply_eqs \<sigma> U)"

lemma link_sapply_eqs:
  "m_sapply_eqs \<sigma> U = m_eqs_of_eqs (sapply_eq_system (embed \<circ> \<sigma>) (embed_eqs U))"
  proof (induction U)
    case Nil
    then show ?case by simp
  next
    case (Cons a U)
    have "m_sapply_eqs \<sigma> (a # U) = (m_sapply_eq \<sigma> a) # (m_sapply_eqs \<sigma> U)" by simp
    moreover have "m_sapply_eq \<sigma> a = m_eq_of_eq (sapply_eq (embed \<circ> \<sigma>) (embed_eq a))"
      using link_sapply_eq by blast
    moreover have "m_sapply_eqs \<sigma> U = m_eqs_of_eqs (sapply_eq_system (embed \<circ> \<sigma>) (embed_eqs U))"
      using Cons.IH by blast
    then show ?case
      by (metis Cons.IH embed_eqs.simps(2) link_sapply_eq m_eqs_of_eqs.simps(2) m_sapply_eqs.simps(2) sapply_eq_system_equiv_def)
  qed

inductive m_unifies :: "m_subst \<Rightarrow> m_eq \<Rightarrow> bool" where
  m_unifies_eq: "(m_sapply \<sigma> u = m_sapply \<sigma> t) \<Longrightarrow> m_unifies \<sigma> (u, t)"

(* TODO *)
lemma link_unifies:
  "m_unifies \<sigma> eq = unifies (embed \<circ> \<sigma>) (embed_eq eq)"
  apply (auto simp add: embed_eq.elims fstI link_sapply m_unifies.simps sndI unifies.simps)
   apply (metis embed_msg_of_term wf_subst_embed wf_term_embed wf_term_sapply)
  by (metis embed_eq.elims old.prod.inject)

inductive m_unifiess :: "m_subst \<Rightarrow> m_eqs \<Rightarrow> bool" where
  m_unifiess_empty: "m_unifiess \<sigma> []"
| m_unifiess_rec:   "(m_unifiess \<sigma> s) \<and> (m_unifies \<sigma> eq) \<Longrightarrow> m_unifiess \<sigma> (eq # s)"

lemma link_unifiess:
  "m_unifiess \<sigma> U = unifiess (embed \<circ> \<sigma>) (embed_eqs U)"
proof (induction U)
  case Nil
  then show ?case by (simp add: m_unifiess_empty unifiess_empty)
next
  case (Cons a U)
  then show ?case
    by (metis (mono_tags, lifting) embed_eqs.simps(2) link_unifies list.discI list.inject m_unifiess.simps unifiess.simps)
qed

fun lift_subst :: "(symbol, string) subst option \<Rightarrow> m_subst option" where
  "lift_subst None = None"
| "lift_subst (Some \<sigma>) = Some (msg_of_term \<circ> \<sigma>)"

fun m_unify :: "m_eqs \<Rightarrow> m_subst option" where
  "m_unify U = lift_subst (unify (embed_eqs U))"

lemma msg_of_term_var[simp]:
  "msg_of_term \<circ> Unify.Var = msg.Var"
proof (rule ext)
  fix x
  show "(msg_of_term \<circ> term.Var) x = msg.Var x"
  proof (cases x)
    case Nil
    then show ?thesis by simp
  next
    case (Cons a list)
    then show ?thesis by simp
  qed
qed

lemma link_unify_1:
  "m_unify [] = Some Var"
proof -
  have "m_unify [] = lift_subst (unify [])" by simp
  then have "... = lift_subst (Some Unify.Var)" by simp
  then have "... = Some (msg_of_term \<circ> Unify.Var)" by simp
  then show ?thesis by simp
qed

fun m_scomp :: "m_subst \<Rightarrow> m_subst \<Rightarrow> m_subst" (infixl "\<circ>m" 75)
  where
  "m_scomp \<sigma> \<tau> = (\<lambda> x. m_sapply \<sigma> (\<tau>(x)))"

fun m_lifted_comp :: "m_subst option \<Rightarrow> m_subst \<Rightarrow> m_subst option"
  where
  "m_lifted_comp None \<tau> = None"
| "m_lifted_comp (Some \<sigma>) \<tau> = Some (\<sigma> \<circ>m \<tau>)"

(* 5. (e) *)

lemma "m_sapply_comp": "m_sapply \<tau> (m_sapply \<sigma> m) = m_sapply (\<tau> \<circ>m \<sigma>) m"
  by (induction m) auto

lemma embed_eq[simp]:
  "fst (embed_eq eq) = embed (fst eq)"
  "snd (embed_eq eq) = embed (snd eq)"
proof -
  show "fst (embed_eq eq) = embed (fst eq)"
    by (metis embed_eq.simps fstI prod.collapse)
  show "snd (embed_eq eq) = embed (snd eq)"
    by (metis embed_eq.simps prod.collapse sndI)
qed

lemma wf_subst_id:
  assumes "wf_subst arity \<tau>"
  shows "sapply (embed \<circ> msg_of_term \<circ> \<tau>) (embed m) = sapply \<tau> (embed m)"
  by (metis (mono_tags) assms comp_apply embed_msg_of_term wf_subst_def)

lemma link_soundness:
  assumes "unifiess \<tau> (embed_eqs U)"
  and "msg_of_term \<circ> \<tau> = \<sigma>"
  and "wf_subst arity \<tau>"
  shows "m_unifiess \<sigma> U"
  using assms
proof (induction U)
  case Nil
  then show ?case by (simp add: m_unifiess_empty)
next
  case (Cons a U)
  have "unifies \<tau> (embed_eq a)"
    by (metis Cons.prems(1) embed_eqs.simps(2) list.discI list.inject unifiess.cases)
  moreover obtain "wf_term arity (embed (fst a))" and "wf_term arity (embed (snd a))"
    by (metis wf_term_embed)
  then obtain "wf_term arity (sapply \<tau> (embed (fst a)))" and "wf_term arity (sapply \<tau> (embed (snd a)))"
    using assms(3) wf_term_sapply by blast
  moreover have "sapply \<tau> (fst (embed_eq a)) = sapply \<tau> (snd (embed_eq a))"
    using unifies.simps calculation(1) by (metis fst_conv sndI)
  then have "sapply \<tau> (embed (fst a)) = sapply \<tau> (embed (snd a))" by simp

  have "unifies (embed \<circ> \<sigma>) (embed_eq a)"
  proof -
    have "sapply (embed \<circ> \<sigma>) (embed (fst a)) = sapply (embed \<circ> msg_of_term \<circ> \<tau>) (embed (fst a))"
      by (simp add: assms(2) comp_assoc)
    then have "... = sapply \<tau> (embed (fst a))"
      using assms(3) wf_subst_id by blast
    then have "... = sapply \<tau> (embed (snd a))" 
      by (simp add: \<open>\<tau> \<cdot> Term.embed (fst a) = \<tau> \<cdot> Term.embed (snd a)\<close>)
    then have "... = sapply (embed \<circ> \<sigma>) (embed (snd a))"
      by (metis assms(2) assms(3) comp_assoc wf_subst_id)
    then show ?thesis
      by (metis \<open>(Term.embed \<circ> \<sigma>) \<cdot> Term.embed (fst a) = (Term.embed \<circ> msg_of_term \<circ> \<tau>) \<cdot> Term.embed (fst a)\<close> \<open>(Term.embed \<circ> msg_of_term \<circ> \<tau>) \<cdot> Term.embed (fst a) = \<tau> \<cdot> Term.embed (fst a)\<close> \<open>\<tau> \<cdot> Term.embed (fst a) = \<tau> \<cdot> Term.embed (snd a)\<close> embed_eq(1) embed_eq(2) prod.collapse unifies_eq)
  qed
  then show ?case
    by (metis Cons.IH Cons.prems(1) assms(2) assms(3) embed_eqs.simps(2) link_unifiess list.inject unifiess.simps)
qed

theorem m_soundness1:
  assumes "m_unify U = Some \<sigma>"
  shows "m_unifiess \<sigma> U"
proof -
  obtain \<tau> where "unify (embed_eqs U) = Some \<tau>"
    using assms by fastforce
  then have "unifiess \<tau> (embed_eqs U)" by (simp add: soundness1)
  moreover have "\<sigma> = msg_of_term \<circ> \<tau>"
    using \<open>unify (embed_eqs U) = Some \<tau>\<close> assms by auto
  moreover have "wf_eqs arity (embed_eqs U)"
  proof (induction U)
    case Nil
    then show ?case
      by (simp add: wf_eqs.intros(1))
  next
    case (Cons a U)
    obtain "wf_term arity (embed (fst a))" and "wf_term arity (embed (snd a))" by simp
    then show ?case
      by (metis Cons.IH embed_eq(1) embed_eq(2) embed_eqs.simps(2) wf_eq_def wf_eqs.simps wf_term_embed)
  qed
  then have "wf_subst arity \<tau>"
    using \<open>unify (embed_eqs U) = Some \<tau>\<close> wf_subst_unify by blast
  then show ?thesis
    using calculation(1) calculation(2) link_soundness by auto
qed

(* 5. (f) *)

fun m_fv_eq :: "m_eq \<Rightarrow> string set" where
  "m_fv_eq eq = (m_fv (fst eq)) \<union> (m_fv (snd eq))"

lemma link_fv_eq:
  "m_fv_eq eq = fv_eq (embed_eq eq)"
proof -
  have "m_fv_eq eq = (m_fv (fst eq)) \<union> (m_fv (snd eq))" by simp
  then have "... = (fv (fst (embed_eq eq))) \<union> (fv (snd (embed_eq eq)))"
    by (metis embed_eq.simps fstI link_fv prod.collapse sndI)
  then show ?thesis by simp
qed

fun m_fv_eqs :: "m_eqs \<Rightarrow> string set" where
  "m_fv_eqs [] = {}"
| "m_fv_eqs (eq # U) = (m_fv_eq eq) \<union> (m_fv_eqs U)"

lemma def_equiv:
  "m_fv_eqs U = (\<Union>x\<in>(set U). m_fv_eq x)"
proof (induction U)
  case Nil
  then show ?case by auto
next
  case (Cons a U)
  then show ?case by simp
qed

lemma link_fv_eqs:
  "m_fv_eqs U = fv_eq_system (embed_eqs U)"
proof (induction U)
  case Nil
  have "m_fv_eqs [] = (\<Union>x\<in>(set []). m_fv_eq x)" by simp
  then have "... = {}" by auto
  moreover have "embed_eqs [] = []" by simp
  moreover have "fv_eq_system [] = fold (\<union>) (map fv_eq []) {}" by simp
  then have "fold (\<union>) (map fv_eq []) {} = fold (\<union>) [] {}" by simp
  then have "fold (\<union>) [] {} = {}" by simp
  then show ?case
    by simp
next
  case (Cons a U)
  then show ?case
    by (metis embed_eqs.simps(2) fv_eq_system_def_equiv link_fv_eq list.discI list.inject m_fv_eqs.elims)
qed

fun m_sdom :: "m_subst \<Rightarrow> string set"
  where
  "m_sdom \<sigma> = {x. \<sigma> x \<noteq> Var x}"

lemma link_sdom:
  "m_sdom \<sigma> = sdom (embed \<circ> \<sigma>)"
proof -
  have "m_sdom \<sigma> = {x. \<sigma> x \<noteq> msg.Var x}" by auto
  then have "... = {x. (embed \<circ> \<sigma>) x \<noteq> (embed \<circ> msg.Var) x}"
    by (metis comp_apply msg_of_term_embed)
  then show ?thesis by auto
qed

fun m_sran :: "m_subst \<Rightarrow> msg set"
  where
"m_sran \<sigma> = (\<Union>x\<in>m_sdom \<sigma>. {\<sigma> x})"

fun msg_set_of_term_set :: "(symbol, string) term set \<Rightarrow> msg set" where
  "msg_set_of_term_set s = {msg_of_term x | x. x \<in> s}"

lemma msg_set_def:
  "msg_set_of_term_set s = (\<Union>x\<in>s. {msg_of_term x})" by auto

lemma msg_set_def_specific:
  "(\<Union>x\<in>(sdom \<tau>). {msg_of_term (\<tau> x)}) = msg_set_of_term_set (\<Union>x\<in>(sdom \<tau>). {\<tau> x})" by auto

lemma link_sran:
  "m_sran \<sigma> = msg_set_of_term_set (sran (embed \<circ> \<sigma>))"
proof -
  have "m_sran \<sigma> = (\<Union>x\<in>m_sdom \<sigma>. {\<sigma> x})" by simp
  then have "... = (\<Union>x\<in>(sdom (embed \<circ> \<sigma>)). {\<sigma> x})"
    using link_sdom by auto
  then have "... = (\<Union>x\<in>(sdom (embed \<circ> \<sigma>)). {(msg_of_term \<circ> embed \<circ> \<sigma>) x})" by auto
  then have "... = (\<Union>x\<in>(sdom (embed \<circ> \<sigma>)). {msg_of_term ((embed \<circ> \<sigma>) x)})" by simp
  then have "... = msg_set_of_term_set (\<Union>x\<in>(sdom (embed \<circ> \<sigma>)). {(embed \<circ> \<sigma>) x})"
    using msg_set_def_specific by presburger
  then show ?thesis
    using \<open>(\<Union>x\<in>m_sdom \<sigma>. {\<sigma> x}) = (\<Union>x\<in>sdom (Term.embed \<circ> \<sigma>). {\<sigma> x})\<close> by auto
qed

fun m_svran:: "m_subst \<Rightarrow> string set"
  where
"m_svran \<sigma> = (\<Union>t\<in>(m_sran \<sigma>).(m_fv t))"

lemma wf_term_embed_sran:
  assumes "y \<in> sran (embed \<circ> \<sigma>)"
  shows "wf_term arity y"
proof -
  have "y \<in> (\<Union>x\<in>sdom (embed \<circ> \<sigma>). {(embed \<circ> \<sigma>) x})" using assms by auto
  obtain x where "y \<in> {(embed \<circ> \<sigma>) x}" and "x \<in> sdom (embed \<circ> \<sigma>)"
    using \<open>y \<in> (\<Union>x\<in>sdom (Term.embed \<circ> \<sigma>). {(Term.embed \<circ> \<sigma>) x})\<close> by blast
  then have "y = (embed \<circ> \<sigma>) x" by blast
  moreover have "wf_subst arity (embed \<circ> \<sigma>)" by simp
  then show ?thesis by (simp add: calculation)
qed

lemma link_svran:
  "m_svran \<sigma> = svran (embed \<circ> \<sigma>)"
proof -
  have "m_svran \<sigma> = (\<Union>t\<in>(m_sran \<sigma>).(m_fv t))" by simp
  then have "... = (\<Union>t\<in>(msg_set_of_term_set (sran (embed \<circ> \<sigma>))).(m_fv t))"
    using link_sran by auto
  then have "... =  (\<Union>x\<in>(sran (embed \<circ> \<sigma>)).(m_fv (msg_of_term x)))" by fastforce
  then have "... =  (\<Union>x\<in>(sran (embed \<circ> \<sigma>)).(fv ((embed \<circ> msg_of_term) x)))"
    using link_fv by auto
  moreover have "\<forall>x\<in>(sran (embed \<circ> \<sigma>)). wf_term arity x"
    using wf_term_embed_sran by blast
  then show ?thesis
    using \<open>(\<Union>t\<in>m_sran \<sigma>. m_fv t) = (\<Union>t\<in>msg_set_of_term_set (sran (Term.embed \<circ> \<sigma>)). m_fv t)\<close> \<open>(\<Union>t\<in>msg_set_of_term_set (sran (Term.embed \<circ> \<sigma>)). m_fv t) = (\<Union>x\<in>sran (Term.embed \<circ> \<sigma>). m_fv (msg_of_term x))\<close> calculation by auto
qed

lemma wf_embed_eqs:
  "wf_eqs arity (embed_eqs U)"
proof (induction U)
  case Nil
  then show ?case by (simp add: wf_eqs.intros(1))
next
  case (Cons a U)
  obtain "wf_term arity (embed (fst a))" and "wf_term arity (embed (snd a))" by simp
  then have "wf_eq arity (embed_eq a)" by (simp add: wf_eq_def)
  then show ?case by (simp add: Cons.IH wf_eqs.intros(2))
qed

lemma msg_term_tau:
  assumes "unify (embed_eqs U) = Some \<tau>"
  and "\<sigma> = msg_of_term \<circ> \<tau>"
  shows "embed \<circ> msg_of_term \<circ> \<tau> = \<tau>"
proof (rule ext)
  show "(embed \<circ> msg_of_term \<circ> \<tau>) t = \<tau> t" for t
  proof -
    have "wf_eqs arity (embed_eqs U)" by (simp add: wf_embed_eqs)
    have "wf_subst arity \<tau>" using \<open>wf_eqs arity (embed_eqs U)\<close> assms(1) wf_subst_unify by auto
    then have "wf_term arity (\<tau> t)" by (simp add: wf_subst_def)
    then show ?thesis by simp
  qed
qed

lemma embed_sapply:
  "embed (m_sapply \<sigma> u) = (embed \<circ> \<sigma>) \<cdot> (embed u)"
  by (simp add: link_sapply)

lemma m_sapply_embed:
  "embed_eqs (m_sapply_eqs \<sigma> U) = (embed \<circ> \<sigma>) \<cdot> (embed_eqs U)"
proof (induction U)
  case Nil
  then show ?case by simp
next
  case (Cons a U)
  have "embed_eq (m_sapply_eq \<sigma> a) = (embed \<circ> \<sigma>) \<cdot> (embed_eq a)"
  proof -
    obtain u and v where "a = (u, v)" by (meson surj_pair)
    have "embed_eq (m_sapply_eq \<sigma> a) = (embed (m_sapply \<sigma> u), embed (m_sapply \<sigma> v))"
      by (simp add: \<open>a = (u, v)\<close>)
    then have "... = ((embed \<circ> \<sigma>) \<cdot> (embed u), (embed \<circ> \<sigma>) \<cdot> (embed v))" using embed_sapply by blast
    then have "... = (embed \<circ> \<sigma>) \<cdot> (embed u, embed v)" by simp
    then show ?thesis
      using \<open>(Term.embed (m_sapply \<sigma> u), Term.embed (m_sapply \<sigma> v)) = ((Term.embed \<circ> \<sigma>) \<cdot> Term.embed u, (Term.embed \<circ> \<sigma>) \<cdot> Term.embed v)\<close> \<open>a = (u, v)\<close> \<open>embed_eq (m_sapply_eq \<sigma> a) = (Term.embed (m_sapply \<sigma> u), Term.embed (m_sapply \<sigma> v))\<close> embed_eq.simps by presburger
  qed
  then show ?case
    by (metis (no_types, lifting) Cons.IH embed_eqs.elims list.discI list.inject m_sapply_eqs.simps(2) sapply_eq_system_equiv_def)
qed

lemma m_fv_sapply_sdom_svran:
  assumes "x \<in> m_fv (m_sapply \<sigma> m)"
  shows "x \<in> (m_fv m - m_sdom \<sigma>) \<union> m_svran \<sigma>"
  using assms
  by (metis embed_sapply fv_sapply_sdom_svran link_fv link_sdom link_svran)

lemma m_lemma_3:
  assumes "m_unify U = Some \<sigma>"
  shows "m_fv_eqs (m_sapply_eqs \<sigma> U) \<subseteq> m_fv_eqs U"
    and "m_sdom \<sigma> \<subseteq> m_fv_eqs U"
    and "m_svran \<sigma> \<subseteq> m_fv_eqs U"
    and "m_sdom \<sigma> \<inter> m_svran \<sigma> = {}"
proof -
  obtain \<tau> where "unify (embed_eqs U) = Some \<tau>" using assms by fastforce
  moreover have "\<sigma> = msg_of_term \<circ> \<tau>" using \<open>unify (embed_eqs U) = Some \<tau>\<close> assms by auto
  moreover show "m_sdom \<sigma> \<subseteq> m_fv_eqs U"
  proof -
    have "m_sdom \<sigma> = sdom (embed \<circ> msg_of_term \<circ> \<tau>)" using link_sdom
      by (simp add: \<open>\<sigma> = msg_of_term \<circ> \<tau>\<close>)
    then have "... = sdom \<tau>" using calculation msg_term_tau by auto
    then have "... \<subseteq> fv_eq_system (embed_eqs U)" using calculation lemma_3_i_iii by blast
    then show ?thesis using \<open>m_sdom \<sigma> = sdom (Term.embed \<circ> msg_of_term \<circ> \<tau>)\<close> link_fv_eqs by auto
  qed
  moreover show "m_svran \<sigma> \<subseteq> m_fv_eqs U"
  proof -
    have "m_svran \<sigma> = svran (embed \<circ> msg_of_term \<circ> \<tau>)"
      using calculation(2) link_svran by auto
    then have "... = svran \<tau>" using calculation(1) msg_term_tau by auto
    then have "... \<subseteq> fv_eq_system (embed_eqs U)" using calculation lemma_3_i_iii by blast
    then show ?thesis
      using \<open>m_svran \<sigma> = svran (Term.embed \<circ> msg_of_term \<circ> \<tau>)\<close> \<open>svran (Term.embed \<circ> msg_of_term \<circ> \<tau>) = svran \<tau>\<close> link_fv_eqs by blast
  qed
  moreover show "m_fv_eqs (m_sapply_eqs \<sigma> U) \<subseteq> m_fv_eqs U"
  proof -
    have "m_fv_eqs (m_sapply_eqs \<sigma> U) = fv_eq_system (embed_eqs (m_sapply_eqs \<sigma> U))"
      by (simp add: link_fv_eqs)
    moreover have "embed_eqs (m_sapply_eqs \<sigma> U) = (embed \<circ> \<sigma>) \<cdot> (embed_eqs U)"
      by (simp add: m_sapply_embed)
    moreover have "fv_eq_system ((embed \<circ> \<sigma>) \<cdot> (embed_eqs U)) \<subseteq> fv_eq_system (embed_eqs U)"
      by (metis \<open>\<sigma> = msg_of_term \<circ> \<tau>\<close> \<open>unify (embed_eqs U) = Some \<tau>\<close> comp_assoc lemma_3_i_iii msg_term_tau) 
    then show ?thesis by (simp add: calculation(2) link_fv_eqs)
  qed
  moreover show "m_sdom \<sigma> \<inter> m_svran \<sigma> = {}"
  proof -
    have "m_sdom \<sigma> \<inter> m_svran \<sigma> =  sdom (embed \<circ> msg_of_term \<circ> \<tau>) \<inter> svran (embed \<circ> msg_of_term \<circ> \<tau>)"
      using calculation(2) link_sdom link_svran by auto
    then have "... = sdom \<tau> \<inter> svran \<tau>" using calculation(1) msg_term_tau by auto
    moreover have "sdom \<tau> \<inter> svran \<tau> = {}"
      by (metis \<open>unify (embed_eqs U) = Some \<tau>\<close> lemma_3_iv) 
    then show ?thesis
      using \<open>m_sdom \<sigma> \<inter> m_svran \<sigma> = sdom (Term.embed \<circ> msg_of_term \<circ> \<tau>) \<inter> svran (Term.embed \<circ> msg_of_term \<circ> \<tau>)\<close> calculation by blast
  qed
qed

end