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
        apply simp+
  done

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
        apply simp_all
  done

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
        apply simp_all
  done

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
  apply (induction U)
  apply (simp add: m_unifiess_empty unifiess_empty)
  by (metis (mono_tags, lifting) embed_eqs.simps(2) link_unifies list.discI list.inject m_unifiess.simps unifiess.simps)

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

(*
lemma link_unify_2:
  "m_unify ((Var x, t) # U) = (
  if (x \<notin> m_fv t) then
    m_lifted_comp (m_unify (m_sapply_eqs (msg.Var(x := t)) U)) (msg.Var(x := t))
   else (
     if Var x = t then m_unify U else None
    )
  )"
  sorry
*)

(*
function (sequential) m_unify :: "m_eqs \<Rightarrow> m_subst option"
  where
  "unify [] = Some Var"
| "unify ((Var x, t) # U) = (
| "unify ((u, Var y) # U) = unify ((Var y, u) # U)"
| "unify ((Fun f u, Fun g v) # U) =
  (if (f = g \<and> length u = length v) then
    unify(append (zip u v) U)
  else
    None)"
*)

(*
fun m_unify :: "m_eqs \<Rightarrow> m_subst option" where
  "m_unify U = lift_subst (unify (embed_eqs U))"
*)

(* 5. (e) *)

theorem m_soundness1:
  assumes "m_unify U = Some \<sigma>"
  shows "m_unifiess \<sigma> U"
  using assms
proof (induction U)
  case Nil
  then show ?case
    by (simp add: m_unifiess_empty)
next
  case (Cons a U)
  obtain \<tau> where "unify (embed_eqs (a # U)) = Some \<tau>"
    using Cons.prems by fastforce
  then have "unifiess \<tau> (embed_eqs (a # U))" 
    by (simp add: soundness1)
  then have "unifiess \<tau> (embed_eqs U)"
    by (metis embed_eqs.elims list.discI list.inject local.Cons unifiess.simps)
  moreover have "\<sigma> = msg_of_term \<circ> \<tau>"
    using Cons.prems \<open>unify (embed_eqs (a # U)) = Some \<tau>\<close> by auto
  then show ?case sorry
qed

(*
lemma link_unifies:
  "m_unifies \<sigma> eq = unifies (embed \<circ> \<sigma>) (embed_eq eq)"

lemma link_unifiess:
  "m_unifiess \<sigma> U = unifiess (embed \<circ> \<sigma>) (embed_eqs U)"
*)

(*
  m_unifies_eq: "(m_sapply \<sigma> u = m_sapply \<sigma> t) \<Longrightarrow> m_unifies \<sigma> (u, t)"
*)

(*
| m_unifiess_rec:   "(m_unifiess \<sigma> s) \<and> (m_unifies \<sigma> eq) \<Longrightarrow> m_unifiess \<sigma> (eq # s)"
*)

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
    by (metis Collect_cong comp_apply msg_of_term_embed)
  then show ?thesis by auto
qed

fun m_sran :: "m_subst \<Rightarrow> msg set"
  where
"m_sran \<sigma> = (\<Union>x\<in>m_sdom \<sigma>. {\<sigma> x})"

fun msg_set_of_term_set :: "(symbol, string) term set \<Rightarrow> msg set" where
  "msg_set_of_term_set s = {msg_of_term x | x. x \<in> s}"

lemma link_sran:
  "m_sran \<sigma> = msg_set_of_term_set (sran (embed \<circ> \<sigma>))"
proof -
  have "m_sran \<sigma> = (\<Union>x\<in>m_sdom \<sigma>. {\<sigma> x})" by simp
  then have "... = (\<Union>x\<in>(sdom (embed \<circ> \<sigma>)). {\<sigma> x})"
    using link_sdom by auto
  then show ?thesis sorry
qed

fun m_svran:: "m_subst \<Rightarrow> string set"
  where
"m_svran \<sigma> = (\<Union>t\<in>(m_sran \<sigma>).(m_fv t))"

lemma link_svran:
  "m_svran \<sigma> = svran (embed \<circ> \<sigma>)"
  sorry

lemma m_lemma_3:
  assumes "m_unify U = Some \<sigma>"
  shows "m_fv_eqs (m_sapply_eqs \<sigma> U) \<subseteq> m_fv_eqs U"
    and "m_sdom \<sigma> \<subseteq> m_fv_eqs U"
    and "m_svran \<sigma> \<subseteq> m_fv_eqs U"
    and "m_sdom \<sigma> \<inter> m_svran \<sigma> = {}"
  sorry

end