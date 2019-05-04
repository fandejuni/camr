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
  then show ?case sledgehammer
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


datatype msg =
  "m_fv (
(*
    Cons string
    | Var string
    | Hash msg
    | Pair msg msg
    | Sym_encrypt msg msg
    | Public_key_encrypt msg msg
    | Signature msg msg
*)

end