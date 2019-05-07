theory Deduction imports
  Main Term
begin

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
  by (metis Adec Ax Pair Sdec Sig insertI1 insert_commute)
(*  
  apply(rule Pair)
   apply(rule Sdec[of _ _ "k"], rule Ax, simp, rule Adec, rule Ax, simp)
  by(rule Sig, rule Sdec[of _ _ "k"], rule Ax, simp, rule Adec, rule Ax, simp)
*)

lemma deduce_weaken:
  assumes "G \<turnstile> t" and "G \<subseteq> H"
  shows "H \<turnstile> t"
  using assms
  by (induction rule: deduce.induct) auto+

lemma deduce_cut_aux:
  assumes "T \<turnstile> u" and "H \<turnstile> t" and "T = insert t H"
  shows "H \<turnstile> u"
  using assms
  by(induction rule: deduce.induct) auto+

lemma deduce_cut:
  assumes "insert t H \<turnstile> u" and "H \<turnstile> t"
  shows "H \<turnstile> u"
  using assms deduce_cut_aux by blast

end