structure Search : sig
  type char
  type msg
  type constraint
  val ktp : constraint list
  val nspk : constraint list
  val ktp_vars : (char list) list
  val nspk_vars : (char list) list
  val print_search : (char list) list -> constraint list -> string
  val print_search_slow : (char list) list -> constraint list -> string
end = struct

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

fun eq A_ a b = equal A_ a b;

fun equal_lista A_ [] (x21 :: x22) = false
  | equal_lista A_ (x21 :: x22) [] = false
  | equal_lista A_ (x21 :: x22) (y21 :: y22) =
    eq A_ x21 y21 andalso equal_lista A_ x22 y22
  | equal_lista A_ [] [] = true;

datatype char = Chara of bool * bool * bool * bool * bool * bool * bool * bool;

datatype msg = Cons of char list | Var of char list | Hash of msg |
  Pair of msg * msg | Sym_encrypt of msg * msg | Public_key_encrypt of msg * msg
  | Signature of msg * msg;

fun equal_bool p true = p
  | equal_bool p false = not p
  | equal_bool true p = p
  | equal_bool false p = not p;

fun equal_chara (Chara (x1, x2, x3, x4, x5, x6, x7, x8))
  (Chara (y1, y2, y3, y4, y5, y6, y7, y8)) =
  equal_bool x1 y1 andalso
    (equal_bool x2 y2 andalso
      (equal_bool x3 y3 andalso
        (equal_bool x4 y4 andalso
          (equal_bool x5 y5 andalso
            (equal_bool x6 y6 andalso
              (equal_bool x7 y7 andalso equal_bool x8 y8))))));

val equal_char = {equal = equal_chara} : char equal;

fun equal_msga (Public_key_encrypt (x61, x62)) (Signature (x71, x72)) = false
  | equal_msga (Signature (x71, x72)) (Public_key_encrypt (x61, x62)) = false
  | equal_msga (Sym_encrypt (x51, x52)) (Signature (x71, x72)) = false
  | equal_msga (Signature (x71, x72)) (Sym_encrypt (x51, x52)) = false
  | equal_msga (Sym_encrypt (x51, x52)) (Public_key_encrypt (x61, x62)) = false
  | equal_msga (Public_key_encrypt (x61, x62)) (Sym_encrypt (x51, x52)) = false
  | equal_msga (Pair (x41, x42)) (Signature (x71, x72)) = false
  | equal_msga (Signature (x71, x72)) (Pair (x41, x42)) = false
  | equal_msga (Pair (x41, x42)) (Public_key_encrypt (x61, x62)) = false
  | equal_msga (Public_key_encrypt (x61, x62)) (Pair (x41, x42)) = false
  | equal_msga (Pair (x41, x42)) (Sym_encrypt (x51, x52)) = false
  | equal_msga (Sym_encrypt (x51, x52)) (Pair (x41, x42)) = false
  | equal_msga (Hash x3) (Signature (x71, x72)) = false
  | equal_msga (Signature (x71, x72)) (Hash x3) = false
  | equal_msga (Hash x3) (Public_key_encrypt (x61, x62)) = false
  | equal_msga (Public_key_encrypt (x61, x62)) (Hash x3) = false
  | equal_msga (Hash x3) (Sym_encrypt (x51, x52)) = false
  | equal_msga (Sym_encrypt (x51, x52)) (Hash x3) = false
  | equal_msga (Hash x3) (Pair (x41, x42)) = false
  | equal_msga (Pair (x41, x42)) (Hash x3) = false
  | equal_msga (Var x2) (Signature (x71, x72)) = false
  | equal_msga (Signature (x71, x72)) (Var x2) = false
  | equal_msga (Var x2) (Public_key_encrypt (x61, x62)) = false
  | equal_msga (Public_key_encrypt (x61, x62)) (Var x2) = false
  | equal_msga (Var x2) (Sym_encrypt (x51, x52)) = false
  | equal_msga (Sym_encrypt (x51, x52)) (Var x2) = false
  | equal_msga (Var x2) (Pair (x41, x42)) = false
  | equal_msga (Pair (x41, x42)) (Var x2) = false
  | equal_msga (Var x2) (Hash x3) = false
  | equal_msga (Hash x3) (Var x2) = false
  | equal_msga (Cons x1) (Signature (x71, x72)) = false
  | equal_msga (Signature (x71, x72)) (Cons x1) = false
  | equal_msga (Cons x1) (Public_key_encrypt (x61, x62)) = false
  | equal_msga (Public_key_encrypt (x61, x62)) (Cons x1) = false
  | equal_msga (Cons x1) (Sym_encrypt (x51, x52)) = false
  | equal_msga (Sym_encrypt (x51, x52)) (Cons x1) = false
  | equal_msga (Cons x1) (Pair (x41, x42)) = false
  | equal_msga (Pair (x41, x42)) (Cons x1) = false
  | equal_msga (Cons x1) (Hash x3) = false
  | equal_msga (Hash x3) (Cons x1) = false
  | equal_msga (Cons x1) (Var x2) = false
  | equal_msga (Var x2) (Cons x1) = false
  | equal_msga (Signature (x71, x72)) (Signature (y71, y72)) =
    equal_msga x71 y71 andalso equal_msga x72 y72
  | equal_msga (Public_key_encrypt (x61, x62)) (Public_key_encrypt (y61, y62)) =
    equal_msga x61 y61 andalso equal_msga x62 y62
  | equal_msga (Sym_encrypt (x51, x52)) (Sym_encrypt (y51, y52)) =
    equal_msga x51 y51 andalso equal_msga x52 y52
  | equal_msga (Pair (x41, x42)) (Pair (y41, y42)) =
    equal_msga x41 y41 andalso equal_msga x42 y42
  | equal_msga (Hash x3) (Hash y3) = equal_msga x3 y3
  | equal_msga (Var x2) (Var y2) = equal_lista equal_char x2 y2
  | equal_msga (Cons x1) (Cons y1) = equal_lista equal_char x1 y1;

val equal_msg = {equal = equal_msga} : msg equal;

fun equal_list A_ = {equal = equal_lista A_} : ('a list) equal;

datatype ('a, 'b) term = Vara of 'b | Fun of 'a * ('a, 'b) term list;

fun equal_term A_ B_ = {equal = equal_terma A_ B_} : ('a, 'b) term equal
and equal_terma A_ B_ (Vara x1) (Fun (x21, x22)) = false
  | equal_terma A_ B_ (Fun (x21, x22)) (Vara x1) = false
  | equal_terma A_ B_ (Fun (x21, x22)) (Fun (y21, y22)) =
    eq A_ x21 y21 andalso equal_lista (equal_term A_ B_) x22 y22
  | equal_terma A_ B_ (Vara x1) (Vara y1) = eq B_ x1 y1;

datatype symbol = SCons of char list | SHash | SPair | SSym_encrypt |
  SPublic_key_encrypt | SSignature;

fun equal_symbola SPublic_key_encrypt SSignature = false
  | equal_symbola SSignature SPublic_key_encrypt = false
  | equal_symbola SSym_encrypt SSignature = false
  | equal_symbola SSignature SSym_encrypt = false
  | equal_symbola SSym_encrypt SPublic_key_encrypt = false
  | equal_symbola SPublic_key_encrypt SSym_encrypt = false
  | equal_symbola SPair SSignature = false
  | equal_symbola SSignature SPair = false
  | equal_symbola SPair SPublic_key_encrypt = false
  | equal_symbola SPublic_key_encrypt SPair = false
  | equal_symbola SPair SSym_encrypt = false
  | equal_symbola SSym_encrypt SPair = false
  | equal_symbola SHash SSignature = false
  | equal_symbola SSignature SHash = false
  | equal_symbola SHash SPublic_key_encrypt = false
  | equal_symbola SPublic_key_encrypt SHash = false
  | equal_symbola SHash SSym_encrypt = false
  | equal_symbola SSym_encrypt SHash = false
  | equal_symbola SHash SPair = false
  | equal_symbola SPair SHash = false
  | equal_symbola (SCons x1) SSignature = false
  | equal_symbola SSignature (SCons x1) = false
  | equal_symbola (SCons x1) SPublic_key_encrypt = false
  | equal_symbola SPublic_key_encrypt (SCons x1) = false
  | equal_symbola (SCons x1) SSym_encrypt = false
  | equal_symbola SSym_encrypt (SCons x1) = false
  | equal_symbola (SCons x1) SPair = false
  | equal_symbola SPair (SCons x1) = false
  | equal_symbola (SCons x1) SHash = false
  | equal_symbola SHash (SCons x1) = false
  | equal_symbola (SCons x1) (SCons y1) = equal_lista equal_char x1 y1
  | equal_symbola SSignature SSignature = true
  | equal_symbola SPublic_key_encrypt SPublic_key_encrypt = true
  | equal_symbola SSym_encrypt SSym_encrypt = true
  | equal_symbola SPair SPair = true
  | equal_symbola SHash SHash = true;

val equal_symbol = {equal = equal_symbola} : symbol equal;

datatype num = One | Bit0 of num | Bit1 of num;

val one_integera : IntInf.int = (1 : IntInf.int);

type 'a one = {one : 'a};
val one = #one : 'a one -> 'a;

val one_integer = {one = one_integera} : IntInf.int one;

type 'a zero = {zero : 'a};
val zero = #zero : 'a zero -> 'a;

val zero_integer = {zero = (0 : IntInf.int)} : IntInf.int zero;

type 'a zero_neq_one = {one_zero_neq_one : 'a one, zero_zero_neq_one : 'a zero};
val one_zero_neq_one = #one_zero_neq_one : 'a zero_neq_one -> 'a one;
val zero_zero_neq_one = #zero_zero_neq_one : 'a zero_neq_one -> 'a zero;

val zero_neq_one_integer =
  {one_zero_neq_one = one_integer, zero_zero_neq_one = zero_integer} :
  IntInf.int zero_neq_one;

datatype nat = Zero_nat | Suc of nat;

datatype 'a set = Set of 'a list | Coset of 'a list;

datatype constraint = Constraint of msg list * msg list * msg;

fun id x = (fn xa => xa) x;

fun zip (x :: xs) (y :: ys) = (x, y) :: zip xs ys
  | zip xs [] = []
  | zip [] ys = [];

fun filter p [] = []
  | filter p (x :: xs) = (if p x then x :: filter p xs else filter p xs);

fun membera A_ [] y = false
  | membera A_ (x :: xs) y = eq A_ x y orelse membera A_ xs y;

fun member A_ x (Coset xs) = not (membera A_ xs x)
  | member A_ x (Set xs) = membera A_ xs x;

fun removeAll A_ x [] = []
  | removeAll A_ x (y :: xs) =
    (if eq A_ x y then removeAll A_ x xs else y :: removeAll A_ x xs);

fun inserta A_ x xs = (if membera A_ xs x then xs else x :: xs);

fun insert A_ x (Coset xs) = Coset (removeAll A_ x xs)
  | insert A_ x (Set xs) = Set (inserta A_ x xs);

fun fold f (x :: xs) s = fold f xs (f x s)
  | fold f [] s = s;

fun sup_set A_ (Coset xs) a = Coset (filter (fn x => not (member A_ x a)) xs)
  | sup_set A_ (Set xs) a = fold (insert A_) xs a;

val bot_set : 'a set = Set [];

fun sup_seta A_ (Set xs) = fold (sup_set A_) xs bot_set;

fun map f [] = []
  | map f (x21 :: x22) = f x21 :: map f x22;

fun image f (Set xs) = Set (map f xs);

fun fv B_ (Vara x) = insert B_ x bot_set
  | fv B_ (Fun (f, l)) = sup_seta B_ (image (fv B_) (Set l));

fun maps f [] = []
  | maps f (x :: xs) = f x @ maps f xs;

fun null [] = true
  | null (x :: xs) = false;

fun foldl f a [] = a
  | foldl f a (x :: xs) = foldl f (f a x) xs;

fun embed (Cons s) = Fun (SCons s, [])
  | embed (Var s) = Vara s
  | embed (Hash m) = Fun (SHash, [embed m])
  | embed (Pair (m1, m2)) = Fun (SPair, [embed m1, embed m2])
  | embed (Sym_encrypt (m1, m2)) = Fun (SSym_encrypt, [embed m1, embed m2])
  | embed (Public_key_encrypt (m1, m2)) =
    Fun (SPublic_key_encrypt, [embed m1, embed m2])
  | embed (Signature (m1, m2)) = Fun (SSignature, [embed m1, embed m2]);

fun fun_upd A_ f a b = (fn x => (if eq A_ x a then b else f x));

fun sapply s (Fun (f, l)) = Fun (f, map (sapply s) l)
  | sapply s (Vara x) = s x;

fun scomp sigma tau = (fn x => sapply sigma (tau x));

fun gen_length n (x :: xs) = gen_length (Suc n) xs
  | gen_length n [] = n;

fun size_list x = gen_length Zero_nat x;

fun equal_nat Zero_nat (Suc x2) = false
  | equal_nat (Suc x2) Zero_nat = false
  | equal_nat (Suc x2) (Suc y2) = equal_nat x2 y2
  | equal_nat Zero_nat Zero_nat = true;

fun snd (x1, x2) = x2;

fun fst (x1, x2) = x1;

fun sapply_eq sigma eq = (sapply sigma (fst eq), sapply sigma (snd eq));

fun sapply_eq_system sigma l = map (sapply_eq sigma) l;

fun lifted_comp NONE tau = NONE
  | lifted_comp (SOME sigma) tau = SOME (scomp sigma tau);

fun unify A_ B_ [] = SOME Vara
  | unify A_ B_ ((Vara x, t) :: u) =
    (if not (member B_ x (fv B_ t))
      then lifted_comp (unify A_ B_ (sapply_eq_system (fun_upd B_ Vara x t) u))
             (fun_upd B_ Vara x t)
      else (if equal_terma A_ B_ (Vara x) t then unify A_ B_ u else NONE))
  | unify A_ B_ ((Fun (v, va), Vara y) :: u) =
    unify A_ B_ ((Vara y, Fun (v, va)) :: u)
  | unify A_ B_ ((Fun (f, ua), Fun (g, v)) :: u) =
    (if eq A_ f g andalso equal_nat (size_list ua) (size_list v)
      then unify A_ B_ (zip ua v @ u) else NONE);

fun m_sapply sigma (Cons s) = Cons s
  | m_sapply sigma (Var s) = sigma s
  | m_sapply sigma (Hash m) = Hash (m_sapply sigma m)
  | m_sapply sigma (Pair (m1, m2)) = Pair (m_sapply sigma m1, m_sapply sigma m2)
  | m_sapply sigma (Sym_encrypt (m1, m2)) =
    Sym_encrypt (m_sapply sigma m1, m_sapply sigma m2)
  | m_sapply sigma (Public_key_encrypt (m1, m2)) =
    Public_key_encrypt (m_sapply sigma m1, m_sapply sigma m2)
  | m_sapply sigma (Signature (m1, m2)) =
    Signature (m_sapply sigma m1, m_sapply sigma m2);

fun m_scomp sigma tau = (fn x => m_sapply sigma (tau x));

fun msg_of_term (Vara s) = Var s
  | msg_of_term (Fun (SCons s, [])) = Cons s
  | msg_of_term (Fun (SHash, [t])) = Hash (msg_of_term t)
  | msg_of_term (Fun (SPair, [t1, t2])) = Pair (msg_of_term t1, msg_of_term t2)
  | msg_of_term (Fun (SSym_encrypt, [t1, t2])) =
    Sym_encrypt (msg_of_term t1, msg_of_term t2)
  | msg_of_term (Fun (SPublic_key_encrypt, [t1, t2])) =
    Public_key_encrypt (msg_of_term t1, msg_of_term t2)
  | msg_of_term (Fun (SSignature, [t1, t2])) =
    Signature (msg_of_term t1, msg_of_term t2)
  | msg_of_term (Fun (SHash, [])) = (raise Fail "undefined")
  | msg_of_term (Fun (SHash, v :: vc :: vd)) = (raise Fail "undefined")
  | msg_of_term (Fun (SPair, [])) = (raise Fail "undefined")
  | msg_of_term (Fun (SPair, [v])) = (raise Fail "undefined")
  | msg_of_term (Fun (SPair, v :: vc :: ve :: vf)) = (raise Fail "undefined")
  | msg_of_term (Fun (SSym_encrypt, [])) = (raise Fail "undefined")
  | msg_of_term (Fun (SSym_encrypt, [v])) = (raise Fail "undefined")
  | msg_of_term (Fun (SSym_encrypt, v :: vc :: ve :: vf)) =
    (raise Fail "undefined")
  | msg_of_term (Fun (SPublic_key_encrypt, [])) = (raise Fail "undefined")
  | msg_of_term (Fun (SPublic_key_encrypt, [v])) = (raise Fail "undefined")
  | msg_of_term (Fun (SPublic_key_encrypt, v :: vc :: ve :: vf)) =
    (raise Fail "undefined")
  | msg_of_term (Fun (SSignature, [])) = (raise Fail "undefined")
  | msg_of_term (Fun (SSignature, [v])) = (raise Fail "undefined")
  | msg_of_term (Fun (SSignature, v :: vc :: ve :: vf)) =
    (raise Fail "undefined")
  | msg_of_term (Fun (SCons va, vb :: vc)) = (raise Fail "undefined")
  | msg_of_term (Fun (v, vb :: va :: vc :: ve)) = (raise Fail "undefined");

fun lift_subst NONE = NONE
  | lift_subst (SOME sigma) = SOME (msg_of_term o sigma);

fun embed_eq (m1, m2) = (embed m1, embed m2);

fun embed_eqs [] = []
  | embed_eqs (eq :: u) = embed_eq eq :: embed_eqs u;

fun m_unify u =
  lift_subst (unify equal_symbol (equal_list equal_char) (embed_eqs u));

val iota : char list =
  [Chara (true, false, false, true, false, true, true, false),
    Chara (false, true, true, true, false, true, true, false),
    Chara (false, false, true, false, true, true, true, false),
    Chara (false, true, false, false, true, true, true, false),
    Chara (true, false, true, false, true, true, true, false),
    Chara (false, false, true, false, false, true, true, false),
    Chara (true, false, true, false, false, true, true, false),
    Chara (false, true, false, false, true, true, true, false)];

val intruder : msg = Cons iota;

val ktp : constraint list =
  [Constraint
     ([Cons [Chara (true, false, false, false, false, true, true, false)],
        Cons [Chara (false, true, false, false, false, true, true, false)],
        intruder],
       [], Pair (Var [Chara (true, false, false, false, false, false, true,
                              false),
                       Chara (false, false, false, false, true, true, false,
                               false)],
                  Var [Chara (false, true, false, false, false, false, true,
                               false),
                        Chara (false, false, false, false, true, true, false,
                                false)])),
    Constraint
      ([Public_key_encrypt
          (Pair (Cons [Chara (true, true, false, true, false, true, true,
                               false),
                        Chara (false, false, false, false, true, true, false,
                                false)],
                  Signature
                    (Cons [Chara (true, true, false, true, false, true, true,
                                   false),
                            Chara (false, false, false, false, true, true,
                                    false, false)],
                      Var [Chara (true, false, false, false, false, false, true,
                                   false),
                            Chara (false, false, false, false, true, true,
                                    false, false)])),
            Var [Chara (false, true, false, false, false, false, true, false),
                  Chara (false, false, false, false, true, true, false,
                          false)]),
         Cons [Chara (true, false, false, false, false, true, true, false)],
         Cons [Chara (false, true, false, false, false, true, true, false)],
         intruder],
        [], Public_key_encrypt
              (Pair (Var [Chara (true, true, false, true, false, false, true,
                                  false),
                           Chara (true, false, false, false, true, true, false,
                                   false)],
                      Signature
                        (Var [Chara (true, true, false, true, false, false,
                                      true, false),
                               Chara (true, false, false, false, true, true,
                                       false, false)],
                          Cons [Chara (true, false, false, false, false, true,
true, false)])),
                Cons [Chara (false, true, false, false, false, true, true,
                              false)])),
    Constraint
      ([Sym_encrypt
          (Cons [Chara (true, false, true, true, false, true, true, false),
                  Chara (true, false, false, false, true, true, false, false)],
            Var [Chara (true, true, false, true, false, false, true, false),
                  Chara (true, false, false, false, true, true, false, false)]),
         Public_key_encrypt
           (Pair (Cons [Chara (true, true, false, true, false, true, true,
                                false),
                         Chara (false, false, false, false, true, true, false,
                                 false)],
                   Signature
                     (Cons [Chara (true, true, false, true, false, true, true,
                                    false),
                             Chara (false, false, false, false, true, true,
                                     false, false)],
                       Var [Chara (true, false, false, false, false, false,
                                    true, false),
                             Chara (false, false, false, false, true, true,
                                     false, false)])),
             Var [Chara (false, true, false, false, false, false, true, false),
                   Chara (false, false, false, false, true, true, false,
                           false)]),
         Cons [Chara (true, false, false, false, false, true, true, false)],
         Cons [Chara (false, true, false, false, false, true, true, false)],
         intruder],
        [], Sym_encrypt
              (Var [Chara (false, true, false, true, true, false, true, false),
                     Chara (false, false, false, false, true, true, false,
                             false)],
                Cons [Chara (true, true, false, true, false, true, true, false),
                       Chara (false, false, false, false, true, true, false,
                               false)])),
    Constraint
      ([Sym_encrypt
          (Cons [Chara (true, false, true, true, false, true, true, false),
                  Chara (true, false, false, false, true, true, false, false)],
            Var [Chara (true, true, false, true, false, false, true, false),
                  Chara (true, false, false, false, true, true, false, false)]),
         Public_key_encrypt
           (Pair (Cons [Chara (true, true, false, true, false, true, true,
                                false),
                         Chara (false, false, false, false, true, true, false,
                                 false)],
                   Signature
                     (Cons [Chara (true, true, false, true, false, true, true,
                                    false),
                             Chara (false, false, false, false, true, true,
                                     false, false)],
                       Var [Chara (true, false, false, false, false, false,
                                    true, false),
                             Chara (false, false, false, false, true, true,
                                     false, false)])),
             Var [Chara (false, true, false, false, false, false, true, false),
                   Chara (false, false, false, false, true, true, false,
                           false)]),
         Cons [Chara (true, false, false, false, false, true, true, false)],
         Cons [Chara (false, true, false, false, false, true, true, false)],
         intruder],
        [], Pair (Var [Chara (true, true, false, true, false, false, true,
                               false),
                        Chara (true, false, false, false, true, true, false,
                                false)],
                   Cons [Chara (true, false, true, true, false, true, true,
                                 false),
                          Chara (true, false, false, false, true, true, false,
                                  false)]))];

val nspk : constraint list =
  [Constraint
     ([Cons [Chara (true, false, false, false, false, true, true, false)],
        Cons [Chara (false, true, false, false, false, true, true, false)],
        intruder],
       [], Pair (Var [Chara (true, false, false, false, false, false, true,
                              false),
                       Chara (false, false, false, false, true, true, false,
                               false)],
                  Var [Chara (false, true, false, false, false, false, true,
                               false),
                        Chara (false, false, false, false, true, true, false,
                                false)])),
    Constraint
      ([Public_key_encrypt
          (Pair (Cons [Chara (false, true, true, true, false, true, true,
                               false),
                        Chara (true, false, false, false, false, true, true,
                                false),
                        Chara (false, false, false, false, true, true, false,
                                false)],
                  Var [Chara (true, false, false, false, false, false, true,
                               false),
                        Chara (false, false, false, false, true, true, false,
                                false)]),
            Var [Chara (false, true, false, false, false, false, true, false),
                  Chara (false, false, false, false, true, true, false,
                          false)]),
         Cons [Chara (true, false, false, false, false, true, true, false)],
         Cons [Chara (false, true, false, false, false, true, true, false)],
         intruder],
        [], Public_key_encrypt
              (Pair (Var [Chara (false, true, true, true, false, false, true,
                                  false),
                           Chara (true, false, false, false, false, false, true,
                                   false),
                           Chara (true, false, false, false, true, true, false,
                                   false)],
                      Cons [Chara (true, false, false, false, false, true, true,
                                    false)]),
                Cons [Chara (false, true, false, false, false, true, true,
                              false)])),
    Constraint
      ([Public_key_encrypt
          (Pair (Var [Chara (false, true, true, true, false, false, true,
                              false),
                       Chara (true, false, false, false, false, false, true,
                               false),
                       Chara (true, false, false, false, true, true, false,
                               false)],
                  Cons [Chara (false, true, true, true, false, true, true,
                                false),
                         Chara (false, true, false, false, false, true, true,
                                 false),
                         Chara (true, false, false, false, true, true, false,
                                 false)]),
            Cons [Chara (true, false, false, false, false, true, true, false)]),
         Public_key_encrypt
           (Pair (Cons [Chara (false, true, true, true, false, true, true,
                                false),
                         Chara (true, false, false, false, false, true, true,
                                 false),
                         Chara (false, false, false, false, true, true, false,
                                 false)],
                   Var [Chara (true, false, false, false, false, false, true,
                                false),
                         Chara (false, false, false, false, true, true, false,
                                 false)]),
             Var [Chara (false, true, false, false, false, false, true, false),
                   Chara (false, false, false, false, true, true, false,
                           false)]),
         Cons [Chara (true, false, false, false, false, true, true, false)],
         Cons [Chara (false, true, false, false, false, true, true, false)],
         intruder],
        [], Public_key_encrypt
              (Pair (Cons [Chara (false, true, true, true, false, true, true,
                                   false),
                            Chara (true, false, false, false, false, true, true,
                                    false),
                            Chara (false, false, false, false, true, true,
                                    false, false)],
                      Var [Chara (false, true, true, true, false, false, true,
                                   false),
                            Chara (false, true, false, false, false, false,
                                    true, false),
                            Chara (false, false, false, false, true, true,
                                    false, false)]),
                Var [Chara (true, false, false, false, false, false, true,
                             false),
                      Chara (false, false, false, false, true, true, false,
                              false)])),
    Constraint
      ([Public_key_encrypt
          (Var [Chara (false, true, true, true, false, false, true, false),
                 Chara (false, true, false, false, false, false, true, false),
                 Chara (false, false, false, false, true, true, false, false)],
            Var [Chara (false, true, false, false, false, false, true, false),
                  Chara (false, false, false, false, true, true, false,
                          false)]),
         Public_key_encrypt
           (Pair (Var [Chara (false, true, true, true, false, false, true,
                               false),
                        Chara (true, false, false, false, false, false, true,
                                false),
                        Chara (true, false, false, false, true, true, false,
                                false)],
                   Cons [Chara (false, true, true, true, false, true, true,
                                 false),
                          Chara (false, true, false, false, false, true, true,
                                  false),
                          Chara (true, false, false, false, true, true, false,
                                  false)]),
             Cons [Chara (true, false, false, false, false, true, true,
                           false)]),
         Public_key_encrypt
           (Pair (Cons [Chara (false, true, true, true, false, true, true,
                                false),
                         Chara (true, false, false, false, false, true, true,
                                 false),
                         Chara (false, false, false, false, true, true, false,
                                 false)],
                   Var [Chara (true, false, false, false, false, false, true,
                                false),
                         Chara (false, false, false, false, true, true, false,
                                 false)]),
             Var [Chara (false, true, false, false, false, false, true, false),
                   Chara (false, false, false, false, true, true, false,
                           false)]),
         Cons [Chara (true, false, false, false, false, true, true, false)],
         Cons [Chara (false, true, false, false, false, true, true, false)],
         intruder],
        [], Public_key_encrypt
              (Cons [Chara (false, true, true, true, false, true, true, false),
                      Chara (false, true, false, false, false, true, true,
                              false),
                      Chara (true, false, false, false, true, true, false,
                              false)],
                Cons [Chara (false, true, false, false, false, true, true,
                              false)])),
    Constraint
      ([Public_key_encrypt
          (Var [Chara (false, true, true, true, false, false, true, false),
                 Chara (false, true, false, false, false, false, true, false),
                 Chara (false, false, false, false, true, true, false, false)],
            Var [Chara (false, true, false, false, false, false, true, false),
                  Chara (false, false, false, false, true, true, false,
                          false)]),
         Public_key_encrypt
           (Pair (Var [Chara (false, true, true, true, false, false, true,
                               false),
                        Chara (true, false, false, false, false, false, true,
                                false),
                        Chara (true, false, false, false, true, true, false,
                                false)],
                   Cons [Chara (false, true, true, true, false, true, true,
                                 false),
                          Chara (false, true, false, false, false, true, true,
                                  false),
                          Chara (true, false, false, false, true, true, false,
                                  false)]),
             Cons [Chara (true, false, false, false, false, true, true,
                           false)]),
         Public_key_encrypt
           (Pair (Cons [Chara (false, true, true, true, false, true, true,
                                false),
                         Chara (true, false, false, false, false, true, true,
                                 false),
                         Chara (false, false, false, false, true, true, false,
                                 false)],
                   Var [Chara (true, false, false, false, false, false, true,
                                false),
                         Chara (false, false, false, false, true, true, false,
                                 false)]),
             Var [Chara (false, true, false, false, false, false, true, false),
                   Chara (false, false, false, false, true, true, false,
                           false)]),
         Cons [Chara (true, false, false, false, false, true, true, false)],
         Cons [Chara (false, true, false, false, false, true, true, false)],
         intruder],
        [], Pair (Var [Chara (false, true, true, true, false, false, true,
                               false),
                        Chara (true, false, false, false, false, false, true,
                                false),
                        Chara (true, false, false, false, true, true, false,
                                false)],
                   Cons [Chara (false, true, true, true, false, true, true,
                                 false),
                          Chara (false, true, false, false, false, true, true,
                                  false),
                          Chara (true, false, false, false, true, true, false,
                                  false)]))];

fun of_bool A_ true = one (one_zero_neq_one A_)
  | of_bool A_ false = zero (zero_zero_neq_one A_);

fun integer_of_char (Chara (b0, b1, b2, b3, b4, b5, b6, b7)) =
  IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (of_bool
                        zero_neq_one_integer
                        b7, (2 : IntInf.int)), of_bool zero_neq_one_integer
         b6), (2 : IntInf.int)), of_bool zero_neq_one_integer
                                   b5), (2 : IntInf.int)), of_bool
                     zero_neq_one_integer
                     b4), (2 : IntInf.int)), of_bool zero_neq_one_integer
       b3), (2 : IntInf.int)), of_bool zero_neq_one_integer
                                 b2), (2 : IntInf.int)), of_bool
                   zero_neq_one_integer
                   b1), (2 : IntInf.int)), of_bool zero_neq_one_integer b0);

fun implode cs =
  (String.implode
    o map (fn k => if 0 <= k andalso k < 128 then (Char.chr o IntInf.toInt) k else raise Fail "Non-ASCII character in literal"))
    (map integer_of_char cs);

fun c_sapply sigma (Constraint (msa, ms, msg)) =
  Constraint
    (map (m_sapply sigma) msa, map (m_sapply sigma) ms, m_sapply sigma msg);

fun c_dec_term (Constraint (m, a, t)) (Pair (u, v)) =
  let
    val ma = removeAll equal_msg (Pair (u, v)) m;
  in
    [([Constraint (u :: v :: ma, Pair (u, v) :: a, t)], Var)]
  end
  | c_dec_term (Constraint (m, a, t)) (Sym_encrypt (u, k)) =
    let
      val ma = removeAll equal_msg (Sym_encrypt (u, k)) m;
    in
      [([Constraint (u :: ma, Sym_encrypt (u, k) :: a, t),
          Constraint (ma, Sym_encrypt (u, k) :: a, k)],
         Var)]
    end
  | c_dec_term (Constraint (m, a, t)) (Public_key_encrypt (u, Cons i)) =
    (if equal_lista equal_char i iota
      then let
             val ma = removeAll equal_msg (Public_key_encrypt (u, intruder)) m;
           in
             [([Constraint (u :: ma, Public_key_encrypt (u, intruder) :: a, t)],
                Var)]
           end
      else [])
  | c_dec_term (Constraint (m, a, t)) (Public_key_encrypt (u, Var x)) =
    let
      val sigma = fun_upd (equal_list equal_char) Var x intruder;
    in
      [([c_sapply sigma (Constraint (m, a, t))], sigma)]
    end
  | c_dec_term (Constraint (m, a, t)) (Cons v) = []
  | c_dec_term (Constraint (m, a, t)) (Var v) = []
  | c_dec_term (Constraint (m, a, t)) (Hash v) = []
  | c_dec_term (Constraint (m, a, t)) (Public_key_encrypt (v, Hash vb)) = []
  | c_dec_term (Constraint (m, a, t)) (Public_key_encrypt (v, Pair (vb, vc))) =
    []
  | c_dec_term (Constraint (m, a, t))
    (Public_key_encrypt (v, Sym_encrypt (vb, vc))) = []
  | c_dec_term (Constraint (m, a, t))
    (Public_key_encrypt (v, Public_key_encrypt (vb, vc))) = []
  | c_dec_term (Constraint (m, a, t))
    (Public_key_encrypt (v, Signature (vb, vc))) = []
  | c_dec_term (Constraint (m, a, t)) (Signature (v, va)) = [];

fun c_dec (Constraint (m, a, t)) = maps (c_dec_term (Constraint (m, a, t))) m;

fun c_comp (Constraint (m, a, Hash t)) = [([Constraint (m, a, t)], Var)]
  | c_comp (Constraint (m, a, Pair (t1, t2))) =
    [([Constraint (m, a, t1), Constraint (m, a, t2)], Var)]
  | c_comp (Constraint (ma, a, Sym_encrypt (m, k))) =
    [([Constraint (ma, a, m), Constraint (ma, a, k)], Var)]
  | c_comp (Constraint (ma, a, Public_key_encrypt (m, k))) =
    [([Constraint (ma, a, m), Constraint (ma, a, k)], Var)]
  | c_comp (Constraint (m, a, Signature (t, Cons i))) =
    (if equal_lista equal_char i iota then [([Constraint (m, a, t)], Var)]
      else [])
  | c_comp (Constraint (m, a, Cons v)) = []
  | c_comp (Constraint (m, a, Var v)) = []
  | c_comp (Constraint (m, a, Signature (v, Var vb))) = []
  | c_comp (Constraint (m, a, Signature (v, Hash vb))) = []
  | c_comp (Constraint (m, a, Signature (v, Pair (vb, vc)))) = []
  | c_comp (Constraint (m, a, Signature (v, Sym_encrypt (vb, vc)))) = []
  | c_comp (Constraint (m, a, Signature (v, Public_key_encrypt (vb, vc)))) = []
  | c_comp (Constraint (m, a, Signature (v, Signature (vb, vc)))) = [];

fun c_unify (Constraint (m, a, Var uu)) = []
  | c_unify (Constraint (m, a, Cons v)) =
    maps (fn u =>
           (case m_unify [(Cons v, u)] of NONE => []
             | SOME sigma => [([], sigma)]))
      (m @ a)
  | c_unify (Constraint (m, a, Hash v)) =
    maps (fn u =>
           (case m_unify [(Hash v, u)] of NONE => []
             | SOME sigma => [([], sigma)]))
      (m @ a)
  | c_unify (Constraint (m, a, Pair (v, va))) =
    maps (fn u =>
           (case m_unify [(Pair (v, va), u)] of NONE => []
             | SOME sigma => [([], sigma)]))
      (m @ a)
  | c_unify (Constraint (m, a, Sym_encrypt (v, va))) =
    maps (fn u =>
           (case m_unify [(Sym_encrypt (v, va), u)] of NONE => []
             | SOME sigma => [([], sigma)]))
      (m @ a)
  | c_unify (Constraint (m, a, Public_key_encrypt (v, va))) =
    maps (fn u =>
           (case m_unify [(Public_key_encrypt (v, va), u)] of NONE => []
             | SOME sigma => [([], sigma)]))
      (m @ a)
  | c_unify (Constraint (m, a, Signature (v, va))) =
    maps (fn u =>
           (case m_unify [(Signature (v, va), u)] of NONE => []
             | SOME sigma => [([], sigma)]))
      (m @ a);

fun c_succ c = c_unify c @ c_comp c @ c_dec c;

fun fold_option f [] = NONE
  | fold_option f (a :: asa) =
    (case f a of NONE => fold_option f asa | SOME aa => SOME aa);

fun list_all p [] = true
  | list_all p (x :: xs) = p x andalso list_all p xs;

fun c_simple (Constraint (m, a, Var uu)) = true
  | c_simple (Constraint (v, va, Cons vc)) = false
  | c_simple (Constraint (v, va, Hash vc)) = false
  | c_simple (Constraint (v, va, Pair (vc, vd))) = false
  | c_simple (Constraint (v, va, Sym_encrypt (vc, vd))) = false
  | c_simple (Constraint (v, va, Public_key_encrypt (vc, vd))) = false
  | c_simple (Constraint (v, va, Signature (vc, vd))) = false;

fun cs_simple cs = list_all c_simple cs;

fun cs_sapply sigma cs = map (c_sapply sigma) cs;

fun cs_succ_aux uu [] = []
  | cs_succ_aux csa (c :: cs) =
    map (fn (csb, sigma) =>
          (cs_sapply sigma csa @ csb @ cs_sapply sigma cs, sigma))
      (c_succ c) @
      cs_succ_aux (csa @ [c]) cs;

fun cs_succ cs = cs_succ_aux [] cs;

fun search ics =
  (if cs_simple ics then SOME (ics, Var)
    else fold_option
           (fn (cs, sigma) =>
             (case search cs of NONE => NONE
               | SOME (csa, sigmaa) => SOME (csa, m_scomp sigmaa sigma)))
           (cs_succ ics));

fun print_list f m =
  [Chara (true, true, false, true, true, false, true, false)] @
    foldl (fn out => fn ma =>
            out @ (if null out then []
                    else [Chara (false, false, true, true, false, true, false,
                                  false),
                           Chara (false, false, false, false, false, true,
                                   false, false)]) @
                    f ma)
      [] m @
      [Chara (true, false, true, true, true, false, true, false)];

fun print_msg (Cons s) =
  [Chara (false, false, false, true, false, true, false, false),
    Chara (true, true, false, false, false, false, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (false, true, true, true, false, true, true, false),
    Chara (true, true, false, false, true, true, true, false),
    Chara (false, false, false, false, false, true, false, false)] @
    s @ [Chara (true, false, false, true, false, true, false, false)]
  | print_msg (Var s) =
    [Chara (false, false, false, true, false, true, false, false),
      Chara (false, true, true, false, true, false, true, false),
      Chara (true, false, false, false, false, true, true, false),
      Chara (false, true, false, false, true, true, true, false),
      Chara (false, false, false, false, false, true, false, false)] @
      s @ [Chara (true, false, false, true, false, true, false, false)]
  | print_msg (Hash m) =
    [Chara (false, false, false, true, false, true, false, false),
      Chara (false, false, false, true, false, false, true, false),
      Chara (true, false, false, false, false, true, true, false),
      Chara (true, true, false, false, true, true, true, false),
      Chara (false, false, false, true, false, true, true, false),
      Chara (false, false, false, false, false, true, false, false)] @
      print_msg m @
        [Chara (true, false, false, true, false, true, false, false)]
  | print_msg (Pair (u, v)) =
    [Chara (false, false, false, true, false, true, false, false),
      Chara (false, false, false, false, true, false, true, false),
      Chara (true, false, false, false, false, true, true, false),
      Chara (true, false, false, true, false, true, true, false),
      Chara (false, true, false, false, true, true, true, false),
      Chara (false, false, false, false, false, true, false, false)] @
      print_msg u @
        [Chara (false, false, false, false, false, true, false, false)] @
          print_msg v @
            [Chara (true, false, false, true, false, true, false, false)]
  | print_msg (Sym_encrypt (m, k)) =
    [Chara (false, false, false, true, false, true, false, false),
      Chara (true, true, false, false, true, false, true, false),
      Chara (true, false, false, true, true, true, true, false),
      Chara (true, false, true, true, false, true, true, false),
      Chara (true, true, true, true, true, false, true, false),
      Chara (true, false, true, false, false, true, true, false),
      Chara (false, true, true, true, false, true, true, false),
      Chara (true, true, false, false, false, true, true, false),
      Chara (false, true, false, false, true, true, true, false),
      Chara (true, false, false, true, true, true, true, false),
      Chara (false, false, false, false, true, true, true, false),
      Chara (false, false, true, false, true, true, true, false),
      Chara (false, false, false, false, false, true, false, false)] @
      print_msg m @
        [Chara (false, false, false, false, false, true, false, false)] @
          print_msg k @
            [Chara (true, false, false, true, false, true, false, false)]
  | print_msg (Public_key_encrypt (m, k)) =
    [Chara (false, false, false, true, false, true, false, false),
      Chara (false, false, false, false, true, false, true, false),
      Chara (true, false, true, false, true, true, true, false),
      Chara (false, true, false, false, false, true, true, false),
      Chara (false, false, true, true, false, true, true, false),
      Chara (true, false, false, true, false, true, true, false),
      Chara (true, true, false, false, false, true, true, false),
      Chara (true, true, true, true, true, false, true, false),
      Chara (true, true, false, true, false, true, true, false),
      Chara (true, false, true, false, false, true, true, false),
      Chara (true, false, false, true, true, true, true, false),
      Chara (true, true, true, true, true, false, true, false),
      Chara (true, false, true, false, false, true, true, false),
      Chara (false, true, true, true, false, true, true, false),
      Chara (true, true, false, false, false, true, true, false),
      Chara (false, true, false, false, true, true, true, false),
      Chara (true, false, false, true, true, true, true, false),
      Chara (false, false, false, false, true, true, true, false),
      Chara (false, false, true, false, true, true, true, false),
      Chara (false, false, false, false, false, true, false, false)] @
      print_msg m @
        [Chara (false, false, false, false, false, true, false, false)] @
          print_msg k @
            [Chara (true, false, false, true, false, true, false, false)]
  | print_msg (Signature (m, k)) =
    [Chara (false, false, false, true, false, true, false, false),
      Chara (true, true, false, false, true, false, true, false),
      Chara (true, false, false, true, false, true, true, false),
      Chara (true, true, true, false, false, true, true, false),
      Chara (false, true, true, true, false, true, true, false),
      Chara (true, false, false, false, false, true, true, false),
      Chara (false, false, true, false, true, true, true, false),
      Chara (true, false, true, false, true, true, true, false),
      Chara (false, true, false, false, true, true, true, false),
      Chara (true, false, true, false, false, true, true, false),
      Chara (false, false, false, false, false, true, false, false)] @
      print_msg m @
        [Chara (false, false, false, false, false, true, false, false)] @
          print_msg k @
            [Chara (true, false, false, true, false, true, false, false)];

fun print_c (Constraint (m, a, t)) =
  [Chara (false, false, false, true, false, true, false, false)] @
    print_list print_msg m @
      [Chara (false, false, false, false, false, true, false, false),
        Chara (false, false, true, true, true, true, true, false),
        Chara (false, false, false, false, false, true, false, false)] @
        print_list print_msg a @
          [Chara (false, false, false, false, false, true, false, false),
            Chara (true, false, true, true, false, true, false, false),
            Chara (true, false, true, true, false, true, false, false),
            Chara (false, true, true, true, true, true, false, false),
            Chara (false, false, false, false, false, true, false, false)] @
            print_msg t @
              [Chara (true, false, false, true, false, true, false, false)];

val ktp_vars : (char list) list =
  [[Chara (true, false, false, false, false, false, true, false),
     Chara (false, false, false, false, true, true, false, false)],
    [Chara (false, true, false, false, false, false, true, false),
      Chara (false, false, false, false, true, true, false, false)],
    [Chara (true, true, false, true, false, false, true, false),
      Chara (true, false, false, false, true, true, false, false)],
    [Chara (false, true, false, true, true, false, true, false),
      Chara (false, false, false, false, true, true, false, false)]];

val nspk_vars : (char list) list =
  [[Chara (true, false, false, false, false, false, true, false),
     Chara (false, false, false, false, true, true, false, false)],
    [Chara (false, true, false, false, false, false, true, false),
      Chara (false, false, false, false, true, true, false, false)],
    [Chara (false, true, true, true, false, false, true, false),
      Chara (true, false, false, false, false, false, true, false),
      Chara (true, false, false, false, true, true, false, false)],
    [Chara (false, true, true, true, false, false, true, false),
      Chara (false, true, false, false, false, false, true, false),
      Chara (false, false, false, false, true, true, false, false)]];

fun search_slow ics =
  (if cs_simple ics then SOME (ics, Var)
    else fold_option id
           (map (fn (cs, sigma) =>
                  (case search_slow cs of NONE => NONE
                    | SOME (csa, sigmaa) => SOME (csa, m_scomp sigmaa sigma)))
             (cs_succ ics)));

fun print_search_result NONE =
  [Chara (false, true, true, true, false, false, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (true, true, false, false, true, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (false, false, true, true, false, true, true, false),
    Chara (true, false, true, false, true, true, true, false),
    Chara (false, false, true, false, true, true, true, false),
    Chara (true, false, false, true, false, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (false, true, true, true, false, true, true, false),
    Chara (false, true, true, true, false, true, false, false)]
  | print_search_result (SOME (cs, sigma)) =
    [Chara (true, true, false, false, true, false, true, false),
      Chara (true, false, false, true, false, true, true, false),
      Chara (true, false, true, true, false, true, true, false),
      Chara (false, false, false, false, true, true, true, false),
      Chara (false, false, true, true, false, true, true, false),
      Chara (true, false, true, false, false, true, true, false),
      Chara (false, false, false, false, false, true, false, false),
      Chara (true, true, false, false, false, true, true, false),
      Chara (true, true, true, true, false, true, true, false),
      Chara (false, true, true, true, false, true, true, false),
      Chara (true, true, false, false, true, true, true, false),
      Chara (false, false, true, false, true, true, true, false),
      Chara (false, true, false, false, true, true, true, false),
      Chara (true, false, false, false, false, true, true, false),
      Chara (true, false, false, true, false, true, true, false),
      Chara (false, true, true, true, false, true, true, false),
      Chara (false, false, true, false, true, true, true, false),
      Chara (true, true, false, false, true, true, true, false),
      Chara (false, true, false, true, true, true, false, false),
      Chara (false, false, false, false, false, true, false, false)] @
      print_list print_c cs @
        [Chara (true, true, false, true, true, true, false, false),
          Chara (false, false, false, false, false, true, false, false),
          Chara (true, true, false, false, true, false, true, false),
          Chara (true, false, true, false, true, true, true, false),
          Chara (false, true, false, false, false, true, true, false),
          Chara (true, true, false, false, true, true, true, false),
          Chara (false, false, true, false, true, true, true, false),
          Chara (true, false, false, true, false, true, true, false),
          Chara (false, false, true, false, true, true, true, false),
          Chara (true, false, true, false, true, true, true, false),
          Chara (false, false, true, false, true, true, true, false),
          Chara (true, false, false, true, false, true, true, false),
          Chara (true, true, true, true, false, true, true, false),
          Chara (false, true, true, true, false, true, true, false),
          Chara (true, true, false, false, true, true, true, false),
          Chara (false, true, false, true, true, true, false, false),
          Chara (false, false, false, false, false, true, false, false)] @
          print_list
            (fn (s, m) =>
              [Chara (false, false, false, true, false, true, false, false)] @
                s @ [Chara (false, false, false, false, false, true, false,
                             false),
                      Chara (true, false, true, true, false, true, false,
                              false),
                      Chara (true, false, true, true, false, true, false,
                              false),
                      Chara (false, true, true, true, true, true, false, false),
                      Chara (false, false, false, false, false, true, false,
                              false)] @
                      print_msg m @
                        [Chara (true, false, false, true, false, true, false,
                                 false)])
            sigma;

fun map_option f NONE = NONE
  | map_option f (SOME x2) = SOME (f x2);

fun print_search ns cs =
  implode
    (print_search_result
      (map_option (fn (csa, sigma) => (csa, map (fn v => (v, sigma v)) ns))
        (search cs)));

fun print_search_slow ns cs =
  implode
    (print_search_result
      (map_option (fn (csa, sigma) => (csa, map (fn v => (v, sigma v)) ns))
        (search_slow cs)));

end; (*struct Search*)
