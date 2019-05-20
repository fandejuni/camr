{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Search(Char, Constraint, print_search_KTP, print_search_NSPK,
          print_search_slow_KTP, print_search_slow_NSPK)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;

data Char = Char Bool Bool Bool Bool Bool Bool Bool Bool;

data Msg = Cons [Char] | Var [Char] | Hash Msg | Pair Msg Msg
  | Sym_encrypt Msg Msg | Public_key_encrypt Msg Msg | Signature Msg Msg;

equal_char :: Char -> Char -> Bool;
equal_char (Char x1 x2 x3 x4 x5 x6 x7 x8) (Char y1 y2 y3 y4 y5 y6 y7 y8) =
  x1 == y1 &&
    x2 == y2 &&
      x3 == y3 && x4 == y4 && x5 == y5 && x6 == y6 && x7 == y7 && x8 == y8;

instance Eq Char where {
  a == b = equal_char a b;
};

equal_msg :: Msg -> Msg -> Bool;
equal_msg (Public_key_encrypt x61 x62) (Signature x71 x72) = False;
equal_msg (Signature x71 x72) (Public_key_encrypt x61 x62) = False;
equal_msg (Sym_encrypt x51 x52) (Signature x71 x72) = False;
equal_msg (Signature x71 x72) (Sym_encrypt x51 x52) = False;
equal_msg (Sym_encrypt x51 x52) (Public_key_encrypt x61 x62) = False;
equal_msg (Public_key_encrypt x61 x62) (Sym_encrypt x51 x52) = False;
equal_msg (Pair x41 x42) (Signature x71 x72) = False;
equal_msg (Signature x71 x72) (Pair x41 x42) = False;
equal_msg (Pair x41 x42) (Public_key_encrypt x61 x62) = False;
equal_msg (Public_key_encrypt x61 x62) (Pair x41 x42) = False;
equal_msg (Pair x41 x42) (Sym_encrypt x51 x52) = False;
equal_msg (Sym_encrypt x51 x52) (Pair x41 x42) = False;
equal_msg (Hash x3) (Signature x71 x72) = False;
equal_msg (Signature x71 x72) (Hash x3) = False;
equal_msg (Hash x3) (Public_key_encrypt x61 x62) = False;
equal_msg (Public_key_encrypt x61 x62) (Hash x3) = False;
equal_msg (Hash x3) (Sym_encrypt x51 x52) = False;
equal_msg (Sym_encrypt x51 x52) (Hash x3) = False;
equal_msg (Hash x3) (Pair x41 x42) = False;
equal_msg (Pair x41 x42) (Hash x3) = False;
equal_msg (Var x2) (Signature x71 x72) = False;
equal_msg (Signature x71 x72) (Var x2) = False;
equal_msg (Var x2) (Public_key_encrypt x61 x62) = False;
equal_msg (Public_key_encrypt x61 x62) (Var x2) = False;
equal_msg (Var x2) (Sym_encrypt x51 x52) = False;
equal_msg (Sym_encrypt x51 x52) (Var x2) = False;
equal_msg (Var x2) (Pair x41 x42) = False;
equal_msg (Pair x41 x42) (Var x2) = False;
equal_msg (Var x2) (Hash x3) = False;
equal_msg (Hash x3) (Var x2) = False;
equal_msg (Cons x1) (Signature x71 x72) = False;
equal_msg (Signature x71 x72) (Cons x1) = False;
equal_msg (Cons x1) (Public_key_encrypt x61 x62) = False;
equal_msg (Public_key_encrypt x61 x62) (Cons x1) = False;
equal_msg (Cons x1) (Sym_encrypt x51 x52) = False;
equal_msg (Sym_encrypt x51 x52) (Cons x1) = False;
equal_msg (Cons x1) (Pair x41 x42) = False;
equal_msg (Pair x41 x42) (Cons x1) = False;
equal_msg (Cons x1) (Hash x3) = False;
equal_msg (Hash x3) (Cons x1) = False;
equal_msg (Cons x1) (Var x2) = False;
equal_msg (Var x2) (Cons x1) = False;
equal_msg (Signature x71 x72) (Signature y71 y72) =
  equal_msg x71 y71 && equal_msg x72 y72;
equal_msg (Public_key_encrypt x61 x62) (Public_key_encrypt y61 y62) =
  equal_msg x61 y61 && equal_msg x62 y62;
equal_msg (Sym_encrypt x51 x52) (Sym_encrypt y51 y52) =
  equal_msg x51 y51 && equal_msg x52 y52;
equal_msg (Pair x41 x42) (Pair y41 y42) =
  equal_msg x41 y41 && equal_msg x42 y42;
equal_msg (Hash x3) (Hash y3) = equal_msg x3 y3;
equal_msg (Var x2) (Var y2) = x2 == y2;
equal_msg (Cons x1) (Cons y1) = x1 == y1;

instance Eq Msg where {
  a == b = equal_msg a b;
};

data Term a b = Vara b | Fun a [Term a b];

instance (Eq a, Eq b) => Eq (Term a b) where {
  a == b = equal_term a b;
};

equal_term :: forall a b. (Eq a, Eq b) => Term a b -> Term a b -> Bool;
equal_term (Vara x1) (Fun x21 x22) = False;
equal_term (Fun x21 x22) (Vara x1) = False;
equal_term (Fun x21 x22) (Fun y21 y22) = x21 == y21 && x22 == y22;
equal_term (Vara x1) (Vara y1) = x1 == y1;

data Symbol = SCons [Char] | SHash | SPair | SSym_encrypt | SPublic_key_encrypt
  | SSignature;

equal_symbol :: Symbol -> Symbol -> Bool;
equal_symbol SPublic_key_encrypt SSignature = False;
equal_symbol SSignature SPublic_key_encrypt = False;
equal_symbol SSym_encrypt SSignature = False;
equal_symbol SSignature SSym_encrypt = False;
equal_symbol SSym_encrypt SPublic_key_encrypt = False;
equal_symbol SPublic_key_encrypt SSym_encrypt = False;
equal_symbol SPair SSignature = False;
equal_symbol SSignature SPair = False;
equal_symbol SPair SPublic_key_encrypt = False;
equal_symbol SPublic_key_encrypt SPair = False;
equal_symbol SPair SSym_encrypt = False;
equal_symbol SSym_encrypt SPair = False;
equal_symbol SHash SSignature = False;
equal_symbol SSignature SHash = False;
equal_symbol SHash SPublic_key_encrypt = False;
equal_symbol SPublic_key_encrypt SHash = False;
equal_symbol SHash SSym_encrypt = False;
equal_symbol SSym_encrypt SHash = False;
equal_symbol SHash SPair = False;
equal_symbol SPair SHash = False;
equal_symbol (SCons x1) SSignature = False;
equal_symbol SSignature (SCons x1) = False;
equal_symbol (SCons x1) SPublic_key_encrypt = False;
equal_symbol SPublic_key_encrypt (SCons x1) = False;
equal_symbol (SCons x1) SSym_encrypt = False;
equal_symbol SSym_encrypt (SCons x1) = False;
equal_symbol (SCons x1) SPair = False;
equal_symbol SPair (SCons x1) = False;
equal_symbol (SCons x1) SHash = False;
equal_symbol SHash (SCons x1) = False;
equal_symbol (SCons x1) (SCons y1) = x1 == y1;
equal_symbol SSignature SSignature = True;
equal_symbol SPublic_key_encrypt SPublic_key_encrypt = True;
equal_symbol SSym_encrypt SSym_encrypt = True;
equal_symbol SPair SPair = True;
equal_symbol SHash SHash = True;

instance Eq Symbol where {
  a == b = equal_symbol a b;
};

data Num = One | Bit0 Num | Bit1 Num;

one_integer :: Integer;
one_integer = (1 :: Integer);

class One a where {
  one :: a;
};

instance One Integer where {
  one = one_integer;
};

class Zero a where {
  zero :: a;
};

instance Zero Integer where {
  zero = (0 :: Integer);
};

class (One a, Zero a) => Zero_neq_one a where {
};

instance Zero_neq_one Integer where {
};

data Nat = Zero_nat | Suc Nat;

data Set a = Set [a] | Coset [a];

data Constraint = Constraint [Msg] [Msg] Msg;

membera :: forall a. (Eq a) => [a] -> a -> Bool;
membera [] y = False;
membera (x : xs) y = x == y || membera xs y;

member :: forall a. (Eq a) => a -> Set a -> Bool;
member x (Coset xs) = not (membera xs x);
member x (Set xs) = membera xs x;

removeAll :: forall a. (Eq a) => a -> [a] -> [a];
removeAll x [] = [];
removeAll x (y : xs) = (if x == y then removeAll x xs else y : removeAll x xs);

inserta :: forall a. (Eq a) => a -> [a] -> [a];
inserta x xs = (if membera xs x then xs else x : xs);

insert :: forall a. (Eq a) => a -> Set a -> Set a;
insert x (Coset xs) = Coset (removeAll x xs);
insert x (Set xs) = Set (inserta x xs);

fold :: forall a b. (a -> b -> b) -> [a] -> b -> b;
fold f (x : xs) s = fold f xs (f x s);
fold f [] s = s;

sup_set :: forall a. (Eq a) => Set a -> Set a -> Set a;
sup_set (Coset xs) a = Coset (filter (\ x -> not (member x a)) xs);
sup_set (Set xs) a = fold insert xs a;

bot_set :: forall a. Set a;
bot_set = Set [];

sup_seta :: forall a. (Eq a) => Set (Set a) -> Set a;
sup_seta (Set xs) = fold sup_set xs bot_set;

image :: forall a b. (a -> b) -> Set a -> Set b;
image f (Set xs) = Set (map f xs);

fv :: forall a b. (Eq b) => Term a b -> Set b;
fv (Vara x) = insert x bot_set;
fv (Fun f l) = sup_seta (image fv (Set l));

foldl :: forall a b. (a -> b -> a) -> a -> [b] -> a;
foldl f a [] = a;
foldl f a (x : xs) = foldl f (f a x) xs;

embed :: Msg -> Term Symbol [Char];
embed (Cons s) = Fun (SCons s) [];
embed (Var s) = Vara s;
embed (Hash m) = Fun SHash [embed m];
embed (Pair m1 m2) = Fun SPair [embed m1, embed m2];
embed (Sym_encrypt m1 m2) = Fun SSym_encrypt [embed m1, embed m2];
embed (Public_key_encrypt m1 m2) = Fun SPublic_key_encrypt [embed m1, embed m2];
embed (Signature m1 m2) = Fun SSignature [embed m1, embed m2];

fun_upd :: forall a b. (Eq a) => (a -> b) -> a -> b -> a -> b;
fun_upd f a b = (\ x -> (if x == a then b else f x));

sapply :: forall a b. (a -> Term b a) -> Term b a -> Term b a;
sapply s (Fun f l) = Fun f (map (sapply s) l);
sapply s (Vara x) = s x;

scomp :: forall a b. (a -> Term b a) -> (a -> Term b a) -> a -> Term b a;
scomp sigma tau = (\ x -> sapply sigma (tau x));

gen_length :: forall a. Nat -> [a] -> Nat;
gen_length n (x : xs) = gen_length (Suc n) xs;
gen_length n [] = n;

size_list :: forall a. [a] -> Nat;
size_list = gen_length Zero_nat;

equal_nat :: Nat -> Nat -> Bool;
equal_nat Zero_nat (Suc x2) = False;
equal_nat (Suc x2) Zero_nat = False;
equal_nat (Suc x2) (Suc y2) = equal_nat x2 y2;
equal_nat Zero_nat Zero_nat = True;

sapply_eq ::
  forall a b. (a -> Term b a) -> (Term b a, Term b a) -> (Term b a, Term b a);
sapply_eq sigma eq = (sapply sigma (fst eq), sapply sigma (snd eq));

sapply_eq_system ::
  forall a b.
    (a -> Term b a) -> [(Term b a, Term b a)] -> [(Term b a, Term b a)];
sapply_eq_system sigma l = map (sapply_eq sigma) l;

lifted_comp ::
  forall a b. Maybe (a -> Term b a) -> (a -> Term b a) -> Maybe (a -> Term b a);
lifted_comp Nothing tau = Nothing;
lifted_comp (Just sigma) tau = Just (scomp sigma tau);

unify ::
  forall a b. (Eq a, Eq b) => [(Term a b, Term a b)] -> Maybe (b -> Term a b);
unify [] = Just Vara;
unify ((Vara x, t) : u) =
  (if not (member x (fv t))
    then lifted_comp (unify (sapply_eq_system (fun_upd Vara x t) u))
           (fun_upd Vara x t)
    else (if equal_term (Vara x) t then unify u else Nothing));
unify ((Fun v va, Vara y) : u) = unify ((Vara y, Fun v va) : u);
unify ((Fun f ua, Fun g v) : u) =
  (if f == g && equal_nat (size_list ua) (size_list v)
    then unify (zip ua v ++ u) else Nothing);

m_sapply :: ([Char] -> Msg) -> Msg -> Msg;
m_sapply sigma (Cons s) = Cons s;
m_sapply sigma (Var s) = sigma s;
m_sapply sigma (Hash m) = Hash (m_sapply sigma m);
m_sapply sigma (Pair m1 m2) = Pair (m_sapply sigma m1) (m_sapply sigma m2);
m_sapply sigma (Sym_encrypt m1 m2) =
  Sym_encrypt (m_sapply sigma m1) (m_sapply sigma m2);
m_sapply sigma (Public_key_encrypt m1 m2) =
  Public_key_encrypt (m_sapply sigma m1) (m_sapply sigma m2);
m_sapply sigma (Signature m1 m2) =
  Signature (m_sapply sigma m1) (m_sapply sigma m2);

m_scomp :: ([Char] -> Msg) -> ([Char] -> Msg) -> [Char] -> Msg;
m_scomp sigma tau = (\ x -> m_sapply sigma (tau x));

msg_of_term :: Term Symbol [Char] -> Msg;
msg_of_term (Vara s) = Var s;
msg_of_term (Fun (SCons s) []) = Cons s;
msg_of_term (Fun SHash [t]) = Hash (msg_of_term t);
msg_of_term (Fun SPair [t1, t2]) = Pair (msg_of_term t1) (msg_of_term t2);
msg_of_term (Fun SSym_encrypt [t1, t2]) =
  Sym_encrypt (msg_of_term t1) (msg_of_term t2);
msg_of_term (Fun SPublic_key_encrypt [t1, t2]) =
  Public_key_encrypt (msg_of_term t1) (msg_of_term t2);
msg_of_term (Fun SSignature [t1, t2]) =
  Signature (msg_of_term t1) (msg_of_term t2);
msg_of_term (Fun SHash []) = error "undefined";
msg_of_term (Fun SHash (v : vc : vd)) = error "undefined";
msg_of_term (Fun SPair []) = error "undefined";
msg_of_term (Fun SPair [v]) = error "undefined";
msg_of_term (Fun SPair (v : vc : ve : vf)) = error "undefined";
msg_of_term (Fun SSym_encrypt []) = error "undefined";
msg_of_term (Fun SSym_encrypt [v]) = error "undefined";
msg_of_term (Fun SSym_encrypt (v : vc : ve : vf)) = error "undefined";
msg_of_term (Fun SPublic_key_encrypt []) = error "undefined";
msg_of_term (Fun SPublic_key_encrypt [v]) = error "undefined";
msg_of_term (Fun SPublic_key_encrypt (v : vc : ve : vf)) = error "undefined";
msg_of_term (Fun SSignature []) = error "undefined";
msg_of_term (Fun SSignature [v]) = error "undefined";
msg_of_term (Fun SSignature (v : vc : ve : vf)) = error "undefined";
msg_of_term (Fun (SCons va) (vb : vc)) = error "undefined";
msg_of_term (Fun v (vb : va : vc : ve)) = error "undefined";

lift_subst :: Maybe ([Char] -> Term Symbol [Char]) -> Maybe ([Char] -> Msg);
lift_subst Nothing = Nothing;
lift_subst (Just sigma) = Just (msg_of_term . sigma);

embed_eq :: (Msg, Msg) -> (Term Symbol [Char], Term Symbol [Char]);
embed_eq (m1, m2) = (embed m1, embed m2);

embed_eqs :: [(Msg, Msg)] -> [(Term Symbol [Char], Term Symbol [Char])];
embed_eqs [] = [];
embed_eqs (eq : u) = embed_eq eq : embed_eqs u;

m_unify :: [(Msg, Msg)] -> Maybe ([Char] -> Msg);
m_unify u = lift_subst (unify (embed_eqs u));

iota :: [Char];
iota =
  [Char True False False True False True True False,
    Char False True True True False True True False,
    Char False False True False True True True False,
    Char False True False False True True True False,
    Char True False True False True True True False,
    Char False False True False False True True False,
    Char True False True False False True True False,
    Char False True False False True True True False];

intruder :: Msg;
intruder = Cons iota;

ktp :: [Constraint];
ktp = [Constraint
         [Cons [Char True False False False False True True False],
           Cons [Char False True False False False True True False], intruder]
         [] (Pair (Var [Char True False False False False False True False,
                         Char False False False False True True False False])
              (Var [Char False True False False False False True False,
                     Char False False False False True True False False])),
        Constraint
          [Public_key_encrypt
             (Pair (Cons [Char True True False True False True True False,
                           Char False False False False True True False False])
               (Signature
                 (Cons [Char True True False True False True True False,
                         Char False False False False True True False False])
                 (Var [Char True False False False False False True False,
                        Char False False False False True True False False])))
             (Var [Char False True False False False False True False,
                    Char False False False False True True False False]),
            Cons [Char True False False False False True True False],
            Cons [Char False True False False False True True False], intruder]
          [] (Public_key_encrypt
               (Pair (Var [Char True True False True False False True False,
                            Char True False False False True True False False])
                 (Signature
                   (Var [Char True True False True False False True False,
                          Char True False False False True True False False])
                   (Cons [Char True False False False False True True False])))
               (Cons [Char False True False False False True True False])),
        Constraint
          [Sym_encrypt
             (Cons [Char True False True True False True True False,
                     Char True False False False True True False False])
             (Var [Char True True False True False False True False,
                    Char True False False False True True False False]),
            Public_key_encrypt
              (Pair (Cons [Char True True False True False True True False,
                            Char False False False False True True False False])
                (Signature
                  (Cons [Char True True False True False True True False,
                          Char False False False False True True False False])
                  (Var [Char True False False False False False True False,
                         Char False False False False True True False False])))
              (Var [Char False True False False False False True False,
                     Char False False False False True True False False]),
            Cons [Char True False False False False True True False],
            Cons [Char False True False False False True True False], intruder]
          [] (Sym_encrypt
               (Var [Char False True False True True False True False,
                      Char False False False False True True False False])
               (Cons [Char True True False True False True True False,
                       Char False False False False True True False False])),
        Constraint
          [Sym_encrypt
             (Cons [Char True False True True False True True False,
                     Char True False False False True True False False])
             (Var [Char True True False True False False True False,
                    Char True False False False True True False False]),
            Public_key_encrypt
              (Pair (Cons [Char True True False True False True True False,
                            Char False False False False True True False False])
                (Signature
                  (Cons [Char True True False True False True True False,
                          Char False False False False True True False False])
                  (Var [Char True False False False False False True False,
                         Char False False False False True True False False])))
              (Var [Char False True False False False False True False,
                     Char False False False False True True False False]),
            Cons [Char True False False False False True True False],
            Cons [Char False True False False False True True False], intruder]
          [] (Pair (Var [Char True True False True False False True False,
                          Char True False False False True True False False])
               (Cons [Char True False True True False True True False,
                       Char True False False False True True False False]))];

nspk :: [Constraint];
nspk =
  [Constraint
     [Cons [Char True False False False False True True False],
       Cons [Char False True False False False True True False], intruder]
     [] (Pair (Var [Char True False False False False False True False,
                     Char False False False False True True False False])
          (Var [Char False True False False False False True False,
                 Char False False False False True True False False])),
    Constraint
      [Public_key_encrypt
         (Pair (Cons [Char False True True True False True True False,
                       Char True False False False False True True False,
                       Char False False False False True True False False])
           (Var [Char True False False False False False True False,
                  Char False False False False True True False False]))
         (Var [Char False True False False False False True False,
                Char False False False False True True False False]),
        Cons [Char True False False False False True True False],
        Cons [Char False True False False False True True False], intruder]
      [] (Public_key_encrypt
           (Pair (Var [Char False True True True False False True False,
                        Char True False False False False False True False,
                        Char True False False False True True False False])
             (Cons [Char True False False False False True True False]))
           (Cons [Char False True False False False True True False])),
    Constraint
      [Public_key_encrypt
         (Pair (Var [Char False True True True False False True False,
                      Char True False False False False False True False,
                      Char True False False False True True False False])
           (Cons [Char False True True True False True True False,
                   Char False True False False False True True False,
                   Char True False False False True True False False]))
         (Cons [Char True False False False False True True False]),
        Public_key_encrypt
          (Pair (Cons [Char False True True True False True True False,
                        Char True False False False False True True False,
                        Char False False False False True True False False])
            (Var [Char True False False False False False True False,
                   Char False False False False True True False False]))
          (Var [Char False True False False False False True False,
                 Char False False False False True True False False]),
        Cons [Char True False False False False True True False],
        Cons [Char False True False False False True True False], intruder]
      [] (Public_key_encrypt
           (Pair (Cons [Char False True True True False True True False,
                         Char True False False False False True True False,
                         Char False False False False True True False False])
             (Var [Char False True True True False False True False,
                    Char False True False False False False True False,
                    Char False False False False True True False False]))
           (Var [Char True False False False False False True False,
                  Char False False False False True True False False])),
    Constraint
      [Public_key_encrypt
         (Var [Char False True True True False False True False,
                Char False True False False False False True False,
                Char False False False False True True False False])
         (Var [Char False True False False False False True False,
                Char False False False False True True False False]),
        Public_key_encrypt
          (Pair (Var [Char False True True True False False True False,
                       Char True False False False False False True False,
                       Char True False False False True True False False])
            (Cons [Char False True True True False True True False,
                    Char False True False False False True True False,
                    Char True False False False True True False False]))
          (Cons [Char True False False False False True True False]),
        Public_key_encrypt
          (Pair (Cons [Char False True True True False True True False,
                        Char True False False False False True True False,
                        Char False False False False True True False False])
            (Var [Char True False False False False False True False,
                   Char False False False False True True False False]))
          (Var [Char False True False False False False True False,
                 Char False False False False True True False False]),
        Cons [Char True False False False False True True False],
        Cons [Char False True False False False True True False], intruder]
      [] (Public_key_encrypt
           (Cons [Char False True True True False True True False,
                   Char False True False False False True True False,
                   Char True False False False True True False False])
           (Cons [Char False True False False False True True False])),
    Constraint
      [Public_key_encrypt
         (Var [Char False True True True False False True False,
                Char False True False False False False True False,
                Char False False False False True True False False])
         (Var [Char False True False False False False True False,
                Char False False False False True True False False]),
        Public_key_encrypt
          (Pair (Var [Char False True True True False False True False,
                       Char True False False False False False True False,
                       Char True False False False True True False False])
            (Cons [Char False True True True False True True False,
                    Char False True False False False True True False,
                    Char True False False False True True False False]))
          (Cons [Char True False False False False True True False]),
        Public_key_encrypt
          (Pair (Cons [Char False True True True False True True False,
                        Char True False False False False True True False,
                        Char False False False False True True False False])
            (Var [Char True False False False False False True False,
                   Char False False False False True True False False]))
          (Var [Char False True False False False False True False,
                 Char False False False False True True False False]),
        Cons [Char True False False False False True True False],
        Cons [Char False True False False False True True False], intruder]
      [] (Pair (Var [Char False True True True False False True False,
                      Char True False False False False False True False,
                      Char True False False False True True False False])
           (Cons [Char False True True True False True True False,
                   Char False True False False False True True False,
                   Char True False False False True True False False]))];

fold_option :: forall a b. (a -> Maybe b) -> [a] -> Maybe b;
fold_option f [] = Nothing;
fold_option f (a : asa) = (case f a of {
                            Nothing -> fold_option f asa;
                            Just aa -> Just aa;
                          });

post :: forall a. [Maybe a] -> Maybe a;
post = fold_option id;

of_bool :: forall a. (Zero_neq_one a) => Bool -> a;
of_bool True = one;
of_bool False = zero;

integer_of_char :: Char -> Integer;
integer_of_char (Char b0 b1 b2 b3 b4 b5 b6 b7) =
  ((((((of_bool b7 * (2 :: Integer) + of_bool b6) * (2 :: Integer) +
        of_bool b5) *
        (2 :: Integer) +
       of_bool b4) *
       (2 :: Integer) +
      of_bool b3) *
      (2 :: Integer) +
     of_bool b2) *
     (2 :: Integer) +
    of_bool b1) *
    (2 :: Integer) +
    of_bool b0;

implode :: [Char] -> String;
implode cs =
  map (let chr k | (0 <= k && k < 128) = Prelude.toEnum k :: Prelude.Char in chr . Prelude.fromInteger)
    (map integer_of_char cs);

c_sapply :: ([Char] -> Msg) -> Constraint -> Constraint;
c_sapply sigma (Constraint msa ms msg) =
  Constraint (map (m_sapply sigma) msa) (map (m_sapply sigma) ms)
    (m_sapply sigma msg);

c_dec_term :: Constraint -> Msg -> [([Constraint], [Char] -> Msg)];
c_dec_term (Constraint m a t) (Pair u v) =
  let {
    ma = removeAll (Pair u v) m;
  } in [([Constraint (u : v : ma) (Pair u v : a) t], Var)];
c_dec_term (Constraint m a t) (Sym_encrypt u k) =
  let {
    ma = removeAll (Sym_encrypt u k) m;
  } in [([Constraint (u : ma) (Sym_encrypt u k : a) t,
           Constraint ma (Sym_encrypt u k : a) k],
          Var)];
c_dec_term (Constraint m a t) (Public_key_encrypt u (Cons i)) =
  (if i == iota
    then let {
           ma = removeAll (Public_key_encrypt u intruder) m;
         } in [([Constraint (u : ma) (Public_key_encrypt u intruder : a) t],
                 Var)]
    else []);
c_dec_term (Constraint m a t) (Public_key_encrypt u (Var x)) =
  let {
    sigma = fun_upd Var x intruder;
  } in [([c_sapply sigma (Constraint m a t)], sigma)];
c_dec_term (Constraint m a t) (Cons v) = [];
c_dec_term (Constraint m a t) (Var v) = [];
c_dec_term (Constraint m a t) (Hash v) = [];
c_dec_term (Constraint m a t) (Public_key_encrypt v (Hash vb)) = [];
c_dec_term (Constraint m a t) (Public_key_encrypt v (Pair vb vc)) = [];
c_dec_term (Constraint m a t) (Public_key_encrypt v (Sym_encrypt vb vc)) = [];
c_dec_term (Constraint m a t) (Public_key_encrypt v (Public_key_encrypt vb vc))
  = [];
c_dec_term (Constraint m a t) (Public_key_encrypt v (Signature vb vc)) = [];
c_dec_term (Constraint m a t) (Signature v va) = [];

c_dec :: Constraint -> [([Constraint], [Char] -> Msg)];
c_dec (Constraint m a t) = concatMap (c_dec_term (Constraint m a t)) m;

c_comp :: Constraint -> [([Constraint], [Char] -> Msg)];
c_comp (Constraint m a (Hash t)) = [([Constraint m a t], Var)];
c_comp (Constraint m a (Pair t1 t2)) =
  [([Constraint m a t1, Constraint m a t2], Var)];
c_comp (Constraint ma a (Sym_encrypt m k)) =
  [([Constraint ma a m, Constraint ma a k], Var)];
c_comp (Constraint ma a (Public_key_encrypt m k)) =
  [([Constraint ma a m, Constraint ma a k], Var)];
c_comp (Constraint m a (Signature t (Cons i))) =
  (if i == iota then [([Constraint m a t], Var)] else []);
c_comp (Constraint m a (Cons v)) = [];
c_comp (Constraint m a (Var v)) = [];
c_comp (Constraint m a (Signature v (Var vb))) = [];
c_comp (Constraint m a (Signature v (Hash vb))) = [];
c_comp (Constraint m a (Signature v (Pair vb vc))) = [];
c_comp (Constraint m a (Signature v (Sym_encrypt vb vc))) = [];
c_comp (Constraint m a (Signature v (Public_key_encrypt vb vc))) = [];
c_comp (Constraint m a (Signature v (Signature vb vc))) = [];

c_unify :: Constraint -> [([Constraint], [Char] -> Msg)];
c_unify (Constraint m a (Var uu)) = [];
c_unify (Constraint m a (Cons v)) =
  concatMap (\ u -> (case m_unify [(Cons v, u)] of {
                      Nothing -> [];
                      Just sigma -> [([], sigma)];
                    }))
    (m ++ a);
c_unify (Constraint m a (Hash v)) =
  concatMap (\ u -> (case m_unify [(Hash v, u)] of {
                      Nothing -> [];
                      Just sigma -> [([], sigma)];
                    }))
    (m ++ a);
c_unify (Constraint m a (Pair v va)) =
  concatMap (\ u -> (case m_unify [(Pair v va, u)] of {
                      Nothing -> [];
                      Just sigma -> [([], sigma)];
                    }))
    (m ++ a);
c_unify (Constraint m a (Sym_encrypt v va)) =
  concatMap (\ u -> (case m_unify [(Sym_encrypt v va, u)] of {
                      Nothing -> [];
                      Just sigma -> [([], sigma)];
                    }))
    (m ++ a);
c_unify (Constraint m a (Public_key_encrypt v va)) =
  concatMap (\ u -> (case m_unify [(Public_key_encrypt v va, u)] of {
                      Nothing -> [];
                      Just sigma -> [([], sigma)];
                    }))
    (m ++ a);
c_unify (Constraint m a (Signature v va)) =
  concatMap (\ u -> (case m_unify [(Signature v va, u)] of {
                      Nothing -> [];
                      Just sigma -> [([], sigma)];
                    }))
    (m ++ a);

c_succ :: Constraint -> [([Constraint], [Char] -> Msg)];
c_succ c = c_unify c ++ c_comp c ++ c_dec c;

c_simple :: Constraint -> Bool;
c_simple (Constraint m a (Var uu)) = True;
c_simple (Constraint v va (Cons vc)) = False;
c_simple (Constraint v va (Hash vc)) = False;
c_simple (Constraint v va (Pair vc vd)) = False;
c_simple (Constraint v va (Sym_encrypt vc vd)) = False;
c_simple (Constraint v va (Public_key_encrypt vc vd)) = False;
c_simple (Constraint v va (Signature vc vd)) = False;

cs_simple :: [Constraint] -> Bool;
cs_simple cs = all c_simple cs;

cs_sapply :: ([Char] -> Msg) -> [Constraint] -> [Constraint];
cs_sapply sigma cs = map (c_sapply sigma) cs;

cs_succ_aux :: [Constraint] -> [Constraint] -> [([Constraint], [Char] -> Msg)];
cs_succ_aux uu [] = [];
cs_succ_aux csa (c : cs) =
  map (\ (csb, sigma) ->
        (cs_sapply sigma csa ++ csb ++ cs_sapply sigma cs, sigma))
    (c_succ c) ++
    cs_succ_aux (csa ++ [c]) cs;

cs_succ :: [Constraint] -> [([Constraint], [Char] -> Msg)];
cs_succ cs = cs_succ_aux [] cs;

search :: [Constraint] -> Maybe ([Constraint], [Char] -> Msg);
search ics =
  (if cs_simple ics then Just (ics, Var)
    else fold_option
           (\ (cs, sigma) ->
             (case search cs of {
               Nothing -> Nothing;
               Just (csa, sigmaa) -> Just (csa, m_scomp sigmaa sigma);
             }))
           (cs_succ ics));

print_list :: forall a. (a -> [Char]) -> [a] -> [Char];
print_list f m =
  [Char True True False True True False True False] ++
    foldl (\ out ma ->
            out ++
              (if null out then []
                else [Char False False True True False True False False,
                       Char False False False False False True False False]) ++
                f ma)
      [] m ++
      [Char True False True True True False True False];

print_msg :: Msg -> [Char];
print_msg (Cons s) =
  [Char False False False True False True False False,
    Char True True False False False False True False,
    Char True True True True False True True False,
    Char False True True True False True True False,
    Char True True False False True True True False,
    Char False False False False False True False False] ++
    s ++ [Char True False False True False True False False];
print_msg (Var s) =
  [Char False False False True False True False False,
    Char False True True False True False True False,
    Char True False False False False True True False,
    Char False True False False True True True False,
    Char False False False False False True False False] ++
    s ++ [Char True False False True False True False False];
print_msg (Hash m) =
  [Char False False False True False True False False,
    Char False False False True False False True False,
    Char True False False False False True True False,
    Char True True False False True True True False,
    Char False False False True False True True False,
    Char False False False False False True False False] ++
    print_msg m ++ [Char True False False True False True False False];
print_msg (Pair u v) =
  [Char False False False True False True False False,
    Char False False False False True False True False,
    Char True False False False False True True False,
    Char True False False True False True True False,
    Char False True False False True True True False,
    Char False False False False False True False False] ++
    print_msg u ++
      [Char False False False False False True False False] ++
        print_msg v ++ [Char True False False True False True False False];
print_msg (Sym_encrypt m k) =
  [Char False False False True False True False False,
    Char True True False False True False True False,
    Char True False False True True True True False,
    Char True False True True False True True False,
    Char True True True True True False True False,
    Char True False True False False True True False,
    Char False True True True False True True False,
    Char True True False False False True True False,
    Char False True False False True True True False,
    Char True False False True True True True False,
    Char False False False False True True True False,
    Char False False True False True True True False,
    Char False False False False False True False False] ++
    print_msg m ++
      [Char False False False False False True False False] ++
        print_msg k ++ [Char True False False True False True False False];
print_msg (Public_key_encrypt m k) =
  [Char False False False True False True False False,
    Char False False False False True False True False,
    Char True False True False True True True False,
    Char False True False False False True True False,
    Char False False True True False True True False,
    Char True False False True False True True False,
    Char True True False False False True True False,
    Char True True True True True False True False,
    Char True True False True False True True False,
    Char True False True False False True True False,
    Char True False False True True True True False,
    Char True True True True True False True False,
    Char True False True False False True True False,
    Char False True True True False True True False,
    Char True True False False False True True False,
    Char False True False False True True True False,
    Char True False False True True True True False,
    Char False False False False True True True False,
    Char False False True False True True True False,
    Char False False False False False True False False] ++
    print_msg m ++
      [Char False False False False False True False False] ++
        print_msg k ++ [Char True False False True False True False False];
print_msg (Signature m k) =
  [Char False False False True False True False False,
    Char True True False False True False True False,
    Char True False False True False True True False,
    Char True True True False False True True False,
    Char False True True True False True True False,
    Char True False False False False True True False,
    Char False False True False True True True False,
    Char True False True False True True True False,
    Char False True False False True True True False,
    Char True False True False False True True False,
    Char False False False False False True False False] ++
    print_msg m ++
      [Char False False False False False True False False] ++
        print_msg k ++ [Char True False False True False True False False];

print_c :: Constraint -> [Char];
print_c (Constraint m a t) =
  [Char False False False True False True False False] ++
    print_list print_msg m ++
      [Char False False False False False True False False,
        Char False False True True True True True False,
        Char False False False False False True False False] ++
        print_list print_msg a ++
          [Char False False False False False True False False,
            Char True False True True False True False False,
            Char True False True True False True False False,
            Char False True True True True True False False,
            Char False False False False False True False False] ++
            print_msg t ++ [Char True False False True False True False False];

ktp_vars :: [[Char]];
ktp_vars =
  [[Char True False False False False False True False,
     Char False False False False True True False False],
    [Char False True False False False False True False,
      Char False False False False True True False False],
    [Char True True False True False False True False,
      Char True False False False True True False False],
    [Char False True False True True False True False,
      Char False False False False True True False False]];

nspk_vars :: [[Char]];
nspk_vars =
  [[Char True False False False False False True False,
     Char False False False False True True False False],
    [Char False True False False False False True False,
      Char False False False False True True False False],
    [Char False True True True False False True False,
      Char True False False False False False True False,
      Char True False False False True True False False],
    [Char False True True True False False True False,
      Char False True False False False False True False,
      Char False False False False True True False False]];

search_slow :: [Constraint] -> Maybe ([Constraint], [Char] -> Msg);
search_slow ics =
  (if cs_simple ics then Just (ics, Var)
    else post (map (\ (cs, sigma) ->
                     (case search_slow cs of {
                       Nothing -> Nothing;
                       Just (csa, sigmaa) -> Just (csa, m_scomp sigmaa sigma);
                     }))
                (cs_succ ics)));

print_search_result :: Maybe ([Constraint], [([Char], Msg)]) -> [Char];
print_search_result Nothing =
  [Char False True True True False False True False,
    Char True True True True False True True False,
    Char False False False False False True False False,
    Char True True False False True True True False,
    Char True True True True False True True False,
    Char False False True True False True True False,
    Char True False True False True True True False,
    Char False False True False True True True False,
    Char True False False True False True True False,
    Char True True True True False True True False,
    Char False True True True False True True False,
    Char False True True True False True False False];
print_search_result (Just (cs, sigma)) =
  [Char True True False False True False True False,
    Char True False False True False True True False,
    Char True False True True False True True False,
    Char False False False False True True True False,
    Char False False True True False True True False,
    Char True False True False False True True False,
    Char False False False False False True False False,
    Char True True False False False True True False,
    Char True True True True False True True False,
    Char False True True True False True True False,
    Char True True False False True True True False,
    Char False False True False True True True False,
    Char False True False False True True True False,
    Char True False False False False True True False,
    Char True False False True False True True False,
    Char False True True True False True True False,
    Char False False True False True True True False,
    Char True True False False True True True False,
    Char False True False True True True False False,
    Char False False False False False True False False] ++
    print_list print_c cs ++
      [Char True True False True True True False False,
        Char False False False False False True False False,
        Char True True False False True False True False,
        Char True False True False True True True False,
        Char False True False False False True True False,
        Char True True False False True True True False,
        Char False False True False True True True False,
        Char True False False True False True True False,
        Char False False True False True True True False,
        Char True False True False True True True False,
        Char False False True False True True True False,
        Char True False False True False True True False,
        Char True True True True False True True False,
        Char False True True True False True True False,
        Char True True False False True True True False,
        Char False True False True True True False False,
        Char False False False False False True False False] ++
        print_list
          (\ (s, m) ->
            [Char False False False True False True False False] ++
              s ++ [Char False False False False False True False False,
                     Char True False True True False True False False,
                     Char True False True True False True False False,
                     Char False True True True True True False False,
                     Char False False False False False True False False] ++
                     print_msg m ++
                       [Char True False False True False True False False])
          sigma;

map_option :: forall a b. (a -> b) -> Maybe a -> Maybe b;
map_option f Nothing = Nothing;
map_option f (Just x2) = Just (f x2);

print_search :: [[Char]] -> [Constraint] -> String;
print_search ns cs =
  implode
    (print_search_result
      (map_option (\ (csa, sigma) -> (csa, map (\ v -> (v, sigma v)) ns))
        (search cs)));

print_search_KTP :: String;
print_search_KTP = print_search ktp_vars ktp;

print_search_NSPK :: String;
print_search_NSPK = print_search nspk_vars nspk;

print_search_slow :: [[Char]] -> [Constraint] -> String;
print_search_slow ns cs =
  implode
    (print_search_result
      (map_option (\ (csa, sigma) -> (csa, map (\ v -> (v, sigma v)) ns))
        (search_slow cs)));

print_search_slow_KTP :: String;
print_search_slow_KTP = print_search_slow ktp_vars ktp;

print_search_slow_NSPK :: String;
print_search_slow_NSPK = print_search_slow nspk_vars nspk;

}
