module NGram

data Trie k v = Empty | Leaf v | Branch (List (k, Trie k v))

-- for lens
instance Functor (const a) where map = const id

subtrie : Eq kt => kt -> (f:Type -> Type) -> Functor f -> 
          (Trie kt vt -> f (Trie kt vt)) -> Trie kt vt -> f (Trie kt vt)
subtrie {kt} {vt} key f inst mod (Branch xs) = map Branch (look xs)
  where look : List (kt, Trie kt vt) -> f (List (kt, Trie kt vt))
        look [] = map (\x => [(key, x)]) (mod Empty)
        look ((k, sub) :: entries) with (key == k)
          | True = map (\x => (k, x) :: entries) (mod sub)
          | False = map ((k, sub) ::) (look entries)
subtrie key f inst mod _ = map (\x => Branch [(key, x)]) (mod Empty)

path : Eq kt => List kt -> (f : Type -> Type) -> Functor f ->
       (Trie kt vt -> f (Trie kt vt)) -> Trie kt vt -> f (Trie kt vt)
path [] f inst mod t = mod t
path (p::ps) f inst mod t = subtrie p f inst (path ps f inst mod) t

subtries : (f:Type -> Type) -> Functor f ->
           (List (kt, Trie kt vt) -> f (List (kt, Trie kt vt))) ->
           Trie kt vt -> f (Trie kt vt)
subtries F inst f (Branch list) = map Branch (f list)
-- this doesn't really obey the lens laws :(
subtries F inst f _ = map Branch (f [])

get : ((f : Type -> Type) -> Functor f -> (a -> f a) -> b -> f b) -> b -> a
get {a} l = l (const a) %instance id

mod : ((f : Type -> Type) -> Functor f -> (a -> f a) -> b -> f b) -> (a -> a) -> b -> b
mod l fun = l id %instance fun
set : ((f : Type -> Type) -> Functor f -> (a -> f a) -> b -> f b) -> a -> b -> b
set l val = mod l (const val)

lookupOne : Eq kt => kt -> Trie kt vt -> Trie kt vt
lookupOne key = get (subtrie key)

stripPrefix : Eq kt => List kt -> Trie kt vt -> Trie kt vt
stripPrefix (p::ps) trie = lookupOne p (stripPrefix ps trie)
stripPrefix [] trie = trie

Frequencies : Nat -> Type -> Type
Frequencies n a = Trie a Nat

emptyFreq : Frequencies n a
emptyFreq = Empty

foundOne : Eq a => Vect n a -> Frequencies n a -> Frequencies n a
foundOne {n} {a} ngram = mod (path (toList ngram)) inc where
  inc : Frequencies n a -> Frequencies n a
  inc (Leaf x) = Leaf (x + 1)
  inc _ = Leaf 1

tryTake : (n:Nat) -> List a -> Maybe (Vect n a)
tryTake Z _ = Just []
tryTake (S n) (x::xs) = Just (x :: !(tryTake n xs))
tryTake _ _ = Nothing

ngrams : Eq a => (n:Nat) -> List a -> Frequencies n a
ngrams n [] = emptyFreq {n}
ngrams n (x::xs) with (tryTake n (x::xs))
  | Nothing = emptyFreq {n}
  | Just ngram = foundOne ngram (ngrams n xs)

probs : Frequencies n a -> Trie a (Nat, Nat)
probs {n} t = rec t 0 where
  rec : Frequencies n a -> Nat -> Trie a (Nat, Nat)
  rec (Leaf freq) acc = Leaf (freq, acc)
  rec Empty _ = Empty
  rec (Branch xs) acc = Branch (map (\(key, x) => (key, rec x leafSum)) xs)
    where count : (b, Trie a Nat) -> Nat
          leafSum : Nat
          leafSum = sum (map count xs)
          count (_, Leaf x) = x
          count _ = 0
