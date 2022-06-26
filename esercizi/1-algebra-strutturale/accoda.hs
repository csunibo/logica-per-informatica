{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}

-- 1.2

accoda_brutto :: t1 -> [t2] -> t1 -> (t2 -> t1 -> t1) -> (t1 -> Bool) -> t1
accoda_brutto queue [] _ _ _ = queue
accoda_brutto queue (x:l) empty insert is_full =
    if is_full queue
        then empty
        else accoda_brutto (insert x queue) l empty insert is_full

data List1 = L1 [Int] deriving Show

empty1 = L1 []
size1 (L1 []) = 0
size1 (L1 (x:l)) = 1 + size1 (L1 l)
insert1 x (L1 l) = L1 (x:l)
is_full1 l = len l == 10

accoda1 :: List1 -> [Int] -> List1
accoda1 q l = accoda_brutto q l empty1 insert1 is_full1

data List2 = L2 [Int] Int deriving Show

empty2 = L2 [] 0
size2 (L2 _ s) = s
insert2 x (L2 q s) = L2 (x:q) (s+1)
is_full2 l = size2 l >= 10

accoda2 :: List2 -> [Int] -> List2
accoda2 q l = accoda_brutto q l empty2 insert2 is_full2

-- 1.3

class Queue a b | a -> b where -- a implementa una lista di b
    empty :: a
    len :: a -> Int
    insert :: b -> a -> a
    is_full :: a -> Bool

accoda :: Queue a b => a -> [b] -> a
accoda queue [] = queue
accoda queue (x:l) =
    if is_full queue then empty else accoda (insert x queue) l

instance Queue List1 Int where
    empty = L1 []
    len (L1 []) = 0
    len (L1 (x : l)) = 1 + len (L1 l)
    insert x (L1 l) = L1 (x : l)
    is_full l = len l == 10

-- accoda (L1 [1,2,3]) [4,5,6]

instance Queue List2 Int where
    empty = L2 [] 0
    len (L2 _ s) = s
    insert x (L2 l s) = L2 (x : l) (s + 1)
    is_full x = len x >= 10

-- accoda (L2 [1,2,3] 3) [4,5,6]