{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}

data T = Leaf String | Node T T deriving Show

class Searchable a where
    log_setup :: String -> a
    move_left :: a
    move_right :: a
    advance :: a -> (a, String) -> (a, String)

search :: Searchable a => Int -> T -> (a, String)
search _ (Leaf s) = (log_setup s, s)
search n (Node t1 t2) = if mod n 2 == 0 then
    advance move_left (search (div n 2) t1) else
    advance move_right (search (div n 2) t2)

instance Searchable String where
    log_setup s = "Trovata la stringa " ++ s
    move_left = "Sinistra. "
    move_right = "Destra. "
    advance move (log, leaf) = (move ++ log, leaf)

instance Searchable Int where
    log_setup _ = 0
    move_left = 1
    move_right = 1
    advance move (log, leaf) = (move + log, leaf)
