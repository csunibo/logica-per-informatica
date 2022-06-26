class Eq a => Ordinato a where
    maggiore :: a -> a -> Bool
-- per ogni x,y (x > y => !(x == y))
-- <= è una relazione transitiva
-- per ogni x,y (not (x > y) /\ y <= x => x == y)


search :: Ordinato a => a -> [a] -> Bool
search _ [] = False
search x (y:l) = if maggiore x y then search x l else x == y

instance Ordinato Int where
    maggiore = (>)