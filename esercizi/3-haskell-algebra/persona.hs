{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}

class Persona a k v | v -> k a, k -> a v where
    key :: a -> k
    value :: a -> v
    default1 :: v

search :: (Eq k, Persona a k v) => k -> [a] -> v
search _ [] = default1
search x (c:l) = if key c == x then value c else search x l

instance Persona (Integer,String,String) Integer String where
    key (id, _, _) = id
    value (_, _, cognome) = cognome
    default1 = ""

newtype CodiceFiscale = CF String
newtype Index = I Integer

instance Persona (Index, CodiceFiscale, String, String) Index CodiceFiscale where
    key (id, _, _, _) = id
    value (_, cf, _, _) = cf
    default1 = CF "DOEJHN00A00H000A"

main :: IO ()
main =
    putStrLn (search 4 [(2,"Anna","Rosa"), (4,"Luca","Chiatti"), (5,"Ugo","Rossi")])