-- | Práctica 1: Introducción a Haskell
-- Profesor: Manuel Soto Romero
-- Ayudante: José Alejandro Pérez Marquez
-- Laboratorio: Erik Rangel Limón
{-# LANGUAGE DeriveGeneric #-}
module Intro where

import Data.Char
import GHC.Generics -- Esto es únicamente para las pruebas
import Data.List


--Funcion auxiliar de "traduceF" 
--revisa si el elemento de la cadena es una vocal para aplicar el lenguaje
--en otro caso deja la letra igual
transformarCaracter :: Char -> String
transformarCaracter c
  | c `elem` "AEIOUaeiou" = c : 'f' : [toLower c]  
  | otherwise = [c]          

--Funcion que recibe un string y lo "traduce" al lenguaje de F's
traduceF :: String -> String
traduceF = concatMap transformarCaracter


--Funcion que recibe dos listas ordenadas y las mezcla ordenadamente
mezcla :: [Int] -> [Int] -> [Int]
mezcla []ys= ys
mezcla xs [] = xs
mezcla (x:xs) (y:ys)
    | x <= y    = x : mezcla xs (y:ys)
    | otherwise = y : mezcla (x:xs) ys  

--Funcion que indica si un String es palindromo
palindromo :: String -> Bool
palindromo palabra | cadena == "" = True
                   | cadena == reverse cadena = True
                   | otherwise = False
                   where cadena = cadenaSinEspacios $ map toLower palabra
                         cadenaSinEspacios = filter (/= ' ')

--Funcion que dada una cadena de Strings, devuelve el prefijo que comparten
prefijoComun :: [String] -> String
prefijoComun [] = ""
prefijoComun (x:xs) = foldl prefijoPal x xs
    where
        prefijoPal acc str = take (length $ takeWhile (uncurry (==)) (zip acc str)) acc

--Funcion que dadas dos listas, devuelve los elementos en los que difieren
diferencia :: (Eq a) => [a]-> [a] -> [a]
diferencia xs ys = filter (\x -> notElem x ys) xs

--Funcion que realiza el producto Punto
--Multiplica las entradas y las suma)
productoPunto :: [Integer] -> [Integer] -> Integer
productoPunto xs ys = sum [x * y | x <- xs, y <- ys]

--Funcion que dado un numero devuelve la triada pitagorica a la que equivalga 
triada :: Int -> [(Int,Int,Int)]
triada n = [(a,b,c) | c <- [1..n], b <- [1..c-1], a <- [1..b-1], a^2 + b^2 == c^2]

--Dado una lista devuelve los distintos posibles conjuntos
combinaciones :: (Eq a) => [a] -> [(a,a,a)]
combinaciones [] = []
combinaciones xs = [(x, y, z) | (x:rest) <- tails xs, (y:ys) <- tails rest, z <- ys]

data BinH a = Hoja a
            | Rama (BinH a) (BinH a) deriving (Show, Generic) -- Generic
                                                              -- es
                                                              -- úncamente
                                                              -- para
                                                              -- las
                                                              -- pruebas

--Dada una funcion aplicarla a lo largo de un arbol en orden
binHfold :: (a -> b -> b) -> b -> BinH a -> b
binHfold f b (Hoja a) = f a b
binHfold f b (Rama l r) = binHfold f der l
    where
        der = binHfold f b r

--Funcion que recibe un arbol y lo devuelve enumerado
binHenum :: BinH a -> BinH (Int,a)
binHenum tree = fst $ aux 0 tree
    where
        aux :: Int -> BinH a -> (BinH (Int, a), Int)
        aux n (Hoja x) = (Hoja (n, x), n + 1)
        aux n (Rama left right) = (Rama left' right', n'')
            where
                (left', n') = aux n left
                (right', n'') = aux n' right
                         
data Bin a = Vacio
           | Nodo a (Bin a) (Bin a) deriving (Show, Generic) -- Generic
                                                             -- es
                                                             -- únicamente
                                                             -- para
                                                             -- las
                                                             -- pruebas

--Dada una funcion aplicarla a lo largo de un arbol en inorder
binFold :: (a -> b -> b) -> b -> Bin a -> b
binFold f b Vacio = b                   -- Caso base 
binFold f b (Nodo a l r) = binFold f (f a right) l
    where
        right = binFold f b r

--Funcion que recibe un arbol y lo devuelve enumerado en inorder
binEnum :: Bin a -> Bin (Int,a)
binEnum tree = fst(aux 0 tree) 
   where
   aux:: Int -> Bin a -> (Bin(Int,a),Int)
   aux n Vacio =(Vacio,n)
   aux n (Nodo a l r)= let (izq, m)= aux n l
                           (der, z)= aux(m+1) r
                       in (Nodo (m,a) izq der, z)

-- | Número de pruebas

pruebas :: Int
pruebas = 1000 -- Este número indica el número de pruebas que se harán
               -- a cada función, lo pueden modificar siempre y cuando
               -- éste número sea mayor o igual a 100.