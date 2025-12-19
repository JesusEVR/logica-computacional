module Prop where

import Data.List (nub)

-- ------------------------------------------------------------------------------
-- Definicion de los tipos de datos siguientes:
-- Prop para representar las fórmulas proporsicionales usando los
-- constructores T, F, Var, Neg, Conj, Disy, Impl y Equiv para formulas atomicas,
-- negaciones, conjunciones, implicaciones y equivalencias respectivamente.
-- ------------------------------------------------------------------------------

data Prop = T | F | Var String
          | Neg Prop
          | Conj Prop Prop | Disy Prop Prop 
          | Impl Prop Prop | Equiv Prop Prop deriving Eq

type Estado = [String]

-- ------------------------------------------------------------------------------
-- Definir un ejemplar de la clase Show para el tipo de dato Prop que muestre una
-- cadena que represente las formulas proposicionales en notacion infija.
-- ------------------------------------------------------------------------------

instance Show Prop where
    -- show :: Prop -> String
    show T = "T"
    show F = "F"
    show (Var x) = x
    show (Neg p) = "¬"++ show p
    show (Conj p q) = "(" ++ show p ++ " /\\ " ++ show q ++ ")"
    show (Disy p q) = "(" ++ show p ++ " \\/ " ++ show q ++ ")"
    show (Impl p q) = "(" ++ show p ++ " -> " ++ show q ++ ")"
    show (Equiv p q) = "(" ++ show p ++ " <-> " ++ show q ++ ")"
-- ------------------------------------------------------------------------------
-- Ejercicio 2
-- Definir la funcion conjPotencia, tal que la aplicación de la funcion es la
-- lista de todos los subconjuntos de x.
-- ------------------------------------------------------------------------------

conjPotencia :: [a] -> [[a]]
conjPotencia [] = [[]]
conjPotencia (x:xs) = map (x:) aux ++ aux
    where aux = conjPotencia xs

-- ------------------------------------------------------------------------------
-- Ejercicio 3.
-- Definir la función vars::Prop -> [String] que devuelve el conjunto de variables
-- proposicionales de una fórmula.
-- ------------------------------------------------------------------------------

vars :: Prop -> [String]
vars T = []
vars F = []
vars (Var p) = [p]
vars (Neg prop) = vars prop
vars (Conj phi psi) = nub (vars phi ++ vars psi)
vars (Disy phi psi) = nub (vars phi ++ vars psi)
vars (Impl phi psi) = nub (vars phi ++ vars psi)
vars (Equiv phi psi) = nub (vars phi ++ vars psi)

-- ------------------------------------------------------------------------------
-- Ejercicio 4.
-- Definir la función interpreta que dada una formula proposicional y un estado
-- regrese la interpretación obtenida de la fórmula en dicho estado.
-- ------------------------------------------------------------------------------

interpretacion:: Prop -> Estado -> Bool
interpretacion T _ = True
interpretacion F _ = False
interpretacion (Var p) e = if (p `elem` e) then True else False
interpretacion (Neg prop) e = not (interpretacion prop e)
interpretacion (Conj phi psi) e = interpretacion phi e && interpretacion psi e
interpretacion (Disy phi psi) e = interpretacion phi e || interpretacion psi e
interpretacion (Impl phi psi) e = interpretacion (Disy (Neg phi) psi) e
interpretacion (Equiv phi psi) e = interpretacion (Conj (Impl phi psi) (Impl psi phi)) e

-- ------------------------------------------------------------------------------
-- Ejercicio 5.
-- Definir la funcion modelos :: Prop -> [Estado] que dada una fórmula devuelve
-- una lista de estados que satisfacen a dicha fórmula.
-- ------------------------------------------------------------------------------

modelos :: Prop -> [Estado]
modelos p = [e | e <- conjPotencia (vars p), interpretacion p e == True]


-- ------------------------------------------------------------------------------
-- Ejercicio 6.
-- Definir una función que dada una fórmula proposicional, indique si es una 
-- tautologia.
-- Firma de la funcion: tautologia:: Prop -> Bool
-- ------------------------------------------------------------------------------

tautologia :: Prop -> Bool
tautologia T = True
tautologia F = False
tautologia p = if False `elem` [interpretacion p e | e <- conjPotencia (vars p)] then False else True

-- ------------------------------------------------------------------------------
-- Ejercicio 7.
-- Definir una funcion que dada una fórmula proposicional, indique si es una
-- contradicción.
-- firma de la funcion: contradiccion :: Prop -> Bool
-- ------------------------------------------------------------------------------

contradiccion :: Prop -> Bool
contradiccion T = False
contradiccion F = True
contradiccion p = if True `elem` [interpretacion p e | e <- conjPotencia (vars p)] then False else True

-- ------------------------------------------------------------------------------
-- Ejercicio 8.
-- Definir una función que dada una fórmula proposicional phi, verifique si es 
-- satisfacible.
-- ------------------------------------------------------------------------------

esSatisfacible :: Prop -> Bool
esSatisfacible T = True
esSatisfacible F = False
esSatisfacible p = True `elem` [interpretacion p e | e <- conjPotencia (vars p)]

-- ------------------------------------------------------------------------------
-- Ejercicio 9.

-- Definir una función que elimine dobles negaciones y aplique las
-- leyes de DeMorgan dada una fórmula proposicional phi.
-- ------------------------------------------------------------------------------
deMorgan :: Prop -> Prop
deMorgan T = T
deMorgan F = F
deMorgan (Var p) = Var p
deMorgan (Neg (Neg p)) = deMorgan p
deMorgan (Neg (Conj p q)) = Disy (deMorgan (Neg p)) (deMorgan (Neg q))
deMorgan (Neg (Disy p q)) = Conj (deMorgan (Neg p)) (deMorgan (Neg q))
deMorgan (Conj p q) = Conj (deMorgan p) (deMorgan q)
deMorgan (Disy p q) = Disy (deMorgan p) (deMorgan q)
deMorgan (Impl p q) = Impl (deMorgan p) (deMorgan q)
deMorgan (Equiv p q) = Equiv (deMorgan p) (deMorgan q)
deMorgan (Neg p) = Neg (deMorgan p)

-- ------------------------------------------------------------------------------
-- Ejercicio 10.
-- Definir una función que elimine las implicaciones lógicas de una proposición
-- ------------------------------------------------------------------------------

elimImplicacion :: Prop -> Prop
elimImplicacion T = T
elimImplicacion F = F
elimImplicacion (Var p) = Var p
elimImplicacion (Impl p q) = Disy (Neg (elimImplicacion p)) (elimImplicacion q)
elimImplicacion (Neg p) = Neg (elimImplicacion p)
elimImplicacion (Conj p q) = Conj (elimImplicacion p) (elimImplicacion q)
elimImplicacion (Disy p q) = Disy (elimImplicacion p) (elimImplicacion q)
elimImplicacion (Equiv p q) = Equiv (elimImplicacion p) (elimImplicacion q)

-- ------------------------------------------------------------------------------
-- Ejercicio 11.
-- Definir una funcion que elimine las equivalencias lógicas de una proposición.
-- ------------------------------------------------------------------------------
elimEquivalencias :: Prop -> Prop
elimEquivalencias T = T
elimEquivalencias F = F
elimEquivalencias (Var p) = Var p
elimEquivalencias (Equiv p q) = 
    Conj (Impl (elimEquivalencias p) (elimEquivalencias q)) 
         (Impl (elimEquivalencias q) (elimEquivalencias p))
elimEquivalencias (Neg p) = Neg (elimEquivalencias p)
elimEquivalencias (Conj p q) = Conj (elimEquivalencias p) (elimEquivalencias q)
elimEquivalencias (Disy p q) = Disy (elimEquivalencias p) (elimEquivalencias q)
elimEquivalencias (Impl p q) = Impl (elimEquivalencias p) (elimEquivalencias q)

-- ------------------------------------------------------------------------------
-- Número de pruebas a hacer.
-- Puedes cambiar este valor siempre y cuando éste sea mayor o igual a 100.
-- ------------------------------------------------------------------------------
pruebas :: Int
pruebas = 1000