module PrimerOrden where

import Data.Char
import Data.List
import Data.Maybe (isJust)

type Simbolo = String

data Term = Var Simbolo | Fun Simbolo [Term] deriving Eq

data Formula = Verdadero | Falso
            | Predicado Simbolo [Term]
            | No Formula
            | Conj Formula Formula | Disy Formula Formula
            | Impl Formula Formula | Equiv Formula Formula
            | ForAll Simbolo Formula | Exist Simbolo Formula
            deriving Eq

type Substitucion = (Simbolo, Term)

type Unificador = [Substitucion]

type Clausula = [Formula]

infixr 4 `ForAll`, `Exist`
infixl 3 `Conj`, `Disy`
infixl 2 `Equiv`
infixr 1 `Impl`

-- ------------------------------------------------------------------------------
    -- Ejercicio 1.
    -- Definir un ejemplar de la clase Show para el tipo de dato Term que muestre una
    -- cadena que represente las formulas
-- -----------------------------------------------------------------------------
instance Show Term where
  --show :: Term -> String
  show (Var x) = x
  show (Fun f term) = f ++ "(" ++ intercalate ", " (map show term) ++ ")"

-- ------------------------------------------------------------------------------
    -- Ejercicio 2.
    -- Definir un ejemplar de la clase Show para el tipo de dato Formula que muestre una
    -- cadena que represente los terminos
    -- Utiliza los caracteres: ∀ y ∃ para denotar los cuantificadores.
-- -----------------------------------------------------------------------------
instance Show Formula where
  --show :: Formula -> String
  show Verdadero = "V"
  show Falso = "F"
  show (Predicado p term) = map toUpper p ++ "(" ++ intercalate "," (map show term) ++ ")" 
  show (No form) = "¬" ++ show form
  show (Conj phi psi) = "(" ++ show phi ++ " /\\ " ++ show psi ++ ")"
  show (Disy phi psi) = "(" ++ show phi ++ " \\/ " ++ show psi ++ ")"
  show (Impl phi psi) = "(" ++ show phi ++ " -> " ++ show psi ++ ")"
  show (Equiv phi psi) = "(" ++ show phi ++ " <-> " ++ show psi ++ ")"
  show (ForAll sim form) = "∀ " ++ sim ++ "." ++ show form 
  show (Exist sim form) = "∃ " ++ sim ++ "." ++ show form

-- ------------------------------------------------------------------------------
    -- Ejercicio 3.
    -- Definir una funcion que devuelva el conjunto de variables libres de una formula.
-- ------------------------------------------------------------------------------
libres :: Formula -> [String]
libres Verdadero = []
libres Falso = []
libres (Predicado _ ts) = nub $ concatMap obtenerVariables ts  --Usamos la func auxiliar "obtenerVariables"
libres (No f) = libres f
libres (Conj f1 f2) = nub $ libres f1 ++ libres f2
libres (Disy f1 f2) = nub $ libres f1 ++ libres f2
libres (Impl f1 f2) = nub $ libres f1 ++ libres f2
libres (Equiv f1 f2) = nub $ libres f1 ++ libres f2
libres (ForAll x f) = delete x $ libres f
libres (Exist x f) = delete x $ libres f

-- ------------------------------------------------------------------------------
    -- Ejercicio 4.
    -- Definir una funcion que devuelva las variables ligadas de una formula
-- ------------------------------------------------------------------------------
ligadas :: Formula -> [String]
ligadas Verdadero = []
ligadas Falso = []
ligadas (Predicado _ _) = [] --Si una var no tiene predicado quiere decir que no tiene variables ligadas por lo cual es vacia
ligadas (No f) = ligadas f
ligadas (Conj f1 f2) = nub $ ligadas f1 ++ ligadas f2
ligadas (Disy f1 f2) = nub $ ligadas f1 ++ ligadas f2
ligadas (Impl f1 f2) = nub $ ligadas f1 ++ ligadas f2
ligadas (Equiv f1 f2) = nub $ ligadas f1 ++ ligadas f2
ligadas (ForAll x f) = x : ligadas f
ligadas (Exist x f) = x : ligadas f

-- ------------------------------------------------------------------------------
    -- Ejercicio 5.
    -- Definir una funcion que trate de aplicar una substitucion una formula
    -- Debe devolver un error si no es posible aplicarla.
-- ------------------------------------------------------------------------------
vars :: Substitucion -> Term -> Term
vars (x,t) (Var s) = if( s /= x) then (Var s) else t
vars _ (Fun s []) = (Fun s [])
vars (x,t) (Fun s terms) = (Fun s (map (vars (x,t)) terms))

subsv1 :: Formula -> Substitucion -> Formula
subsv1 Verdadero _ = Verdadero
subsv1 Falso _ = Falso
subsv1 (Predicado p terms) s = (Predicado p (map (vars s) terms) )
subsv1 (No phi) s = No (subsv1 phi s)
subsv1 (Conj phi psi) s = (Conj (subsv1 phi s) (subsv1 psi s))
subsv1 (Disy phi psi) s = (Disy (subsv1 phi s) (subsv1 psi s))
subsv1 (Impl phi psi) s = (Impl (subsv1 phi s) (subsv1 psi s))
subsv1 (Equiv phi psi) s = (Equiv (subsv1 phi s) (subsv1 psi s))
subsv1 (ForAll s phi) (x,t) = if (x `elem` (ligadas phi)) then error "No es posible sustituir variables ligadas" else (ForAll s (subsv1 phi (x,t))) 
subsv1 (Exist s phi) (x,t) =  if (x `elem` (ligadas phi)) then error "No es posible sustituir variables ligadas" else (Exist s (subsv1 phi (x,t))) 

-- ------------------------------------------------------------------------------
    -- Ejercicio 6.
    -- Definir una funcion que determine si dos formulas son alfaequivalentes.
-- ------------------------------------------------------------------------------
alfaEquivalencia :: Formula -> Formula -> Bool
alfaEquivalencia Verdadero Verdadero = True
alfaEquivalencia Falso Falso = True
alfaEquivalencia (Predicado p ts) (Predicado q rs) = if p == q && not(False `elem` zipWith (==) ts rs) then True else False
alfaEquivalencia (No p) (No q) = alfaEquivalencia p q
alfaEquivalencia (Conj p1 p2) (Conj q1 q2) = alfaEquivalencia p1 q1 && alfaEquivalencia p2 q2
alfaEquivalencia (Disy p1 p2) (Disy q1 q2) = alfaEquivalencia p1 q1 && alfaEquivalencia p2 q2
alfaEquivalencia (Impl p1 p2) (Impl q1 q2) = alfaEquivalencia p1 q1 && alfaEquivalencia p2 q2
alfaEquivalencia (Equiv p1 p2) (Equiv q1 q2) = alfaEquivalencia p1 q1 && alfaEquivalencia p2 q2 
alfaEquivalencia (ForAll x p) (ForAll y q) = alfaEquivalencia p (subsv1 q (y, Var x)) 
alfaEquivalencia (Exist x p) (Exist y q) = alfaEquivalencia p (subsv1 q (y, Var x)) 
alfaEquivalencia _ _ = False

obtenerVariables :: Term -> [String]
obtenerVariables (Var x) = [x]
obtenerVariables (Fun _ ts) = nub $ concatMap obtenerVariables ts

-- ------------------------------------------------------------------------------
    -- Ejercicio 7.
    -- Definir una funcion que obtenga el umg de dos formulas 
    -- si no es posible obtener el umg regresa error
-- ------------------------------------------------------------------------------
unifica :: Formula -> Formula -> Maybe Unificador
unifica f g = aux_unifica2 (aux_unifica f g) []


aux_unifica :: Formula -> Formula -> Maybe [(Term,Term)]
aux_unifica (Predicado p t1) (Predicado q t2)
    | (p == q) && (length (t1) == length(t2)) = Just (zip t1 t2)
    | otherwise = Nothing
aux_unifica (No f) (No g) = aux_unifica f g
aux_unifica (Conj f1 f2) (Conj g1 g2) = case (aux_unifica f1 g1, aux_unifica f2 g2) of
                                            (Nothing,_) -> Nothing
                                            (_,Nothing) -> Nothing
                                            (Just t1, Just t2) -> Just (t1 ++ t2)
aux_unifica (Disy f1 f2) (Disy g1 g2) = case (aux_unifica f1 g1, aux_unifica f2 g2) of
                                            (Nothing,_) -> Nothing
                                            (_,Nothing) -> Nothing
                                            (Just t1, Just t2) -> Just (t1 ++ t2)
aux_unifica (Impl f1 f2) (Impl g1 g2) = case (aux_unifica f1 g1, aux_unifica f2 g2) of
                                            (Nothing,_) -> Nothing
                                            (_,Nothing) -> Nothing
                                            (Just t1, Just t2) -> Just (t1 ++ t2)
aux_unifica (Equiv f1 f2) (Equiv g1 g2) = case (aux_unifica f1 g1, aux_unifica f2 g2) of
                                            (Nothing,_) -> Nothing
                                            (_,Nothing) -> Nothing
                                            (Just t1, Just t2) -> Just (t1 ++ t2)
aux_unifica _ _ = Nothing

aux_unifica2 :: Maybe [(Term,Term)] -> Unificador -> Maybe Unificador
aux_unifica2 Nothing sigma = Nothing
aux_unifica2 (Just []) sigma = Just sigma
aux_unifica2 (Just ((Var x,Var y):xs)) sigma 
    | x == y = aux_unifica2 (Just xs) sigma
    | otherwise = let sust = (x, Var y)
                      sigma' = sust : map (\(s,t) -> (s,vars sust t)) sigma
                      w = map (\(t1,t2) -> (vars sust t1, vars sust t2)) xs
                    in
                    aux_unifica2 (Just w) sigma'
aux_unifica2 (Just ((Var x, t):xs)) sigma
    | x `elem` obtenerVariables t = Nothing
    | otherwise = let sust = (x, t)
                      sigma' = sust : map (\(s,t') -> (s,vars sust t')) sigma
                      w = map (\(t1,t2) -> (vars sust t1, vars sust t2)) xs
                    in
                    aux_unifica2 (Just w) sigma'
aux_unifica2 (Just ((t, Var x):xs)) sigma
    | x `elem` obtenerVariables t = Nothing
    | otherwise = let sust = (x, t)
                      sigma' = sust : map (\(s,t) -> (s,vars sust t)) sigma
                      w = map (\(t1,t2) -> (vars sust t1, vars sust t2)) xs
                    in
                    aux_unifica2 (Just w) sigma'
aux_unifica2 (Just ((Fun f t1, Fun g t2):xs)) sigma
    | f == g && length t1 == length t2 = aux_unifica2 (Just $ zip t1 t2 ++ xs) sigma
    | otherwise = Nothing

-- ------------------------------------------------------------------------------
    -- Ejercicio 8.
    -- Definir una funcion que determine si es posible obtener un
    -- resolvente dadas dos formulas
    -- ------------------------------------------------------------------------------
-- Intenta encontrar un par de literales complementarios en dos cláusulas que se pueden unificar

resolvente :: Clausula -> Clausula -> Bool
resolvente c1 c2 =
    any esResolventePosible [(f1, f2) | f1 <- c1, f2 <- c2, isJust (comUnificables f1 f2)]
  where
    esResolventePosible (f1, f2) =
        case comUnificables f1 f2 of
          Just _ -> clausVacia c1 c2 f1 f2
          Nothing -> False


clausVacia :: Clausula -> Clausula -> Formula -> Formula -> Bool
clausVacia c1 c2 f1 f2 =
    let aplicada1 = delete f1 c1
        aplicada2 = delete f2 c2
        var1 = concatMap libres aplicada1
        var2 = concatMap libres aplicada2
    in null (intersect var1 var2)

    

comUnificables :: Formula -> Formula -> Maybe Unificador
comUnificables (Predicado p1 t1) (No (Predicado p2 t2)) | p1 == p2 = unifica (Predicado p1 t1) (Predicado p2 t2)
comUnificables (No (Predicado p1 t1)) (Predicado p2 t2) | p1 == p2 = unifica (Predicado p1 t1) (Predicado p2 t2)
comUnificables _ _ = Nothing


-- ------------------------------------------------------------------------------
    -- Ejercicio 9.
    -- Definir una funcion que dadas dos claúsulas, obtenga el resolvente obtenido de aplicar la regla de resolución binaria.
-- ------------------------------------------------------------------------------

resolucion :: Clausula -> Clausula -> Clausula
resolucion c1 c2 =
    case find (\(f1, f2) -> esResoluble (f1, f2)) [(f1, f2) | f1 <- c1, f2 <- c2] of
      Just (f1, f2) -> delete f1 c1 ++ delete f2 c2
      Nothing       -> error "No hay resolvente "
  where
    esResoluble (Predicado p1 t1, No (Predicado p2 t2)) = p1 == p2 && isJust (unifica (Predicado p1 t1) (Predicado p2 t2))
    esResoluble (No (Predicado p1 t1), Predicado p2 t2) = p1 == p2 && isJust (unifica (Predicado p1 t1) (Predicado p2 t2))
    esResoluble _ = False

-- ------------------------------------------------------------------------------
    -- Pruebas.
-- ------------------------------------------------------------------------------
pruebas :: Int
pruebas = 1000


