module Main where

import Sudoku (Sudoku, sudokuFormula)
import SAT.MiniSat (solve)
import Data.Map.Lazy (toList)
import Data.Char
import Data.List

sudoSolve :: Sudoku -> Maybe Sudoku
sudoSolve s = fmap (map fst . filter snd . toList) $
              solve $
              sudokuFormula s

parseLine :: Int -> String -> [(Int,Int,Int)]
parseLine n str = map (uncurry $ (,,) n) $
                  filter ((/= 0) . snd) $
                  zip [1..9] $
                  map digitToInt str

printSol :: Int -> [(Int,Int,Int)] -> String
printSol n xs | n > 9 = ""
              | otherwise = (++ ("\n" ++ printSol (n+1) xs)) $
                            ((show n ++ " | ") ++) $
                            foldr (\x acc -> x : ' ' : acc) [] $
                            map (intToDigit . trd) $
                            sortBy (\(_,a,_) (_,b,_) -> compare a b) $
                            filter ((== n) . fst') xs 
  where
    fst' (a,_,_) = a
    trd (_,_,c) = c

sudoReader :: [(Int,Int,Int)] -> Int -> IO [(Int,Int,Int)]
sudoReader xs n | n > 9 = return xs
            | otherwise = do
                putStrLn $
                  "Ingresa los números de la fila " ++
                  show n ++
                  " (los espacios en blanco se denotan con un 0):"
                x <- getLine
                if any (not . isDigit) x || length x /= 9 then do
                  putStrLn "No es una fila válida"
                  sudoReader xs n
                  else
                  sudoReader (xs ++ parseLine n x) (n+1)

readSolve :: IO ()
readSolve = do
  xs <- sudoReader [] 1
  case sudoSolve xs of
    Nothing -> putStrLn "El sudoku no tiene solucion"
    Just sol -> do
      putStrLn "La solución es la siguiente:"
      putStrLn "  | 1 2 3 4 5 6 7 8 9"
      putStrLn "---------------------"
      putStrLn $ printSol 1 sol

main :: IO ()
main = do
  putStrLn "==== Sudoku Solver 1.0.0. ===="
  putStrLn "1. Resolver Sudoku\n2. Salir"
  putStrLn "Elige una opción:"
  x <- getLine
  if any (not . isDigit) x then
    putStrLn "No es una opción válida" >> main
    else
    case read x :: Int of
      1 -> readSolve >> main
      2 -> return ()
      _ -> putStrLn "No es una opción válida" >> main
