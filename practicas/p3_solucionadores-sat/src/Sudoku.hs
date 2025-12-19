module Sudoku where

import SAT.MiniSat

type Sudoku = [(Int,Int,Int)]

celdas:: Sudoku -> Formula (Int, Int, Int)
celdas sudo = All[ExactlyOne[Var (i,j,n)| n <- [1..9] ] | i <- [1..9], j <- [1..9]]

-- Asegura que cada fila tenga todos los números del 1 al 9 sin repetir.
filas :: Sudoku -> Formula (Int, Int, Int)
filas sudo =  All[ExactlyOne [Var (i, j, n) | j <- [1..9]] | i <- [1..9], n <- [1..9]]

-- Asegura que cada columna tenga todos los números del 1 al 9 sin repetir.
columnas :: Sudoku -> Formula (Int, Int, Int)
columnas sudo = All[ExactlyOne [Var (i, j, n) | i <- [1..9]] | j <- [1..9], n <- [1..9]]

-- Asegura que cada bloque 3x3 tenga todos los números del 1 al 9 sin repetir.
bloque :: Sudoku -> Formula (Int, Int, Int)
bloque sudo = All[ExactlyOne [Var (bi + i, bj + j, n) |i <- [0..2], j <- [0..2]] |bi<-[1,4,7], bj <- [1,4,7], n <- [1..9]]

sudokuFormula :: Sudoku -> Formula (Int, Int, Int)
sudokuFormula sudo = All (map (\(i, j, n) -> Var (i, j, n)) sudo) :&&: celdas sudo :&&: filas sudo :&&: columnas sudo :&&: bloque sudo
