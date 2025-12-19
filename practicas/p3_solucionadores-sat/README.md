## Práctica 3
- Integrantes:
  * Joshua Juárez Cruz                  No. de Cuenta: 320124516
  * Antonio Castillo Hernández          No. de Cuenta: 320017438
  * Emiliano Luna Campos                No. de Cuenta: 320292084
  * Jesús Elías Vázquez Reyes           No. de Cuenta: 320010549


## Ejercicios

- SudokuFormula:
Formula que recibe un sudoku, y devuelve una formula que expresa las reestricciones que se deben de cumplir en un tablero de sudoku.Se recibe una lista de tuplas (con las coordenas y el elemento de la celda). Para cada una de estas se crea una variable, que hacemos verdadera con miniSAT, y finalmente se acompañan de AND's con funciones auxliares para proceder de manera logica sobre el sudoku dado.

```
sudokuFormula :: Sudoku -> Formula (Int, Int, Int)
sudokuFormula sudo = All (map (\(i, j, n) -> Var (i, j, n)) sudo) :&&: celdas sudo :&&: filas sudo :&&: columnas sudo :&&: bloque sudo

```

- Celdas:
Funcion auxiliar, que recibe un sudoku, y devuelve una formula logica. Primero con All se establece que todas las condiciones especificadas dentro del rango deben ser verdaderas. Ademas se crea una lista de formulas logicas para cada celda, cada formula se asegura que en una celda especifica exactamente un número n entre 1 y 9 esté presente.

```
celdas:: Sudoku -> Formula (Int, Int, Int)
celdas sudo = All[ExactlyOne[Var (i,j,n)| n <- [1..9] ] | i <- [1..9], j <- [1..9]]
```

- Filas:
Funcion auxiliar, que recibe un sudoku, y devuelve una formula logica.Se crea una fórmula lógica que establece que todas las condiciones especificadas dentro del rango deben ser verdaderas para los indices i y n. Por otro lado se crea una lista de fórmulas lógicas, una para cada fila y número en el Sudoku, se asegura que en una fila y numero especifico exactamente una de las variables en la lista [Var (i,1,n), Var (i,2,n), ..., Var (i,9,n)] debe ser verdadera.

```
filas :: Sudoku -> Formula (Int, Int, Int)
filas sudo =  All[ExactlyOne [Var (i, j, n) | j <- [1..9]] | i <- [1..9], n <- [1..9]]
```

- Columnas:
Funcion auxiliar analoga para la anterior, unicamente con la diferencia de que las condiciones deben ser verdaderas para los indices j y n. Por lo que se asegura que en una columna y numero especifico exactamente una de las variables en la lista [Var (1,j,n), Var (2,j,n), ..., Var (9,j,n)] debe ser verdadera.

```
columnas :: Sudoku -> Formula (Int, Int, Int)
columnas sudo = All[ExactlyOne [Var (i, j, n) | i <- [1..9]] | j <- [1..9], n <- [1..9]]
```

- Bloques:

Funcion auxiliar, igualmente recibe un sudoku y devuelve una formula logica de tuplas. crea una fórmula lógica que establece que todas las condiciones especificadas dentro de los rangos 1,4,7  para bi (que representa el índice de la fila inicial de cada bloque), 1,4,7 para bj (que representa el índice de la columna inicial de cada bloque) y 1..9 para n (que representa el número) deben ser verdaderas. 

Posteriormente con un proceso mas enrevesado se recorre por bloques de 3x3. Se crea una lista de formulas logcas, cada fórmula asegura que en un bloque específico y un número específico n, exactamente una de las variables en la lista [Var (bi + i, bj + j, n) | i <- \[0..2\], j <- \[0..2\]\] debe ser verdadera, es decir nos aseguramos que en el rango de n (1...9), no se debe repetir alguno de estos numeros.

```
sudokuFormula :: Sudoku -> Formula (Int, Int, Int)
sudokuFormula sudo = All (map (\(i, j, n) -> Var (i, j, n)) sudo) :&&: celdas sudo :&&: filas sudo :&&: columnas sudo :&&: bloque sudo

```



