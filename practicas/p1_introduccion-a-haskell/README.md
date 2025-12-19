## Practica 1 :
- Integrantes:
  * Joshua Juárez Cruz                  No. de Cuenta: 320124516
  * Antonio Castillo Hernández          No. de Cuenta: 320017438
  * Emiliano Luna Campos                No. de Cuenta: 320292084
  * Jesús Elías Vázquez Reyes           No. de Cuenta: 320010549

## Funciones:
- traduceF :: String -> String
```
traduceF :: String -> String
traduceF = concatMap transformarCaracter
```
Para esta función nos apoyamos de una auxiliar:
  - transformarCaracter :: Char -> String
```
transformarCaracter :: Char -> String
transformarCaracter c
  | c `elem` "AEIOUaeiou" = c : 'f' : [toLower c]  
  | otherwise = [c]  
```
 
```traduceF``` reliza una llamada a ```transformarCaracter``` que recibe uno por uno cada caracter que conforma la cadena recibida por ```traduceF```, después revisa si cada caracter es una vocal o una consonante. Si es vocal, la concatena con un char 'f' y se apoya de la funcion toLower (existente en Haskell) para volver minúscula a la vocal minúscula y después la concatena. Si se trata de una consonante no le hace nada.

- mezcla :: [Int] -> [Int] -> [Int]
```
mezcla :: [Int] -> [Int] -> [Int]
mezcla []ys= ys
mezcla xs [] = xs
mezcla (x:xs) (y:ys)
    | x <= y    = x : mezcla xs (y:ys)
    | otherwise = y : mezcla (x:xs) ys  
```

En esta función recursiva, primero tenemos dos casos base, en la cual alguna de las dos listas es vacía, en este caso únicamente devuelve la otra lista. Tenemos entonces el caso recursivo, el cual consiste en primero tomar los primeros elementos de cada lista y los compara, el elemento más pequeño es el primero en la lista resultante y se mezcla el resto de la primera lista con la segunda lista intacta.
  
- palindromo :: String -> Bool
```
palindromo :: String -> Bool
palindromo palabra | cadena == "" = True
                   | cadena == reverse cadena = True
                   | otherwise = False
                   where cadena = cadenaSinEspacios $ map toLower palabra
                         cadenaSinEspacios = filter (/= ' ')
```

Esta funcion está puesta bajo tres casos: si el String es vacío, por vacuidad devuelve TRUE; si la cadena no es vacia, utilizamos una función para hacer el String en minúsculas y sin espacios, a este resultado aplicamos la funcion "reverse". Si el resultado es igual al mismo String devuelve TRUE, en otro caso devuelve FALSE.

- prefijoComun :: [String] -> String
```
prefijoComun :: [String] -> String
prefijoComun [] = ""
prefijoComun (x:xs) = foldl prefijoPal x xs
    where
        prefijoPal acc str = take (length $ takeWhile (uncurry (==)) (zip acc str)) acc
```
En esta función utilizamos dos casos, si la lista es vacia, devuelve la cadena vacia. En otro caso descompone la lista en elementos y con la funcion "fold1" de forma cumulativa utilizamos otra funcion, que primero crea una lista de tuplas, devuelve el número de caracteres consecutivos desde el inicio de las cadenas que son iguales y finalmente se usa para tomar esa cantidad de caracteres desde el inicio de acc, que es el acumulador que hasta ese punto contiene el prefijo común encontrado.
  
- diferencia :: (Eq a) => [a] -> [a] -> [a]
```
diferencia :: (Eq a) => [a]-> [a] -> [a]
diferencia xs ys = filter (\x -> notElem x ys) xs
```
Esta función, ```diferencia```, es una funcion simple que implementa una definición similar a una diferencia de conjuntos, i.e. dada una intancia de entrada de dos listas, devolvemos una nueva lista, cuyos elementos sean aquellos que cumplan con estar dentro de la primera lista y que no esta en la segunda lista. Para lograr esto nos apoyamos de la funcion ```filter (\x -> notElem x ys)```, que aplicar un 'filtro' sobre los elementos, en este caso se revisa mediante una función de orden superior que un elemento 'x' no sea un elemento de la lista 'ys'. 

- productoPunto :: [Integer] -> [Integer] -> Integer
```
productoPunto :: [Integer] -> [Integer] -> Integer
productoPunto xs ys = sum [x * y | x <- xs, y <- ys]
```
Utilizamos una funcion que recorre dos listas dadas, por cada elemento de estas que haya recorrido los multiplica y el resultado lo va sumando.
  
- triada :: Int -> [(Int,Int,Int)]
```
triada :: Int -> [(Int,Int,Int)]
triada n = [(a,b,c) | c <- [1..n], b <- [1..c-1], a <- [1..b-1], a^2 + b^2 == c^2]
```
Dado el numero obtenido, utilizamos una lista por compresion; en la cual definimos que la C del teorema de pitagoras puede ir en valor desde el 0 hasta el numero dado; que la B puede ir desde 0 hasta un numero antes que la C; y que A puede ir desde 0 hasta un valor antes de la B, y una ultima condicon que es la que pide el ejercicio, de esta manera obtenemos las distintas posibilades para obtener la triada.

- combinaciones :: (Eq a) => [a] -> [(a,a,a)]
```
combinaciones :: (Eq a) => [a] -> [(a,a,a)]
combinaciones [] = []
combinaciones xs = [(x, y, z) | (x:rest) <- tails xs, (y:ys) <- tails rest, z <- ys]
```
Tenemos dos casos. Si la lista es vacia, devuelve una lista vacia. En otro caso utilizamos tails para generar las posibles colas de la lista, posteriormente cada una de estas es descompuesta en cabeza y cola, de esta manera se toma el primer elemento y deja el resto para mas combinaciones, el resultado lo hace pasar por el mismo proceso, seleccionando un segundo elemento, y un tercer paso para el ultimo elemento.

- binHfold :: (a -> b -> b) -> b -> BinH a -> b
```
binHfold :: (a -> b -> b) -> b -> BinH a -> b
binHfold f b (Hoja a) = f a b
binHfold f b (Rama l r) = binHfold f der l
    where
        der = binHfold f b r
```
La funcion ```binHFold``` realiza un recorrido en orden del árbol binario, aplicando una función f a cada hoja del árbol, de izquierda a derecha. 

Cuando la función recibe una hoja (Hoja a), aplica la función f al valor de la hoja (a) y al valor inicial (b). Esto significa que cuando llega una hoja, se aplica la función f directamente a ese valor y al acumulado hasta el momento.
En el momento que la función recibe una rama (Rama l r), se llama recursivamente en el subárbol izquierdo (l). Sin embargo, antes de eso se calcula el acumulado del subárbol derecho (r) utilizando ```binHFold``` con el valor inicial b. Este valor acumulado del subárbol derecho (der) se pasa como segundo argumento a la dicha llamada recursiva. Esto último sirve para que primero se procesen todas las hojas del subárbol izquierdo antes de pasar al subárbol derecho, manteniendo así el orden de procesamiento de izquierda a derecha.

- binHenum :: BinH a -> BinH (Int,a)

```
binHenum :: BinH a -> BinH (Int,a)
binHenum tree = fst $ aux 0 tree
    where
        aux :: Int -> BinH a -> (BinH (Int, a), Int)
        aux n (Hoja x) = (Hoja (n, x), n + 1)
        aux n (Rama left right) = (Rama left' right', n'')
            where
                (left', n') = aux n left
                (right', n'') = aux n' right
```
La función ```binHenum``` toma un árbol binario y devuelve una versión enumerada del mismo, donde cada hoja está etiquetada con un número consecutivo, comenzando desde cero y siguiendo el orden de izquierda a derecha.

Dado un árbol binario, la función ```binHenum``` asigna a cada hoja una etiqueta única en forma de tupla, donde el primer elemento de la tupla es el número de etiqueta y el segundo es el valor original de la hoja.

Notece que la función ```aux``` toma un contador **n** y un **árbol BinH** a y devuelve un par donde el primer elemento es el árbol con hojas enumeradas y el segundo elemento es el próximo número de etiqueta disponible. Para una hoja, simplemente etiqueta la hoja con el número actual y actualiza el contador. Para un nodo, aplica recursivamente ```aux``` en los subárboles izquierdo y derecho, actualizando el contador en cada paso.

- binFold :: (a -> b -> b) -> b -> Bin a -> b
```
binFold :: (a -> b -> b) -> b -> Bin a -> b
binFold f b Vacio = b                   -- Caso base 
binFold f b (Nodo a l r) = binFold f (f a right) l
    where
        right = binFold f b r
```
La funcion ```binFold``` se encarga de realizar la 'evaluación' de una función 'f' a lo largo de cada elemento de un árbol 'bin' y teniendo como valor 'final' a b, el caso base. 

Para nuesta implementación de ```binFold``` tenemos dos casos: el caso base, cuando la lista que se pasas como parametro es vacia, en el que se regresa el valor final; y tenemos un caso recursivo, en el que el árbol tiene un elemento y dos subárboles izquierdo y derecho; primero aplica binfold al derecho que acumula un valor, este se combina con el nodo raiz para posteriormente aplicar binfold en el subarbol izquierdo y tambien combinar los resultados. 

- binEnum :: Bin a -> Bin (Int,a)

```
binEnum :: Bin a -> Bin (Int,a)
binEnum tree = fst(aux 0 tree) 
   where
   aux:: Int -> Bin a -> (Bin(Int,a),Int)
   aux n Vacio =(Vacio,n)
   aux n (Nodo a l r)= let (izq, m)= aux n l
                           (der, z)= aux(m+1) r
                       in (Nodo (m,a) izq der, z)

```

La función ```binEnum``` toma un árbol binario y regresa una versión enumerada del mismo, donde se sigue un recorrido **in-order**.

Nótese que dado un árbol binario, la función ```binEnum``` asigna a cada nodo una etiqueta única en forma de tupla, donde el primer elemento de la tupla es el número de etiqueta y el segundo es el valor original del nodo. La enumeración sigue un recorrido **in-order**, lo que significa que los nodos se enumeran en el orden en que se visitan, primero el hijo izquierdo, luego el nodo actual y finalmente el hijo derecho.

Tambien tenemos uan funcion aurxiliar llamada ```aux``` que toma un contador **n** y un árbol Binario y devuelve un par donde el primer elemento es el árbol con nodos enumerados y el segundo elemento es el próximo número de etiqueta disponible. Para el caso base, cuando se alcanza una hoja *(Vacio)*, simplemente devuelve una hoja con el contador actual y el mismo contador. Para un nodo, aplica recursivamente ```aux``` en los subárboles izquierdo y derecho, incrementando el contador en cada paso.
