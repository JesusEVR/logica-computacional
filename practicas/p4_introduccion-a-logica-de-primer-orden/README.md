## Práctica 4
- Integrantes:
  * Antonio Castillo Hernández          No. de Cuenta: 320017438
  * Emiliano Luna Campos                No. de Cuenta: 320292084
  * Jesús Elías Vázquez Reyes           No. de Cuenta: 320010549
  * Joshua Juárez Cruz                  No. de Cuenta: 320124516

## Ejercicios:
- Ejercicio 1. instance Show Term where
```
instance Show Term where
  --show :: Term -> String
  show (Var x) = x
  show (Fun f term) = f ++ "(" ++ intercalate ", " (map show term) ++ ")"

```
Esta función devuelve la representación en una cadena de un términos lógicos de la lógica de primer orden. Tenemos dos casos: si el término es una variable, simplemente devuelve su Simbolo; si el término es una función, construye una representación en forma de cadena que comienza con el nombre de la función, seguido de los argumentos de la función entre paréntesis, separados por comas. 

La instrucción ```map show term``` aplica la función show a cada término en la lista de terminos de la función, convirtiéndolos en una lista con sus representaciones en cadenas. Luego, ```intercalate ", "``` toma esta lista de cadenas y las concatena en una sola cadena, insertando ", " entre estas.

- Ejercicio 2. instance Show Formula where
```
instance Show Formula where
  show Verdadero = "V"
  show Falso = "F"
  show (Predicado p term) = (map toUpper p) ++ "(" ++ intercalate "," (map show term) ++ ")" 
  show (No form) = "¬" ++ show form
  show (Conj phi psi) = show phi ++ " /\\ " ++ show psi
  show (Disy phi psi) = show phi ++ " /\\ " ++ show psi
  show (Impl phi psi) = show phi ++ " /\\ " ++ show psi
  show (Equiv phi psi) = show phi ++ " /\\ " ++ show psi
  show (ForAll sim form) = "∀ " ++ sim ++ " . (" ++ show form ++ ")"
  show (Exist sim form) = "∃ " ++ sim ++ " . (" ++ show form ++ ")"

```
Esta función devuelve las fórmulas lógicas representadas como cadenas de texto. Para esta implementación consideramos varios casos:

Cuando la fórmula es ```Verdadero```, se representa simplemente por el carácter ```V```.

Cuando la fórmula es ```Falso```, se representa por el carácter ```F```.

Cuando se tiene un ```Predicado```, se convierte el símbolo asosciado al predicado a mayúsculas usando ```map toUpper p```. Luego, los términos del predicado se representan usando la instancia Show de Term, y se concatenan con comas entre ellos de manera similar al caso de las funciones en la función show para terminos.

En la negación (```No```), se añade el símbolo ```¬``` antes de la representación textual de la fórmula.

La conjunción (```Conj```) de dos fórmulas se representa con el símbolo ```/\```, situado entre las representaciones textuales de phi y psi, ambas encerradas entre paréntesis. La disyunción (```Disy```), implicación (```Impl```) y equivalencia (```Equiv```) se representan de manera similar a la conjunción, pero con sus símbolos correspondientes.

Para el cuantificador universal, usamos el símbolo ```∀```, seguido del símbolo de la variable y un punto, antes de la fórmula en la que se aplica el cuantificador. 

Para el cuantificador existencial, se representa de manera similar, pero en este caso con el símbolo ```∃```.

- Ejercicio 3. libres :: Formula -> [Simbolo]
```
libres :: Formula -> [String]
libres Verdadero = []
libres Falso = []
libres (Predicado _ ls) = nub (concatMap obtenerVariables ls)
libres (No f) = libres f 
libres (Conj f g) = nub ( libres f ++ libres g) 
libres (Disy f g) = nub ( libres f ++ libres g)
libres (Impl f g) = nub ( libres f ++ libres g)
libres (Equiv f g) = nub ( libres f ++ libres g)
libres (ForAll s f) = delete s (libres f)
libres (Exist s f) = delete   s (libres f)

```
Esta función regresa una lista de variables libres de una formula. Se presentan varios casos:

Las fórmulas Verdadero y Falso no contienen variables, por lo que la lista de variables libres es vacía.

En el caso de un predicado, calcula las variables libres de cada término en ls, utilizando la función ```libresEnTermino``` y la función ```concatMap``` para aplicar esta función a cada término y luego unir los resultados. Finalmente, usamos ```nub``` para eliminar duplicados.

Cuando se tiene la negación de una fórmula f, se regresan las mismas variables libres de f.

Para los operadores binarios conjunción, disyunción, implicación y equivalencia, la función combina las listas de variables libres de las subfórmulas f y g, utilizando ++ para concatenar las listas y ```nub``` para eliminar duplicados.

Para los cuantificadores, cualquier aparición de la variable s en la fórmula f ya no es libre. La instrucción ```delete s (libres f)``` elimina la variable s de la lista de variables libres obtenida de f, así nos aseguramos que solo se regresen las variables que son realmente libres.

- Ejercicio 4. ligadas :: Formula -> [String]
```
ligadas :: Formula -> [String]
ligadas Verdadero = []
ligadas Falso = []
ligadas (Predicado _ ls) = []
ligadas (No f) = ligadas f 
ligadas (Conj f g) = nub ( ligadas f ++ ligadas g) 
ligadas (Disy f g) = nub ( ligadas f ++ ligadas g)
ligadas (Impl f g) = nub ( ligadas f ++ ligadas g)
ligadas (Equiv f g) = nub ( ligadas f ++ ligadas g)
ligadas (ForAll x f) = x : (ligadas f)
ligadas (Exist x f) = x : (ligadas f)

```

Esta función se encarga de devolver una lista de todas las variables que están ligadas en una fórmula. Recordemos que las variables ligadas son aquellas que están definidas dentro de los cuantificadores universales y que tienen la particularidad de que afectan el alcance de las subfórmulas en las que aparecen. 

Dicha función es relevante en la lógica de primer orden ya que cobran especial relevancia cuando se evalúan o transforman fórmulas en este contexto. Ahora bien demos un vistazo la forma en que se implemento:

#### Implementación:
- **Casos base:** Para las constantes `Verdadero` y `Falso`, y en el caso de un `Predicado` sin cuantificadores, no hay variables ligadas, ya que eso se establece en los axiomas de la lógica de primer orden, por lo tanto se devuelve una lista vacía.

- **Recursividad:** Para operadores lógicos (como `No`, `Conj`, `Disy`, `Impl`, `Equiv`), se aplica la función `ligadas` a las subfórmulas y se combinan los resultados usando `nub` para eliminar duplicados, asegurando que cada variable ligada aparezca solo una vez en la lista resultante.

- **Cuantificadores:** En los casos de `ForAll` y `Exist`, la variable del cuantificador se añade a la lista de variables ligadas de la subfórmula correspondiente. Esto refleja el hecho de que la variable está ligada dentro del alcance del cuantificador.

Así mismo la función `nub` se usa para asegurarse de que la lista de variables en los casos recursivos no contenga variables duplicadas que pudieran aparecer como resultado de la concatenación de listas de variables o de cualquier otra manipulación.

- Ejercicio 5. subsv1 :: Formula -> Substitucion -> Formula
```
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

```
La función `subsv1` se encarga de aplicar una substitución a una fórmula dada. Recordando que una substitución es un par  que se compone de "(símbolo, término)" que nos indica cómo reemplazar todas las ocurrencias de un símbolo en una fórmula por un término dado. Veamos que la función se implementa recursivamente para todos los constructores posibles de fórmulas y tenemos dos tipos de casos:

- **Casos base:** Para las constantes que son `Verdadero` y `Falso`, la substitución no modifica la fórmula ya que como su nombre nos indica, son constantes y estas en la Lógica de Primer Orden/LPRED, no se sustituyen.

- **Casos recursivos:** Ahora bien, en los casos recursivos para operadores lógicos y cuantificadores, se aplica la substitución recursivamente a las subfórmulas. Si el símbolo a substituir está ligado por un cuantificador, se lanza un error, pues no se pueden substituir variables ligadas en la lógica de primer orden.

Por lo tanto es de esta manera en la que se aplican las substituciones de formula a formula.

- Auxiliar. vars :: Substitucion -> Term -> Term
```
vars :: Substitucion -> Term -> Term
vars (x,t) (Var s) = if( s /= x) then (Var s) else t
vars _ (Fun s []) = (Fun s [])
vars (x,t) (Fun s terms) = (Fun s (map (vars (x,t)) terms))

```
Veamos ahora que la función `vars` aplica una substitución a un término dentro del contexto de la lógica de primer orden. Es decir, en este caso la substitución se trata de un par `(x, t)` donde `x` es el símbolo de una variable y `t` es el término que reemplazará a `x`. Dicha función consta de 3 posibles casos:

- **Caso `Var s`**: Si el término es una variable y su símbolo `s` es igual a `x`, entonces se sustituye por el término `t`. Si `s` es diferente de `x`, el término se deja sin cambios.

- **Caso `Fun s []`**: Cuando el término es una función sin argumentos, se devuelve tal cual, ya que no hay variables dentro de esta función para sustituir.

- **Caso `Fun s terms`**: Si el término es una función con argumentos, la función `vars` se aplica recursivamente a cada uno de los argumentos de la función. Esto asegura que todas las ocurrences de la variable `x` dentro de los argumentos sean sustituidas por `t`.

Notese que esta implementación puede aplicar substituciones de forma  recursiva, por lo cual de esta manera es mas sencillo encontrar todos los posibles casos de estructuras de términos de este estilo que pueden aparecer en la lógica de primer orden.

- Ejercicio 6. alfaEquivalencia :: Formula -> Formula -> Bool

```
alfaEquivalencia :: Formula -> Formula -> Bool
alfaEquivalencia Verdadero Verdadero = True
alfaEquivalencia Falso Falso = False
alfaEquivalencia (Predicado p ts) (Predicado q rs) = if p == q && not(False `elem` zipWith (==) ts rs) then True else False
alfaEquivalencia (No p) (No q) = alfaEquivalencia p q
alfaEquivalencia (Conj p1 p2) (Conj q1 q2) = alfaEquivalencia p1 q1 && alfaEquivalencia p2 q2
alfaEquivalencia (Disy p1 p2) (Disy q1 q2) = alfaEquivalencia p1 q1 && alfaEquivalencia p2 q2
alfaEquivalencia (Impl p1 p2) (Impl q1 q2) = alfaEquivalencia p1 q1 && alfaEquivalencia p2 q2
alfaEquivalencia (Equiv p1 p2) (Equiv q1 q2) = alfaEquivalencia p1 q1 && alfaEquivalencia p2 q2 
alfaEquivalencia (ForAll x p) (ForAll y q) = alfaEquivalencia p (subsv1 q (y, Var x)) 
alfaEquivalencia (Exist x p) (Exist y q) = alfaEquivalencia p (subsv1 q (y, Var x)) 
alfaEquivalencia _ _ = False
```

Este función recibe dos ```Formulas``` de la lógica de primer orden y revisa si una es una alfa equivalencia de la otra. Para esto utilizamos nuestra función, previamente definida, ```subsv1``` que se encarga de realizar una substitución en una ```Formula```. El funcionamiento es sencillo: Si al realizar la substitución sobre la segunda Formula podemos deducir que los terminos en ambas funciones son los mismos, entonces la Formula original era una alfa equivalencia de la primer Formula.

Para esta función ocupamos una implementación recursiva para cada constructor del tipo de dato ```Formula```, tenemos los siguientes casos:

- Si ambas fórmulas son del tipo ```Verdadero``` o ```Falso```, la respuesta es trivial y devolvemos ```True```.
- Si ambas fórmulas son del tipo ```Predicado```, revisamos que el simbolo de predicado sea el mismo y que la lista de terminos en ambos sea la misma. En caso positivo, devolvemos ```True```, en otro caso, devolvemos ```False```. Este caso es la base que nos permitira resolver este problema para fórmula con cuantificadores.
- Si el operador principal de ambas funciones es la negación (```No```), son alfa equivalentes si las formulas no negadas son alfa equivalentes.
- Si el operador binario principal de ambas funciones es el mismo, en cada fórmula hay dos subfórmulas, digamos ```p_1``` y ```p_2``` para la primera fórmula, ```q_1``` y ```q_2``` para la segunda fórmula. Decimos que par original de fórmulas es alfa equivalente si ```p_1``` es alfa equivalente con ```q_1```, y además ```p_2``` es alfa equivalente con ```q_2```.
- Si ambas fórmulas tienen el mismo cuantificador (```ForAll``` o ```Exist```), entonces decimos que son alfa equivalentes si al sustituir la variable de ligado de la primer fórmula en la segunda fórmula, el resultado es una fórmula equivalente. Esto se complementa con la base de los predicados, pues si después de la suficientes llamadas recursivas se encuentra que los predicados son los mismos y tiene la misma lista de términos en el mismo orden, entonces podemos concluir la alfa equivalencia, de otro modo devolvemos ```False```.
- En cualquier otro caso recibimos formulas que no tienen el mismo operador principal, por lo que decimos que las formulas no son alfa equivalentes.

- Ejercicio 7. unifica :: Formula -> Formula -> Maybe Unificador
```
unifica :: Formula -> Formula -> Maybe Unificador
unifica f g = aux_unifica2 (aux_unifica f g) []


```
Esta función revisa si, dadas dos fórmulas de la lógica de primer orden, existe un unificador más general (umg). En caso positivo, devuelve el unificador de las formulas. En otro caso, simplemente regresa error. Para la implementación de esta función hacemos uso de una función auxiliar a la que llamamos ```aux_unifica2```.

- Auxiliar. aux_unifica :: Formula -> Formula -> Maybe [(Term,Term)]
```
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
```
Esta función auxiliar llamada `(aux_unifica)` trata de buscar un conjunto inicial de pares de términos que podrían ser unificados entre dos fórmulas de la lógica de primer orden donde se buscan la posibles substituciones que puedan hacer que las fórmulas equivalentes. Por consiguiente veamos su implementación.

#### Implementación:
Notemos que tenemos 3 casos generales:

- **Predicados**: Si ambas fórmulas son predicados con el mismo símbolo y la misma cantidad de términos, retorna un `Just` con los pares de términos correspondientes de ambas listas. Si los símbolos de los predicados o la cantidad de términos difieren, retorna `Nothing`.

- **Negación**: Aplica la unificación a las fórmulas dentro de los operadores de negación. Si una de las fórmulas internas no se puede unificar, la función también falla.

- **Conjunción, Disyunción, Implicación, Equivalencia**: Estos casos manejan operadores binarios donde se necesita que ambos pares de subfórmulas se unifiquen exitosamente. Si la unificación de alguna de las subfórmulas falla, entonces la función retorna `Nothing`. Si ambas subfórmulas se unifican correctamente, concatena las listas de pares de términos que resultan de cada subfórmula y retorna un `Just` de esta concatenación.

#### Casos Generales:
Si ninguna de las estructuras de los casos anteriores coincide, la función retorna `Nothing`, indicando que no existe unificación posible bajo las reglas definidas.

---

- Auxiliar. obtenerVariables :: Term -> [String]
```
obtenerVariables :: Term -> [String]
obtenerVariables (Var x) = [x]
obtenerVariables (Fun _ ts) = nub $ concatMap obtenerVariables ts


```
Esta función auxiliar recibe un termino de la lógica de primer orden y devulve una lista con las variables contenidas en el termino. Si el término es una variable, simplemente devuelve una lista que contiene esa variable. Si el término se trata de una función, analizamos de forma recursiva los términos en la lista ls de argumentos, concatenando las listas de variables libres resultantes y eliminando los posibles duplicados. Finalmente, ```concatMap libresEnTermino ls``` aplica ```obtenerVariables``` a cada elemento de ls y concatena todo.

- Auxiliar. aux_unifica2 :: Maybe [(Term,Term)] -> Unificador -> Maybe Unificador
```
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
```

Esta función está diseñada para realizar un proceso recursivo de unificación, ajustando un unificador existente o determinando que la unificación no es posible.

### Entrada y Parámetros
Recibe un `Maybe` que puede contener una lista de pares de términos, o `Nothing` si no hay términos a considerar.
También recibe una lista de sustituciones, donde cada sustitución es un par `(Simbolo, Term)` que indica cómo debe ser reemplazada una variable.

Tenemos varios casos:

- Si no hay términos para unificar regresamos `Nothing`.

- Si la lista de términos a unificar está vacía, se retorna el unificador actual (`sigma`) envuelto en `Just`, esto se refiere a que la unificación ha sido completada sin problemas.
Si los términos son dos variables (`Var x`, `Var y`):
     - Si `x == y`, simplemente se continúa con el resto de los términos (`xs`), manteniendo el unificador actual (`sigma`).
     - Si `x != y`, se crea una nueva sustitución donde `x` se sustituye por `y`, se ajusta el unificador actual con esta nueva sustitución y se aplica esta sustitución a todos los términos restantes antes de continuar con la recursión.

- Si se quiere unificar una variable y un término: el primer sub-caso es si el término `t` contiene la variable `x`, la unificación falla y retorna `Nothing` para evitar ciclos infinitos o auto-referencias; el segundo subcaso es si no contiene `x`, se procede a sustituir `x` por `t` en el unificador y en los términos restantes, y se sigue con la recursión.

La situción inversa del caso anterior: unificar un término y una variable. Se maneja de la misma manera pero ajustando la dirección de la sustitución.

- Si queremos unificar dos funciones, ambas tienen el mismo símbolo `f == g` y la misma cantidad de argumentos `length t1 == length t2`, se intenta unificar los argumentos de las funciones y se continua la unificación con los términos restantes. En caso de que los símbolos de las funciones o la cantidad de sus argumentos no coincidea, la unificación falla y devolvemos (`Nothing`).

- Ejercicio 8. resolvente :: Clausula -> Clausula -> Bool
```
resolvente :: Clausula -> Clausula -> Bool
resolvente c1 c2 =
    any esResolventePosible [(f1, f2) | f1 <- c1, f2 <- c2, isJust (comUnificables f1 f2)]
  where
    esResolventePosible (f1, f2) =
        case comUnificables f1 f2 of
          Just _ -> clausVacia c1 c2 f1 f2
          Nothing -> False

```
Funcion que dadas dos clausulas indica si son resolventes o no (Unificables y complementarias). Se reciben dos clausulas, de las cuales se obtiene una lista de pares que pueden ser unificables, mediante el uso de una lista por compresion y una funcion auxiliar `comUnificables`. Minetras que en la misma funcion se ayuda de `esResolventePosible` para saber si la tupla relamente puede ser resoluble, esto lo hace apoyandose en la funcion auxiliar `clausVacia`


- Auxiliar. comUnificables :: Formula -> Formula -> Maybe Unificador
```
comUnificables :: Formula -> Formula -> Maybe Unificador
comUnificables (Predicado p1 t1) (No (Predicado p2 t2)) | p1 == p2 = unifica (Predicado p1 t1) (Predicado p2 t2)
comUnificables (No (Predicado p1 t1)) (Predicado p2 t2) | p1 == p2 = unifica (Predicado p1 t1) (Predicado p2 t2)
comUnificables _ _ = Nothing
```

Funcion auxiliar que recibe dos formulas y devuelve un posible unificador. En los dos primero casos, la funcion verifica que el primer predicado y el segundo sean iguales para que puedan ser consideradas para unificacion, si los predicados son iguales y una fórmula es la negación de la otra, se procede a intentar unificar los términos. Posteriormente se indica que las fórmulas son unificables bajo las reglas de la lógica de predicados. En cualquier otro caso, devuelve un error


- Auxiliar. clausVacia :: Clausula -> Clausula -> Formula -> Formula -> Bool
```
clausVacia :: Clausula -> Clausula -> Formula -> Formula -> Bool
clausVacia c1 c2 f1 f2 =
    let aplicada1 = delete f1 c1
        aplicada2 = delete f2 c2
        var1 = concatMap libres aplicada1
        var2 = concatMap libres aplicada2
    in null (intersect var1 var2)

```
Funcion auxiliar que recibe dos clusulas, y dos formulas (pertenecientes a las clausulas respectivamente) y siguiendo un paso similiar al de la clausula vacia y asegura si las cláusulas resultantes de la resolución son independientes en términos de sus variables libres o no. Elimina las formulas `f1` y `f2` obtenidas de las clausulas, asi preparan las cláusulas para la verificación posterior, eliminando las fórmulas que, según la lógica de resolución, se "cancelarían" mutuamente debido a que son complementarias y unificables. Posteriormente a estas clausulas con `f1` y `f2`, les aplica la funcion para obtener sus variables libres. Finalmente comprueba si la intersección de estas listas obtenidas es vacía. Si es vacía, esto significa que no hay variables compartidas entre las cláusulas restantes después de eliminar f1 y f2.

- Ejercicio 9. resolucion :: Clausula -> Clausula -> Clausula
```
resolucion :: Clausula -> Clausula -> Clausula
resolucion c1 c2 =
    case find (\(f1, f2) -> esResoluble (f1, f2)) [(f1, f2) | f1 <- c1, f2 <- c2] of
      Just (f1, f2) -> delete f1 c1 ++ delete f2 c2
      Nothing       -> error "No hay resolvente "
  where
    esResoluble (Predicado p1 t1, No (Predicado p2 t2)) = p1 == p2 && isJust (unifica (Predicado p1 t1) (Predicado p2 t2))
    esResoluble (No (Predicado p1 t1), Predicado p2 t2) = p1 == p2 && isJust (unifica (Predicado p1 t1) (Predicado p2 t2))
    esResoluble _ = False

```
La función recibe dos cláusulas y regresa una nueva cláusula, llamada resolvente, mediante la aplicación de la regla de resolución binaria.

Utilizamos la función ```find``` para buscar el primer par de fórmulas ```(f1, f2)``` dentro de todas las combinaciones posibles de fórmulas de `c1` y `c2` donde esResoluble ```(f1, f2)``` nos devuelve `True`. 
Es decir, se busca un par de fórmulas donde una es la negación de la otra y son unificables.

Tenemos dos casos:

Si se encuentra tal par de fórmulas, eliminamos dichas de sus respectivas cláusulas y se combinan el resto de las fórmulas de ambas cláusulas para formar el resolvente.

Si no es posible encontrar algún par de fórmulas que cumplan con la condición de resolución, lanzamos un error indicando que no se encontró un resolvente.

Nuestra función auxiliar ```esResoluble``` verifica si un par de fórmulas son resolubles. Primero comprobamos si una fórmula es la negación de la otra y si ambas tienen el mismo predicado `p1 == p2`. Utilizamos la función ```unifica``` para verificar si los términos de las fórmulas pueden ser unificados. Si ```unifica``` devuelve un resultado (es decir, ```isJust``` devuelve `True`), entonces dichas fórmulas son resolubles.
