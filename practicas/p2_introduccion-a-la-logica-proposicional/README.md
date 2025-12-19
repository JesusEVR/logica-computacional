## Práctica 2
- Integrantes:
  * Joshua Juárez Cruz                  No. de Cuenta: 320124516
  * Antonio Castillo Hernández          No. de Cuenta: 320017438
  * Emiliano Luna Campos                No. de Cuenta: 320292084
  * Jesús Elías Vázquez Reyes           No. de Cuenta: 320010549

## Ejercicios:
- Ejercicio 1. instance Show Prop where
```
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

```
Esta funcion da una cadena que muestra la proposicion en notacion infija, se definen ocho posibles casos. Primero los "triviales", que constan de las constantes, la variable atomica, y la misma con su negacion. Y despues las compuestas con las cuales se hace uso de la recursion, se muestra la formula y se muestra la funcion de de las proposiciones que la componen.
 
- Ejercicio 2. conjPotencia :: [a] -> [[a]]

```
conjPotencia :: [a] -> [[a]]
conjPotencia []=[[]]
conjPotencia (x:xs)=  map (x:) aux ++ aux
          where aux = conjPotencia xs
```
Funcion que da todos los posibles subconjuntos de uno dado. Dividida principalmente en dos casos, en caso de que se de la lista vacia, devolvemos una lista con unicamente la lista vacia. En otro caso, se divide la lista entre el primer elemento y el resto, este ultimo pasa a recursion, mientras que el elemento obtenido primeramente se concatena al resultado de la misma recursion. 

- Ejercicio 3. vars :: Prop -> [String]

```
vars :: Prop -> [String]
vars T = []
vars F = []
vars (Var p) = [p]
vars (Neg prop) = vars prop
vars (Conj phi psi) = nub (vars phi ++ vars psi)
vars (Disy phi psi) = nub (vars phi ++ vars psi)
vars (Impl phi psi) = nub (vars phi ++ vars psi)
vars (Equiv phi psi) = nub (vars phi ++ vars psi)

```
Dada una formula de la lógica proposicional, esta función devuelve una lista con las variables involucradas en dicha formula. Para lograr esto tenemos casos: 

BASE: En los casos base tenemos a las constantes lógicas (```T``` y ```F```) y las fórmulas atómicas o variables proposicionales (```Var p```), si la proposición del argumento es una constante lógica, entonces la lista que se devuelve es vacía (```[]```). Por otro lado, si se trata de una formula atómica se devuelve la lista con esta fórmurla (```[p]```).

RECURSIÓN: El primer caso destacable es el del operador unario de la negación (```Neg prop```), en el cual simplemente hacemos recursión sobre la fórmula dentro de la negación.

Luego, para cualquier operador binario (```Conj```, ```Disy```, etc) hacemos recursión para buscar las variables en las fórmulas lógicas involucrados en la operación.

- Ejercicio 4. interpretacion :: Prop -> Estado -> Bool

```
interpretacion :: Prop -> Estado -> Bool
interpretacion (Var p) e = if (p `elem` e) then True else False
interpretacion T _ = True
interpretacion F _ = False
interpretacion (Neg prop) estado = not (interpretacion prop estado == True)
interpretacion (Conj p q) e = interpretacion p e && interpretacion q e
interpretacion (Disy p q) e = interpretacion p e || interpretacion q e
interpretacion (Impl p q) e = interpretacion (Disy (Neg p) q ) e
interpretacion (Equiv p q) e = interpretacion p e == interpretacion q e
```

Esta función se encarga de evaluar una proposición lógica con un estado dado. Si la proposición es una variable, verifica si está en el estado de verdadero o falso. Para constantes `T` y `F`, devuelve `True` y `False` que son los casos de Top y Botton. Luego maneja los demas casos para las operaciones lógicas como la negación (`Neg`), conjunción (`Conj`), disyunción (`Disy`), implicación (`Impl`) y equivalencia (`Equiv`) aplicando recursivamente la interpretación a sus subcomponentes segun sea el caso. Para esto además nos apoyamos de los operadores ya definidos por Haskell pues, por ejemplo, la interpretación de una conjunción (```Conj```) solo puede ser ```True``` si la interpretación de las fórmulas sobre las que se aplica la conjunción son ```True```, para verificar esto usamos el operador ```&&``` ya definido en Haskell.

- Ejercicio 5. modelos :: Prop -> [Estado]

```
modelos :: Prop -> [Estado]
modelos p = [e | e <- conjPotencia (vars p), interpretacion p e == True]

```
Esta función se encarga de devolver una lista con todos los estados que satisfacen a una fórmula de la lógica proposicional. Para nuestra implementación hacemos uso de la definción de una lista por comprensión.

En general, decimos que para cualquier fórmula ```p``` de ```PROP```, su lista de modelos será la lista de todos los posibles estados tales que su interpretación es ```True```. Es decir, en la definición de nuestra lista nos encargamos de encontrar todos los posibles estados que puedan tener las variables de la fórmula mediante la función de ```conjPotencia```, aplicada sobre las variables de ```p```, y después usamos la fucnión ```interpretacion``` sobre ```p``` y cada estado ```e```, si alguno es ```True```, entonces lo guardamos dentro de nuestra lista de modelos, si no se descarta.

- Ejercicio 6. tautologia :: Prop -> Bool

```
tautologia :: Prop -> Bool
tautologia T = True
tautologia F = False
tautologia p = if False `elem` [interpretacion p e | e <- conjPotencia (vars p)] then False else True

```
Para nuestra la implementación de nuestra función tenemos diferentes casos:

Si la fórmula que se pasa como argumento es ```T```, entonces trivialmente es una tautología. Si es ```F```, entonces no puede ser tautologia, pues tiene valor de verdad ```False```. En el ultimo caso, para cualquier otra fórmula de la lógica proposicional, definimos una lista por comprensión, la cual es la lista de todos las interpretación de la fórmula ```p``` con cada posible conjunto de estados que pueda tener. Revisamos si en esta lista se encuentra el valor ```False```, en caso  afirmativo significaría que existe un conjunto de estados para los cuales la fórmula ```p``` no es ```True```, por lo tanto no puede ser una tautologia y devolvemos el valor ```False```. De otra forma, si dicho valor ```False``` no se encuentra nunca, podemos concluir que ```p``` es, en efecto, una tautologia.

- Ejercicio 7. contradiccion :: Prop -> Bool

```
contradiccion :: Prop -> Bool
contradiccion T = False
contradiccion F = True
contradiccion p = if True `elem` [interpretacion p e | e <- conjPotencia (vars p)] then False else True

```
Si la fórmula que se pasa como argumento es ```T```, entonces no puede ser una contradicción, ya que siempre tiene valor de verdad ```True```. Si es ```F```, entonces es, trivialmente, una contradicción. En el ultimo caso, para cualquier otra fórmula ```p``` de la lógica proposicional, definimos una lista por comprensión igual a como lo hicimos en la función pasada, con la difernecias de que ahora revisamos si en esta lista se encuentra el valor ```True```, en caso  afirmativo significaría que existe un conjunto de estados para los cuales la fórmula ```p``` es ```True```, por lo tanto no puede ser una contradicción y devolvemos el valor ```False```. De otra forma, si dicho valor ```True``` no se encuentra nunca, podemos concluir que ```p``` es, en efecto, una contradicción y devolvemos ```True```.

- Ejercicio 8. esSatisfacible :: Prop -> Bool

```
esSatisfacible :: Prop -> Bool
esSatisfacible T = True
esSatisfacible F = False
esSatisfacible p = True `elem` [interpretacion p e | e <- conjPotencia (vars p)]

```
Esta función sirve para determinar si una proposición lógica es satisfacible. Maneja los casos de Top y Botton y además para otras proposiciones, evalúa si al menos una interpretación de la proposición es `True` sobre todos las posibles interpretaciones generadas por el conjunto potencia de sus variables.

- Ejercicio 9. deMorgan :: Prop -> Prop

```
deMorgan :: Prop -> Prop
deMorgan T = T
deMorgan F = F
deMorgan (Var p) = Var p
deMorgan :: Prop -> Prop
deMorgan (Neg (Neg p)) = deMorgan p
deMorgan (Neg (Conj p q)) = Disy (deMorgan (Neg p)) (deMorgan (Neg q))
deMorgan (Neg (Disy p q)) = Conj (deMorgan (Neg p)) (deMorgan (Neg q))
deMorgan (Conj p q) = Conj (deMorgan p) (deMorgan q)
deMorgan (Disy p q) = Disy (deMorgan p) (deMorgan q)
deMorgan (Impl p q) = Impl (deMorgan p) (deMorgan q)
deMorgan (Equiv p q) = Equiv (deMorgan p) (deMorgan q)
deMorgan (Neg p) = Neg (deMorgan p)
```

La función toma como argumento una proposición lógica y devuelve otro argumento del mismo tipo. Maneja los casos base de Top, Bottom y una variable proposicional, devolviendo el mismo dato sin cambios.
En el tercer caso devuelve el De Morgan de una negación: la proposición original.
Los siguientes dos casos son los principales de la ley, donde la negación de una conjunción (`Conj`) es equivalente a la disyunción (`Disy`) de las negaciones de cada proposición, y la negación de una disyunción (Disy) es equivalente a la conjunción (`Conj`) de las negaciones. Finalmente se aplica la función a las negaciones de las proposiciones.
Los últimos casos son manejados de forma similar, donde se usan operadores binarios y la negación. Se mantiene la estructura original mientras se aplica la función a cada proposición.

- Ejercicio 10. elimImplicacion :: Prop -> Prop
```
elimImplicacion :: Prop -> Prop
elimImplicacion T = T
elimImplicacion F = F
elimImplicacion (Var p) = Var p
elimImplicacion :: Prop -> Prop
elimImplicacion (Impl p q) = Disy (Neg (elimImplicacion p)) (elimImplicacion q)
elimImplicacion (Neg p) = Neg (elimImplicacion p)
elimImplicacion (Conj p q) = Conj (elimImplicacion p) (elimImplicacion q)
elimImplicacion (Disy p q) = Disy (elimImplicacion p) (elimImplicacion q)
elimImplicacion (Equiv p q) = Equiv (elimImplicacion p) (elimImplicacion q)
```
La función toma como argumento una proposición lógica y devuelve otro argumento del mismo tipo. Maneja los casos base de Top, Bottom y una variable proposicional, devolviendo el mismo dato sin cambios.
En el tercer caso se elimina el operador de implicación, realizando una equivalencia en su lugar: la implicación (`Impl`) de p y q es igual a la disyunción (`disy`) de la negación de p, con q. Después de aplica la función a cada proposición.
Los últimos casos son manejados de forma similar, donde se usan otros operadores binarios y la negación. Se mantiene la estructura original mientras se aplica la función a cada proposición.

- Ejercicio 11. elimEquivalencias :: Prop -> Prop
```
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
```
La función toma como argumento una proposición lógica y devuelve otro argumento del mismo tipo. Maneja los casos base de Top, Bottom y una variable proposicional, devolviendo el mismo dato sin cambios.
En el tercer caso se elimina el operador de equivalencia, reemplazándola por: la equivalencia (`Equiv`) de p y q es igual a la conjunción (`conj`) de la implicación (`Impl`) de p con q, y la implicación (`Impl`) de q con p. Después de aplica la función de elimImplicación a cada componente de la conjunción.
Los últimos casos son manejados de forma similar, donde se usan otros operadores binarios. Se mantiene la estructura original mientras se aplica la función a cada proposición.

