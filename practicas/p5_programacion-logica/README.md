## Práctica 5
- Integrantes:
  * Castillo Hernández Antonio          No. de Cuenta: 320017438
  * Juárez Cruz Joshua                  No. de Cuenta: 320124516
  * Luna Campos Emiliano                No. de Cuenta: 320292084
  * Vázquez Reyes Jesús Elías           No. de Cuenta: 320010549

## Ejercicios

- Ejercicio 1: Buen fin
```
articulo(pantalon).
articulo(chamarra).
articulo(sombrilla).

color(azul).
color(rojo).
color(amarillo).

descuento(10).
descuento(25).
descuento(50).

distintos(X,Y,Z) :- X \= Y, X \= Z, Y \= Z.

chamarra_azul(Articulo, _) :- Articulo \= chamarra.
chamarra_azul(chamarra, azul).

rojo_descuento(C, _, _, _) :- C \= rojo.
rojo_descuento(_, _, A, _) :- A \= sombrilla.
rojo_descuento(rojo, D1, sombrilla, D2) :- D1 > D2.

pantalon_descuento(Articulo,_) :- Articulo \= pantalon.
pantalon_descuento(pantalon, Descuento) :- Descuento \= 10.

tuplas(T1,T2,T3) :-
    T1 = t(curry, Articulo1, Color1, Descuento1),
    T2 = t(kleene, Articulo2, Color2, Descuento2),
    T3 = t(russell, Articulo3, Color3, Descuento3),
    articulo(Articulo1),
    articulo(Articulo2),
    articulo(Articulo3),
    color(Color1),
    color(Color2),
    color(Color3),
    descuento(Descuento1),
    descuento(Descuento2),
    descuento(Descuento3),
    distintos(Articulo1, Articulo2, Articulo3),
    distintos(Color1,Color2,Color3),
    distintos(Descuento1,Descuento2,Descuento3),
    chamarra_azul(Articulo1,Color1),
    chamarra_azul(Articulo2,Color2),
    chamarra_azul(Articulo3,Color3),
    Articulo1 \= chamarra,
    Descuento3 = 25,
    rojo_descuento(Color1, Descuento1, Articulo1, Descuento1),
    rojo_descuento(Color1, Descuento1, Articulo2, Descuento2),
    rojo_descuento(Color1, Descuento1, Articulo3, Descuento3),
    rojo_descuento(Color2, Descuento2, Articulo1, Descuento1),
    rojo_descuento(Color2, Descuento2, Articulo2, Descuento2),
    rojo_descuento(Color2, Descuento2, Articulo3, Descuento3),
    rojo_descuento(Color3, Descuento3, Articulo1, Descuento1),
    rojo_descuento(Color3, Descuento3, Articulo2, Descuento2),
    rojo_descuento(Color3, Descuento3, Articulo3, Descuento3),
    pantalon_descuento(Articulo1,Descuento1),
    pantalon_descuento(Articulo2,Descuento2),
    pantalon_descuento(Articulo3,Descuento3),
    Articulo1 \= pantalon,
    Articulo2 \= pantalon.

```
Ejercicio que modela el acertijo del primer inciso. Primero se define la base de conocimientos según el texto dado, se crean predicados para los artículos, los colores y los descuentos que fueron llevados comprados, además se crea una cláusula para que ni los articulos ni los colores o descuentos sean los mismos. Posteriormente se crean predicados para las cuatro pistas que se dan en el ejercicio, en este caso **chamarra_azul**,**rojo_descuento** y **pantalon_descuento**.

Ahora se define el predicado principal para resolver el ejercicio, que consta en dar tres tuplas (una por cada persona y sus compras). Se sigue poniendo predicados de la base de conocimientos **articulo**, **color**, **descuento**; y ahora el predicado para que sean distintos unos de otros. Leyendo las pistas se hacen dos restricciones, ya que la chamarra azul no es de la primera pista (Curry) y el descuento de *25%* se realizó en la tercera pista (Russell). Ahora se procede a hacer las posibles combinaciones de articulos y los predicados que definen las pistas, para **chamarra_azul** y **pantalon_descuento** se le pasan los tres articulos y los tres colores; **rojo_descuento** recibe todas las combinaciones de los tres articulos, los tres colores y los tres descuentos. Y finalmente una última restricción para los predicados es que los pantalones no fueron comprados por Curry ni Kleene.


- Ejercicio 2: Particion
```
particion(L1, L2, L3) :- length(L1, N),
                        Mitad is N // 2,  % División entera
                        auxiliar(L1, L2, L3, Mitad),
                        !.   

```

El predicado de `particion(L1, L2, L3)` divide una lista `L1` en dos partes, `L2` y `L3`. `L2` es la primera mitad de la lista, y `L3` es la segunda mitad. Si el número de elementos en `L1` es impar, `L2` tendrá un elemento más que `L3`.

El predicado principal utiliza la función `length` para determinar la longitud de la lista `L1` y divide este valor entre dos usando división entera. Asi mismo utiliza un predicado auxiliar `auxiliar` para distribuir los elementos en `L2` y `L3`.

- Función Auxiliar
```
auxiliar([], [], [], _).
auxiliar([X|XS], [X|L2], L3, N) :- N > 0, N1 is N - 1, auxiliar(XS, L2, L3, N1).
auxiliar([X|XS], L2, [X|L3], N) :- N = 0, auxiliar(XS, L2, L3, N).

```
Esta función Auxiliar maneja la particion de la lista `L1` en dos sublistas `L2` y `L3`.

- *Caso base:* Cuando la lista original está vacía (`[]`), las sublistas `L2` y `L3` también deben estar vacías ya que es facil ver que de `[]` solo queda `[]`.

- *Caso Recursivo 1:* Veamos que si `N > 0` estaremos en este caso. Por consiguiente se toma el elemento cabeza `X` de la lista original y lo coloca en la sublista `L2`. Luego, se decrementa `N` por uno (`N1 is N - 1`) y se hace una llamada recursiva con el resto de la lista (`XS`). Este proceso continúa hasta que `N` alcanza cero, llenando `L2` con los primeros `N` elementos de `L1`.

- *Caso Recursivo 2:* Una vez que `N` es igual a cero, estaremos en este otro caso. Por lo cual veamos que en este punto, todos los elementos subsiguientes en la lista original se agregan a `L3`. Aquí, `X` se añade a `L3`, y se hace una llamada recursiva con el resto de la lista (`XS`), manteniendo `L2` intacta y agregando a `L3`. Este proceso asegura que todos los elementos restantes después de llenar `L2` terminen en `L3`.

---

- Ejercicio 3: Combina
```
combina([], L, L).
combina(L, [], L).
combina([X|XS], [Y|YS], [X|L2]) :- X =< Y, combina(XS, [Y|YS], L2).
combina([X|XS], [Y|YS], [Y|L2]) :- X > Y, combina([X|XS], YS, L2).

```
La función recibe dos listas ordenadas de forma ascendente, y devuelve una tercera con los elementos ordenados de esas dos.

En el caso base se tiene una lista vacía y otra lista ```L``` cualquiera. Se regresa ésta última.

El segundo caso base es similar al anterior, pero se recibe primero una lista ```L``` cualquiera y luego la vacía. Devolvemos ```L``` nuevamnente.

El primer caso recursivo cotempla cuando ambas listas tienen elementos. Aquí se comparan los primeros elementos de ambas listas (```X``` y ```Y```). Si ```X``` es menor o igual que ```Y```, se agrega ```X``` a la lista resultante.
Luego, la función se llama recursivamente, con el resto de la primera lista (```XS```) y la segunda lista completa (```[Y|YS]```), fusionando así el resto de los elementos en ```L2```.

En el segundo caso recursivo, ambas listas tienen elementos pero ```X``` es mayor que ```Y```. En esta ocasión agregamos ```Y``` a la lista resultante. Luego, la función se llama recursivamente con la primera lista completa (```[X|XS]```) y el resto de la segunda lista (```YS```), fusionando así el resto de los elementos en ```L2```.

- Ejercicio 4: Máximo Común Divisor
```
gcd(X, Y, Z) :- Y > 0, Modulo is X mod Y, gcd(Y, Modulo, Z).

coprimos(X, Y) :- gcd(X, Y, GCD), GCD == 1.

```

La función ```gcd``` calcula el máximo común divisor de dos números dados. Seguimos la idea del Algoritmo de Euclides, donde sabemos que ```mcd(X, 0) = X``` y ```mcd(a,b) = mcd(b,a%b)```, con % siendo la operación módulo (mod).

Así, sabemos que ```Z``` es MDC de ```X``` y ```Y``` si y solo si ```Z``` es MCD de ```Y``` y ```X%Y```.

La función ```coprimos``` verifica si dos números son primos relativos, es decir, su máximo común divisor es 1. Para ello, se usa la función ```gcd``` con el fin de verificar que el MCD de ```X``` y ```Y``` sea 1.

- Ejercicio 5: Agrupación
```
agrupa([],[]).
agrupa([E],[[E]]).
agrupa([X,Y|XS], [[X|L1]|L2]) :- X==Y, agrupa([Y|XS], [L1|L2]).
agrupa([X,Y|XS], [[X]|L2]) :- X\=Y, agrupa([Y|XS], L2).

```
Predicado que recibe una lista de elementos, y devuelve una lista de listas. Si recibe una lista vacia trivialmente devuelve una lista vacia. Si recibe una lista de un solo elemento devuelve una lista con la lista unitaria del elemento. En otro caso toma los dos primeros elementos de la lista son iguales agrega el primer elemento a una lista, la concatena a la lista de listas y hace recursion sobre el siguiente sobre la lista en la que ya no estan los primeros elementos. Si los dos primeros elementos no son iguales deja una lista con el primer elemento y hace resursion sobre el siguiente.


- Ejercicio 6: Pertenencia
```
pertenece(E,[E|_]).
pertenece(E,[_|XS]) :- pertenece(E,XS).

```
La función determina si un elemento pertenece a un lista dada. 

La regla del caso base nos indica que, dado un elemento ```E``` y una lista con dicho elemento como cabeza, se devuelve ```true```. No nos importa la cola de la lista.

En la segunda regla de inferencia, se analiza el caso donde el elemento E no es la cabeza de la lista inicial. Se llama recursivamente la función para comprobar si ```E``` está presente en la cola de la lista, y si es así, se devuelve ```true```.

- Ejercicio 7: Elimina
```
elimina(_,[],[]).
elimina(X,[X|XS],XS).
elimina(A,[X|XS],[X|YS]) :- elimina(A,XS,YS).

```
La función elimina un elemento de una lista dada.

La primer regla contempla el caso donde se recibe una lista vacía. Dado que la lista no posee elemento alguno, devolvemos la misma.


La segunda regla indica que, si el elemento a eliminar es la cabeza de la lista parámetro, se devuelve la cola de dicha lista.

La tercer regla analiza cuando el elemento```A``` no es la cabeza de la lista parámetro. En este caso, se requiere una llamada recursiva donde se busca la presencia de ```A``` en la cola ```XS```, si encontramos el elemento, devolvemos ```YS``` (```XS``` sin ```A```), si no, se analiza al resto de elementos.

- Ejercicio 8: Caminos
```
% Base de conocimientos con las puertas entre cuartos
puerta(a, b).
puerta(b, a).
puerta(b, c).
puerta(b, e).
puerta(c, b).
puerta(c, d).
puerta(d, c).
puerta(d, e).
puerta(e, d).
puerta(e, b).
puerta(e, f).
puerta(e, g).
puerta(g, e).

camino(X, Y, XS) :-
    camino_aux(X, Y, [X], XS).

```
En esta función se trata de abordar el problema de encontrar todos los caminos posibles entre dos cuartos en un sistema de cuartos interconectados por puertas.

**Implementación:**
Veamos que el predicado principal `camino(X, Y, XS)` inicia la búsqueda de caminos desde el cuarto `X` hasta el cuarto `Y`, donde `XS` será la lista que contendrá el camino encontrado. La lógica de búsqueda está implementada en el predicado auxiliar `camino_aux`.


- Auxiliar de Camino

```
camino_aux(Y, Y, V, XS) :-
    reverse(V, XS).

camino_aux(X, Y, V, XS) :-
    puerta(X, N),
    \+ pertenece(N, V), 
    camino_aux(N, Y, [N|V], XS).

```
En esta función notemos algunos puntos importantes:

**Argumentos:**
- **`X`**: El cuarto actual desde el que se está buscando un camino.
- **`Y`**: El destino final del camino que se desea encontrar.
- **`V`**: La lista de cuartos que ya han sido visitados en el camino actual. Esta lista es crucial para evitar ciclos y repetir visitas a los mismos cuartos.
- **`XS`**: La variable que eventualmente contendrá el camino encontrado desde `X` hasta `Y`.

**Casos:**

1. **Caso Base (`camino_aux(Y, Y, V, XS)`):**
   - **Cuando el cuarto actual `X` es igual al destino `Y`**, esto indica que se ha encontrado un camino válido desde el cuarto inicial hasta `Y`.
   - **`reverse(V, XS)`**: La lista de visitados `V` se invierte para convertirla en el camino correcto desde el inicio hasta el fin. Esto es porque `V` se construye añadiendo elementos al principio de la lista, lo que significa que el orden de los cuartos está invertido respecto al camino real.

2. **Caso Recursivo (`camino_aux(X, Y, V, XS)`):**
   - **`puerta(X, N)`**: En esta parte se busca una puerta que conecte el cuarto actual `X` con otro cuarto `N`.Por lo cual este paso explora las conexiones disponibles desde `X`.

   - **`\+ pertenece(N, V)`**: Aquí verificamos que el cuarto `N` no esté ya en la lista de visitados `V`.

   - **Recursividad **: Si `N` no ha sido visitado, se hace una llamada recursiva a `camino_aux` con `N` como el nuevo cuarto actual, `[N|V]` como la nueva lista de visitados (añadiendo `N` al principio de `V`), y `XS` como la variable que sigue almacenando el camino.

    Este proceso se repite hasta que se encuentre el destino `Y` o hasta que se agoten las opciones.
