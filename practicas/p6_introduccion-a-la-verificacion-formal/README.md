## Práctica 6
- Integrantes:
  * Castillo Hernández Antonio         No. de Cuenta: 320017438
  * Juárez Cruz Joshua                 No. de Cuenta: 320124516
  * Luna Campos Emiliano               No. de Cuenta: 320292084
  * Vázquez Reyes Jesús Elías          No. de Cuenta: 320010549

## Ejercicios:

### Ejercicio 1.
*Demuestra: (p → q → r) ⇔ (p ∧ q) → r*

```coq
Lemma imp_conj : 
  forall P Q R: Prop, (P -> Q -> R) <-> (P /\ Q -> R).
Proof.
  intros P Q R.
  split.
  + intros PimpQimpR PandQ.
    apply PimpQimpR.
    apply PandQ.
    apply PandQ.
  + intros PandQimpR evP evQ.
    apply PandQimpR.
    split.
    apply evP.
    apply evQ.
Qed.
```
**Explicación**:
En este ejercicio, se está demostrando una equivalencia lógica. La equivalencia dice que una implicación anidada `(P -> Q -> R)` es lógicamente equivalente a una implicación con una conjunción en el antecedente `(P /\ Q) -> R`.

Primero, se dividen los dos lados de la equivalencia usando `split`. En la primera dirección, se asume `(P -> Q -> R)` y `(P /\ Q)`, y se demuestra que `R` sigue de estos. Esto se hace aplicando la implicación `(P -> Q -> R)` a las partes de `(P /\ Q)`. En la segunda dirección, se asume `(P /\ Q -> R)` y se demuestra que `R` sigue de `P` y `Q` aplicando la implicación con la conjunción.

### Ejercicio 2.

*Demuestra: (p → q) → (q → r) → (p → r)*

```coq
Lemma imp_trans : 
  forall P Q R : Prop, (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros P Q R.
  intros PimpQ QimpR evP.
  apply QimpR.
  apply PimpQ.
  apply evP.
Qed.
```
**Explicación**:
Este ejercicio demuestra la transitividad de la implicación lógica. Por ejemplo, si `P` implica `Q` y `Q` implica `R`, entonces `P` implica `R`.

Primero, se introducen las hipótesis `(P -> Q)`, `(Q -> R)` y `P`. Luego, se aplica `P -> Q` a `P` para obtener `Q`, y finalmente se aplica `Q -> R` a `Q` para obtener `R`. Así, se concluye que `P` implica `R`.

### Ejercicio 3.

*Demuestra (p ∨ q) ∧ ¬p → q*

```coq
Lemma or_and_not : 
  forall P Q : Prop, (P \/ Q) /\ ~P -> Q.
Proof.
  intros P Q.
  intros Hip.
  destruct Hip as [PorQ notP].
  destruct PorQ as [Pholds | Qholds].
  - contradiction.
  - apply Qholds.
Qed.
```
**Explicación**:
Aca se trata de probar la equivalencia lógica de:  `(P \/ Q) /\ ~P`, entonces `Q`. 

Primero, se descompone la hipótesis en `(P \/ Q)` y `~P`. Luego, se analiza `(P \/ Q)`. Si `P` es verdadero, tenemos una contradicción con `~P`, lo cual se maneja con `contradiction`. Si `Q` es verdadero, entonces podemos concluir directamente `Q`.

### Ejercicio 4.
*Demuestra ¬(p ∨ q) ⇔ (¬p ∧ ¬q)*

```coq
Lemma deMorgan : 
  forall P Q : Prop, ~(P \/ Q) <-> (~P /\ ~Q).
Proof.
  unfold not.
  intros P Q.
  split.
  + intros PorQimpF.
    split.
    - intros evP. apply PorQimpF. left. apply evP.
    - intros evQ. apply PorQimpF. right. apply evQ.
  + intros PimpFandQimpF PorQ.
    destruct PimpFandQimpF as [PimpFHolds QimpFHolds].
    destruct PorQ as [Pholds | Qholds].
    - apply PimpFHolds. apply Pholds.
    - apply QimpFHolds. apply Qholds.
Qed.
```
**Explicación**:
Aquí se está demostrando una de las leyes de De Morgan, que dice que la negación de una disyunción es equivalente a la conjunción de las negaciones.

Se expande la definición de `not` usando `unfold not`. Luego, la prueba se divide en dos direcciones. En la primera dirección, se muestra que `~(P \/ Q)` implica `~P` y `~Q`, y en la segunda dirección, se muestra que `~P` y `~Q` implica `~(P \/ Q)`.

### Ejercicio 5. 

*Demuestra ∀n∈N, n + 1 = S(n)*

```coq
Lemma suma_suc :
  forall n : nat, n + 1 = S n.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.
```
**Explicación**:
Este lemma nos dice que sumar uno a un número natural `n` es equivalente a aplicar el sucesor `S` a `n`.

La prueba se realiza por inducción sobre `n`. En el caso base, `0 + 1 = 1` se resuelve directamente con `reflexivity`. En el caso inductivo, asumimos que `n' + 1 = S n'` y demostramos que `S n' + 1 = S (S n')` usando la hipótesis de inducción y simplificación.

### Ejercicio 6. 

*Demuestra ∀n,m∈N, n + m = m + n*

```coq
Lemma suma_conm :
  forall n m : nat, n + m = m + n.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - simpl.
    rewrite -> neutro_der.
    reflexivity.
  - simpl.
    rewrite -> IHn'.
    rewrite <- suma_der.
    reflexivity.
Qed.
```
**Explicación:**
El lema estipula la conmutatividad de la suma de naturales. Se procede por inducción sobre `n`.

En el caso base tenemos `0 + m = m + 0`. Simplificando, y por el teorema auxiliar `neutro_der` nos queda `m = m`. 

Suponemos verdadera la HI: `n' + m = m + n'`.

En el paso inductivo tenemos `S n' + m = m + S n'`, simplificando queda `S (n' + m) = m + S n'`. Usando la hipótesis hacia la izquierda tenemos `S (m + n') = m + S n'`, y por el teorema auxiliar `suma_ der`: `m + S n' = m + S n'`, que es lo que queríamos demostrar.

- Teorema auxiliar.

*∀n∈N, n + 0 = n*
```coq
Theorem neutro_der : forall n:nat, n + 0 = n.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl.
    rewrite -> IHn'.
    reflexivity.
Qed. 
```
**Explicación:**
Teorema auxiliar del neutro derecho en la suma de naturales. Se desmuestra a partir de inducción sobre `n`.

En el caso base tenemos `0 + 0 = 0`, solo basta usar `reflexivity`. 

Suponemos verdadera la `HI: n' + 0 = n'`.

En el paso inductivo tenemos `S n' + 0 = S n'`, simplificando y usando la hipótesis de inducción llegamos a lo que se desea demostrar.

- Teorema auxiliar.

*∀n,m∈N, n + S(m) = S(n + m)*
```coq
Theorem suma_der : forall n m:nat, n + S(m) = S(n + m).
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl.
    rewrite <- IHn'.
    reflexivity.
Qed.
```
**Explicación:**
El teorema auxiliar estipula la propiedad de que, un número `n` más el sucesor de otro número `m`, es igual al sucesor de la suma de `n y m`. Se desmuestra a partir de una inducción sobre `n`.

En el caso base tenemos `0 + S m = S (0 + m)`. Simplificando nos queda `S m = S m`, por lo que usando `reflexivity` se finaliza este primer paso.

Suponemos verdadera la `HI: n' + S m = S (n' + m)`.

En el paso inductivo tenemos `S n' + S m = S (S n' + m)`, usando la hipótesis de inducción hacia la izquierda, tenemos `S (n' + S m) = S (n' + S m)`. Finalmente, se aplica `reflexivity` y se demuestra el teorema.

### Ejercicio 7. 

*Demuestra ∀n,m,p∈N, p·(n + m) = p·n + p·m*
```coq
Lemma mult_dist :
  forall n m p : nat, p * (n + m) = p * n + p * m.
Proof.
  intros n m p.
  induction n as [| n' IHn'].
  - rewrite -> mult_0_der.
    simpl.
    reflexivity.
  - simpl.
    rewrite <- mult_der.
    rewrite -> IHn'.
    rewrite <- mult_der.
    assert (H: p*m + p = p + p * m).
    {
      rewrite <- suma_conm.
      reflexivity.
    }
    rewrite -> suma_asoc.
    rewrite H.
    rewrite <- suma_asoc.
    reflexivity.
Qed.
```
**Explicación:**
El lema espitula la distributividad de la multiplicación sobre la suma, en los naturales. Se demuestra por inducción sobre `n`.

En el caso base usamos el teorema auxiliar mult_0_der para simplificar `p * (0 + m) = p * 0 + p * m`, resultando en: `p * (0 + m) = 0 + p * m`. Simplificando obtenemos: `p * m = p * m`, como ambos lados son iguales, se concluye con `reflexivity`.

La hipoótesis de inducción es `p * (n' + m) = p * n' + p * m`.

En el paso inductivo simplificamos la expresión `p * (S n' + m) = p * S n' + p * m`, para después aplicar el teorema axuciliar `mul_der` hacia la derecha: `p * (n' + m) + p = p * S n' + p * m`.

Por la hipótesis: `p * n' + p * m + p = p * S n' + p * m`, usando el teorema auxiliar `mul_der` nos queda: `p * n' + p * m + p = p * n' + p + p * m`.

Establecemos una función auxiliar `H` (a partir de `suma_conm`) para reordenar los términos en la suma. Usamos la asociatividad de la suma (`suma_asoc`) para agrupar los términos correctamente y finalizar la demostración con `reflexivity`.

- Teorema auxiliar

*∀n∈N, n * 0 = 0*

```coq
Theorem mult_0_der:
  forall n : nat, n * 0 = 0.
Proof.
  intros n.
  induction n as [| n' HIn'].
  - reflexivity.
  - simpl.
    rewrite -> HIn'.
    reflexivity.
Qed.
```
**Explicación:**
Teorema auxiliar de la multiplicación por cero en los naturales. Procedemos por inducción sobre `n`.

En el caso base tenemos `0 * 0 = 0`. Simplificamos con `reflexivity`.

La hipótesis de inducción es `n' * 0 = 0`.

En el paso inductivo tenemos `S n' * 0 = 0`, simplificando nos queda `n' * 0 = 0`. Aplicamos la HI para tener `0 = 0` y usamos `reflexivity` para concluir.

- Teorema auxiliar

*∀x,y,z∈N, (x + y) + z = x + (y + z)*
  
```coq
Theorem suma_asoc:
  forall x y z : nat, (x + y) + z = x + (y + z).
Proof.
  intros x y z.
  induction x as [| x' IHx'].
  - reflexivity.
  - simpl.
    rewrite <- IHx'.
    reflexivity.
Qed.
```
**Explicación:**
Teorema auxiliar que estipula la asociatividad en la suma de naturales. Se demuestra por inducción sobre `x`.

En el caso base tenemos `0 + y + z = 0 + (y + z)`. Basta con usar `reflexivity` para simplificar y obtener lo mismo de ambos de la igualdad.

La hipótesis de inducción es `x' + y + z = x' + (y + z)`.

En el paso inductivo simplificamos para obtener `S (x' + y + z) = S (x' + (y + z))`. Aplicamos la hipótesis hacia la izquierda y se finaliza con `reflexivity`.

- Teorema auxiliar

*∀n,m∈N, n * m + n = n * S m*

```coq
Theorem mult_der:
  forall n m : nat, n * m + n = n * S m.
Proof.
  intros n m.
  induction n.
  - simpl. reflexivity.
  - simpl.
    rewrite -> suma_conm.
    rewrite <- IHn.
    simpl.
    rewrite -> suma_conm.
    rewrite -> suma_asoc.
    reflexivity.
Qed.
```
**Explicación:**
Teorema auxiliar que nos dice que la multiplicación de `n * m + n` es equivalente al producto de `n` y el sucesor de `m`. Se demuestra por inducción sobre `n` (qué sorpresa).

En el caso base tenemos `0 * m + 0 = 0 * S m`. Simplificando nos queda `0 = 0`. Usamos reflexivity para terminar.

La hipótesis de inducción es `S n * m + S n = S n * S m`.

En el paso inducitvo simplificamos para obtener `m + n * m + S n = S (m + n * S m)`. Por el lema `suma_conm` (ejercicio 6): `S n + (m + n * m) = S (m + n * S m)`, después aplicamos la hipótesis y tenemos `S n + (m + n * m) = S (m + (n * m + n))`.

Simplificando: `S (n + (m + n * m)) = S (m + (n * m + n))`; por `suma_conm` nos queda `S (m + n * m + n) = S (m + (n * m + n))`. Finalmente aplicamos el teorema auxiliar `suma_asoc`: `S (m + (n * m + n)) = S (m + (n * m + n))`.

### Ejercicio 8. 

*Implementa de manera recursiva una función que calcule la suma de todos los números naturales hasta n.*
```coq
Fixpoint gauss (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => S n' + gauss n'
  end.
```
**Explicación:**
Se hace un `match` en `n`. 

En caso de que el parámetro `n` de la función sea 0, se devuelve 0.

En caso de que el parámetro tenga la forma `S n'`, sumamos el número recibido y la función aplicada al predecesor de éste. La función llegará, en algún momento, al caso donde el parámetro de `gauss` sea 0, ahí la función comenzará a devolver los valores solicitados anteriormenete, mientras los va sumando.

### Ejercicio 9. 

*Demuestra que tu implementación de `gauss` cumple que ∀n∈N, 2·gauss(n) = n·(n + 1).*

```coq
Lemma gauss_eq :
  forall n : nat, 2 * gauss n = n * (n + 1).
Proof.
  intros n.
  induction n.
  - simpl. reflexivity.
  - simpl gauss. replace (S (n + gauss n)) with (S n + gauss n).
    + rewrite -> (mult_dist (S n) (gauss n)).
      rewrite -> IHn.
      simpl.
      rewrite -> neutro_der.
      rewrite -> (comm_mult n (S (n + 1))).
      simpl.
      rewrite -> suma_suc.
      rewrite <- (suma_asoc (S n) n (S n * n)).
      rewrite -> (suma_conm n (S n)).
      rewrite -> (comm_mult n (S n)).
      reflexivity.
    + simpl. reflexivity.
Qed.
```
La demostración procede por inducción sobre `n`.

En el caso base la fórmula se verifica trivialmente, pues `2 * gauss(0)` es `0` y `0·(0 + 1)` también es `0`. Basta con usar `simpl` y `reflexivity`.

En la hipótesis de inducción, se supone que la fórmula es verdadera para un `n` arbitrario, es decir: `2 * gauss(n) = n * (n+1)`.

En el paso inductivo primero simplificamos la expresión, después `replace` reemplaza `(S (n + gauss n))` con `(S n + gauss n)`, y así se generan 2 sub-casos.

En el subcaso 1 tenemos `2 * (S n + gauss n) = S n * (S n + 1)`, y por el ejercicio 7 `(mul_dist)` nos queda `2 * S n + 2 * gauss n = S n * (S n + 1)`.

Aplicando la hipótesis de inducción y simplificando obtenemos `S (n + S n + n * (n + 1)) = S (n + 1 + n * S (n + 1))`. Aquí usamos el teorema auxiliar `conm_mult` definido en el ejercicio 9, después simplificamos: `S (n + S n + n * (n + 1)) = S (n + 1 + (n + (n + 1) * n))`.

Reemplazamos los `n + 1` con `S n` y luego aplicamos el teorema auxiliar `suma_asoc` para manipular la expresión, de forma que podamos eliminar paréntesis innecesarios. Finalmente, se usa la conmutatividad de la suma para mover términos del lado izquierdo, de tal forma que solo resta usar `reflexivity` para concluir el sub-caso 1.

El sub-caso 2 es bastante sencillo, dado que tenemos `S n + gauss n = S (n + gauss n)` solo es necesario usar `simpl` para que el sucesor del lado izquierdo afecte a toda la expresión antes del signo igual. Se concluye con `reflexivity`.

- Teorema auxiliar

*n * m = m * n*
```coq
Lemma comm_mult :
  forall n m : nat, n * m = m * n.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - (* Caso base: n = 0 *)
    simpl.
    rewrite -> mult_0_der.
    reflexivity.
  - (* Caso inductivo: n = S n' *)
    simpl.
    rewrite -> IHn'.
    rewrite <- mult_der.
    rewrite -> suma_conm.
    reflexivity.
Qed.
```
**Explicación:**
Teorema auxiliar que estipula la conmutatividad en la multiplicación. Se demuestra por inducción sobre `n`.

En el caso base primero simplificamos la expresión `0 * m = m * 0`, obteniendo `0 = m * 0`. Así, el teorema auxiliar `mult_0_der` hace el trabajo restante para usar `reflexivity` en el resultado `0 = 0`.

En la hipótesis de inducción, se supone que la fórmula es verdadera para un `n'` arbitrario, es decir: `n' * m = m * n'`.

En el paso inductivo se busca demostrar `S n' * m = m * S n'`. Tras simplificar, podemos usar la hipóteis para hacer una sustitución: `m + m * n' = m * S n'`.

Hacemos uso del teorema auxiliar `mult_der`: `m + m * n' = m * n' + m`. Posteriormente, solo resta utilizar la conmutatividad de la suma para ser capaces de concluir con `reflexivity`.

### Ejercicio 10.

*Demuestra que la operación de concatenación es asociativa en listas.*

```coq
Lemma concat_assoc :
  forall (A : Type) (xs ys zs : list A), xs ++ ys ++ zs = (xs ++ ys) ++ zs.
Proof.
  intros A xs ys zs.
  induction xs as [| x xs' IHxs'].
  - simpl.
    reflexivity.
  - simpl.
    rewrite -> IHxs'.
    reflexivity.
Qed.
```
**Explicación:**
El lema estipula la asociatividad de la concatenación de listas. Se demuestra con inducción sobre la lista `xs`.


El caso base es cuando xs es vacía, entonces tenemos: `nil ++ ys ++ zs = (nil ++ ys) ++ zs`. Simplificando tenemos: `ys ++ zs = ys ++ zs`, y la demostración se completa con `reflexivity`.


Suponemos verdadera la HI: `xs' ++ ys ++ zs = (xs' ++ ys) ++ zs`.


En el paso inductivo se quiere demostrar `(x :: xs') ++ ys ++ zs = ((x :: xs') ++ ys) ++ zs`, es decir, el caso donde `xs` tiene un elemento más. 

Procedemos a simpliifcar: `x :: xs' ++ ys ++ zs = x :: (xs' ++ ys) ++ zs`.

Por la HI nos queda: `x :: (xs' ++ ys) ++ zs = x :: (xs' ++ ys) ++ zs`. Terminamos con `reflexivity`.

### Ejercicio 11.

*Usando la siguiente definición de reversa en Coq:*
```coq
Fixpoint reversa {A : Type} (l : list A) :=
  match l with
  | nil => nil
  | cons x xs => reversa xs ++ (x :: nil)
  end.
```
*Demuestra que para toda lista xs, ys de tipo A, reversa (xs ++ ys) = reversa ys ++ reversa xs*
```coq
Lemma rev_concat :
  forall (A : Type) (xs ys : list A), reversa (xs ++ ys) = reversa ys ++ reversa xs.
Proof.
  intros A xs ys.
  induction xs as [| x xs' IHxs'].
  - simpl.
    rewrite -> concat_nil_der.
    reflexivity.
  - simpl.
    rewrite -> IHxs'.
    rewrite <- concat_assoc.
    reflexivity.
Qed.  
```
**Explicación:**
El lema estipula la distributividad de la función `reversa` sobre la concatenación de listas. Demostramos por inducción sobre xs.

En el caso base tenemos que `xs = nil`, es decir: `reversa (nil ++ ys) = reversa ys ++ reversa nil`. Usando `simpl`, el lema auxiliar `concat_nil_der` y `reflexivity` se simplifican e igualan ambos lados de la igualdad, concluyendo la dmeostración.

Se supone la HI: reversa (xs' ++ ys) = reversa ys ++ reversa xs' como verdadera.

En el paso inductivo se tiene: `reversa ((x :: xs') ++ ys) = reversa ys ++ reversa (x :: xs')`. 

Simplificando y usando la hipótesis nos queda: `(reversa ys ++ reversa xs') ++ x :: nil = reversa ys ++ reversa xs' ++ x :: nil`.

Finalmente se usa el lema `concat_assoc` (ejercicio 10), seguido de `reflexivity`.

- Teorema auxiliar

*xs ++ nil = xs*
```coq
Theorem concat_nil_der:
  forall (A : Type) (xs : list A), xs ++ nil = xs.
Proof.
  intros A xs.
  induction xs as [| x xs' IHxs'].
  - simpl.
    reflexivity.
  - simpl.
    rewrite -> IHxs'.
    reflexivity.
Qed.
```
**Explicación:**
Este teorema axuiliar nos dice que la concatenación de una lista `xs` con la lista vacía (por la derecha), es igual a `xs` solamente. Se procede por inducción sobre `xs`.

En el caso base se tiene `nil ++ nil = nil`, simplificando nos queda `nil = nil`.

Ahora suponemos verdadera la HI: `xs' ++ nil = xs'`.

En el paso inductivo tenemos: `(x :: xs') ++ nil = x :: xs'`, quitando los paréntesis y usando la hipótesis nos queda `x :: xs' = x :: xs'`. Por último, usamos `reflexivity`.

### Ejercicio 12 :

*Define la función take, que toma una lista `xs`, un número natural `n`, y regresa la lista con los primeros `n` elementos de `xs`.*

```coq
Fixpoint take {A : Type} (n : nat) (l : list A) : list A :=
  match n, l with
  | 0, _ => nil
  | _, nil => nil
  | S n', cons x xs => x :: take n' xs
  end.
```

**Explicación**:
En este fixpoint se define la función `take` que toma una lista `xs` de tipo `A` y un número natural `n`, y devuelve una nueva lista que contiene los primeros `n` elementos de `xs`.

- La definición usa un `match` para manejar los diferentes casos:
  - Si `n` es `0`, el resultado es `nil` (una lista vacía), sin importar el valor de `l`.
  - Si `l` es `nil` (una lista vacía), el resultado es `nil`, sin importar el valor de `n`.
  - Si `n` es el sucesor de `n'` (`S n'`) y `l` es una lista no vacía `cons x xs`, entonces se construye una nueva lista con `x` seguido de `take n' xs` (es decir aquí se emplea la recursión).

### Ejercicio 13. 

*Define la función drop, que toma una lista `xs`, un número natural `n`, y regresa la lista sin los primeros `n` elementos de `xs`.*

```coq
Fixpoint drop {A : Type} (n : nat) (l : list A) : list A :=
  match n, l with
  | 0, xs => xs
  | _, nil => nil
  | S n', x :: xs => drop n' xs
  end.
```

**Explicación**:
En este caso, definimos la función `drop` que toma una lista `xs` de tipo `A` y un número natural `n`, y devuelve una nueva lista que es `xs` sin los primeros `n` elementos.

- La definición también usa un `match` para manejar los diferentes casos:
  - Si `n` es `0`, el resultado es `xs` completo, sin cambios.
  - Si `l` es `nil` (una lista vacía), el resultado es `nil`, sin importar el valor de `n`.
  - Si `n` es el sucesor de `n'` (`S n'`) y `l` es una lista no vacía `cons x xs`, entonces se descarta `x` y se llama recursivamente a `drop` con `n'` y `xs`.

### Ejercicio 14. 

*Demuestra que para toda lista de tipo A y ∀n∈N, xs = take n xs ++ drop n xs*
```coq
Lemma tdn:
  forall (A: Type) (n: nat) (xs : list A),
  xs = take n xs ++ drop n xs.
Proof.
  intros A n. 
induction n as [| n' IH]; intros xs.
  - simpl. (* Caso n = 0 *)
    destruct xs as [| x xs'].
    + simpl. 
      reflexivity.
    + simpl.
      reflexivity.
  - destruct xs as [| x xs']. (* Caso n = S n' *)
    + simpl. (* xs = nil *)
      reflexivity.
    + simpl. (* xs = x :: xs' *)
      rewrite <- IH.
      reflexivity.
Qed.
```
**Explicación:**
Para el ejercicio se procede por inducción sobre `n`.

En el caso base `(n = 0)` tenemos dos subcasos usando `destruct`, cuando `xs` es vacía y cuando tiene cabeza y cola. En ambos subcasos basta con simplifiicar y usar `reflexivity`.

La hipótesis de inducción es `xs : list A, xs = take n' xs ++ drop n' xs`.

En el paso inductivo tenemos dos subcasos usando `destruct`, cuando `xs'` es vacía y cuando tiene cabeza y cola.

Sub-caso 1: `nil = take (S n') nil ++ drop (S n') nil`. Usamos `simpl` y nos queda `nil = nil`. Concluímos con `reflexivity`.

Sub-caso 2: `x :: xs' = take (S n') (x :: xs') ++ drop (S n') (x :: xs')`. Simplificamos y usamos la `HI` para obtener `x :: xs' = x :: xs'`. Solo resta usar `reflexivity`.

### Ejercicio 15. 

*Demuestra que para toda lista de tipo A y ∀n,m∈N, take m (drop n xs) = drop n (take (m + n) xs)*
```coq
Lemma ts:
  forall (A : Type) (xs : list A) (n m : nat), 
    take m (drop n xs) = drop n (take (m + n) xs).
Proof.
  intros A xs.
  induction xs as [| x xs' IHxs].
  - (* Caso base: xs = nil *)
    intros n m. destruct n.
    + simpl.
      rewrite neutro_der.
      reflexivity.
    + simpl.
      destruct m as [| m'].
        * simpl.
          reflexivity.
        * simpl.
         reflexivity.
  - (* Caso inductivo: xs = x :: xs' *)
  intros n m. destruct n as [|  n].
    + (* Subcaso: n = 0 *)
      simpl.
      rewrite neutro_der.
      reflexivity.
    + rewrite suma_der.
      simpl.
      rewrite IHxs.
      reflexivity.
Qed.
```
**Explicación:**
Para el ejercicio `15` se utilizan dos tacticas `(Theorem)` auxiliares para la prueba del lema `ts`, que son explicadas mas abajo.

Esta prueba se hace por induccion sobre la lista, primero se introduce los argumento y la hipotesis. Se tienen dos pruebas:

Lista vacia: Se hace un `destruct` sobre `n`, por lo que hay dos pruebas. Con `n=0` se simplifica con ayuda de los teoremas auxiliares. Para `S n`, se hace un `destruct` sombre `m` y unicamente se simplifica en ambos casos de este mismo.

Lista con un elemento mas: Igualmete se inicia con un `destruct` sobre `n`, el primer caso se simplifica, en el segundo se reescriben propiedades de la suma de los naturales y se simplifica, posteriormente se reescribe la `HIP` y se hace `reflexivity`.

- Teorema auxiliar

*Si n = 0 -> drop n xs = xs.*
```coq
Theorem drop_cero:
  forall (A : Type) (xs  : list A) (n : nat), n = 0 -> drop n xs = xs.
Proof.
  intros A xs n.
  intro H.
  rewrite H.
  destruct xs.
  + simpl. reflexivity.
  + simpl. reflexivity.
Qed.

```
**Explicacion:**
Auxiliar que prueba que la funcion `drop` con parametro `n=0` regresa la misma lista que se dio como parametro. Se hace un `destruct` sobre la lista y en ambos casos simplemente se simplifican ambos lados de la igualdad.

- Teorema auxiliar

*Si xs = nil -> take n xs = nil.*
```coq
Theorem take_nil:
  forall (A : Type) (n : nat) (xs : list A), xs = nil -> take n xs = nil.
Proof.
  intros A n xs.
  intros H.
  rewrite H.
  destruct n.
  + simpl. reflexivity.
  + simpl. reflexivity.
Qed.
```
**Ecplicacion:**
Auxiliar que prueba que la funcion `drop` con parametro `xs=nil` regresa la lista `nil` sin importas la `n` que se dio como parametro . Se hace un `destruct` sobre `n` y en ambos casos simplemente se simplifican ambos lados de la igualdad.

### Ejercicio 16. 

*Demuestra que para toda lista de tipo A y ∀n,m∈N, take m (take n xs) = take (min m n) xs*
```coq
Lemma min:
  forall (A : Type) (xs : list A) (n m : nat),
    take m (take n xs) = take (min m n) xs.
Proof.
intros A xs n m.
revert xs m.
induction n as [|n' IH]; intros xs m.
  - simpl.
    destruct m.
    simpl.
    reflexivity. 
    simpl.
    reflexivity.
  - destruct xs as [|x xs'].
    simpl.
    + destruct m.
      simpl.
      reflexivity.
      simpl.
      reflexivity.
    + destruct m.
      simpl.
      reflexivity.
      simpl.
      rewrite IH.
      reflexivity.
Qed.
```
**Explicación:**
Esta prueba se hace por induccion sobre `n`, se introducen los argumentos y la hipotesis. Por lo que hay dos pruebas.

`n=0`: Se hace un `destruct` sobre `m`, por lo que hay dos casos; `m=0` y `S m`. en ambos basta con hacer `simpl` y `reflexivity`.

`S n`: Se hace `destruct` sobre `xs`, por lo que hay dos casos `xs=nil` y `x:xs`. Para el primero se hace otro `destruct` sobre `m`, casos en los cuales basta con simplificar. En el segundo caso tambien se hace `destruct` sobre `m`, en el primer caso unicamente se simplifica; en el segundo se simplifica y se ocupa la `HIP`, con lo que queda demostrado.
