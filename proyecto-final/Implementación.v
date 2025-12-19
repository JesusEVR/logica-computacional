Require Import Nat.
Require Import Lia.

(* 
Considérese una representación alternativa para los números naturales, la cual se basa en un sistema binario. Es decir,
en vez de tener un solo constructor, además del cero, para construir números naturales, se tienen 2 constructores, y
cuyas reglas de construcción son las siguientes:

El cero es un número natural.
Si n es un número natural, el doble de n también es un número natural.
Si n es un número natural, entonces uno mas que n es un número natural.
*)

(* Ejercicio 2. 
   Definir de manera recursiva el tipo de dato 'bin' que corresponde 
   a la representación de los números naturales en sistema binario. *)
Inductive bin : Type :=
  | C : bin
  | D : bin -> bin
  | Suc : bin -> bin.

(* Ejercicio 3.
   Definir la función 'incrementa' que suma 1 a un número en forma binaria. *)

Definition incrementa (b:bin) : bin :=
  match b with
 | C => Suc C
 | D n => Suc (D n)
 | Suc n => Suc (Suc n)
  end.

(* Ejercicio 4.
   Definir la función 'bin2nat' que dado un número en forma 
   binaria devuelve su representación en natural. *)

Fixpoint bin2nat (b : bin) : nat :=
  match b with
  | C => 0
  | D n => 2 * (bin2nat n)
  | Suc n => S (bin2nat n)
  end.

(* Ejercicio 5. 
   Demuestra que las funciones incrementa y bin2nat pueden conmutar, es decir, 
   incrementar un número binario  y luego convertirlo a natural produce el mismo 
   resultado que convertirlo primero a natural y luego incrementarlo. *)

(* Auxiliar *)
Theorem neutro_der : forall n:nat, n + 0 = n.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl.
    rewrite -> IHn'.
    reflexivity.
Qed. 

(* Auxiliar *)
Lemma suma_suc :
  forall n : nat, S n = n + 1.
Proof.
    intros n.
    induction n as [| n' IHn'].
    - reflexivity.
    - simpl.
      rewrite -> IHn'.
      reflexivity.
Qed.

Theorem conmuta : forall (b:bin),
  bin2nat(incrementa b) = (bin2nat b) + 1.
Proof.
  intros b. 
  destruct b.
  - simpl. reflexivity.
  - simpl. rewrite neutro_der. simpl bin2nat. rewrite suma_suc. reflexivity.
  - simpl. rewrite <- suma_suc. reflexivity.
Qed.

(* Test para ver que funciona 'incrementa'. *)
 
 Compute incrementa (Suc(D (Suc C))).

(* Test para ver que funcione 'bin2nat'. *)
 
 Compute bin2nat(incrementa(Suc(Suc C))).
 
 Example bin2nat_test: bin2nat(Suc(D(Suc(D(Suc C))))) = 7.
Proof.
  simpl.
  reflexivity.
Qed.

(* Ejercicio 6. 
   Definir la función nat2bin que dado un número en 
   forma natural devuelve su representación en binario. *)

Fixpoint nat2bin (n : nat) : bin :=
  match n with
  | 0 => C
  | S n' => Suc (nat2bin n')
  end.

(* Tests para comprobar que nat2bin funciona. *) 

Compute nat2bin 0.
Compute nat2bin 1.
Compute nat2bin 2.
Compute nat2bin 3.
Compute nat2bin 4.

Example nat2bin_test : bin2nat (nat2bin 4) = 4.
Proof.
  simpl.
  reflexivity.
Qed.

(* Ejercicio 7. 
   Demuestra que al convertir cualquier número natural a binario y luego volver 
   a convertirlo da como resultado el mismo número natural con el que se comenzó. *)

Theorem inversa : forall (n : nat),
  bin2nat (nat2bin n) = n.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

(* Ejercicio 8. 
   Demuestra o da un contraejemplo de la siguiente proposición. *)

Theorem inversa2 : forall (b:bin) ,
  nat2bin (bin2nat b) = b.
Proof.
  intros b.
  induction b as [| b' IHb' | b' IHb'].
  - simpl. reflexivity.  (* Caso base para zero *)
  - simpl. rewrite neutro_der.  (* Caso para incr b' *)
Abort.

(*CONTRAEJEMPLOS
  - Algunos de contraejemplos en los cauales no se cumple el teorema dado inversa2. *)

 Compute nat2bin(bin2nat(Suc(Suc(D(D(Suc C)))))).

 Compute nat2bin(bin2nat(D(Suc(Suc(D(D(Suc C))))))).

(* Ejercicio 9. 
   Definir la función doble que dado un número binario devuelve 
   el doble de éste usando la misma representación. *)

Definition doble (b:bin) : bin :=
  match b with
  | C => C
  | _ => D b
  end.

(* Comprobación de que funciona 'doble'. *)
 Compute doble(Suc(D(Suc(D(Suc C))))).

(* Ejercicio 10.
   Demuestra las propiedades. *)

(* Auxiliar *)
Lemma bin2nat_incrementa : forall b : bin,
  bin2nat (incrementa b) = bin2nat b + 1.
Proof.
  intros b.
  destruct b.
  - simpl. reflexivity.
  - simpl. rewrite neutro_der. rewrite -> suma_suc. reflexivity.
  - simpl. rewrite -> suma_suc. reflexivity.
Qed.

(* Auxiliar *)
Lemma bin2nat_doble : forall b : bin,
  bin2nat (doble b) = 2 * bin2nat b.
Proof.
  intros b.
  destruct b.
 - simpl. reflexivity.
 - simpl. reflexivity.
 - simpl. reflexivity.
Qed.

(* Inciso a pero convirtiendo a naturales cada lado de la igualdad *)
Theorem prop1_alt : forall b : bin,
  bin2nat (incrementa (incrementa (doble b))) = bin2nat (doble (incrementa b)).
Proof.
  intros b.
  rewrite bin2nat_incrementa.
  rewrite bin2nat_incrementa.
  rewrite bin2nat_doble.
  rewrite bin2nat_doble.
  rewrite bin2nat_incrementa.
  simpl.
  lia.  (* Táctica 'lia' puede ayudar a resolver igualdades aritméticas directamente *)
Qed.

(* Inciso 'a' original. Usamos 'admitted' pues arriba lo demostramos cuando se
   convierten ambos lados de igualdad a naturales, para facilitar el ejercicio. *)
Theorem prop1 : forall b : bin,
  incrementa (incrementa (doble b)) = doble (incrementa b).
Proof.
Admitted.

(* Auxiliar *)
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

(* Auxiliar *)
Theorem suma_der : forall n m:nat, n + S(m) = S(n + m).
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl.
    rewrite <- IHn'.
    reflexivity.
Qed.

(* Funcion auxiliar alterna de 'nat2bin', donde en el caso recursivo se usa 
   la función 'incrementa' en lugar de solo colocar un constructor Suc. 
   Ambas serían equivalentes. *)
Fixpoint nat2bin_Alt (n : nat) : bin :=
  match n with
  | 0 => C
  | S n' => incrementa (nat2bin_Alt n')
  end.

(* Inciso 'b' pero utilizando la función 'nat2bin_alt' en vez de 'nat2bin'. *)
Theorem prop2_alt : forall (n : nat), nat2bin_Alt(n + n) = doble (nat2bin_Alt n).
Proof.
  intros.
  induction n.
    - reflexivity.
    - rewrite suma_der.
      simpl.
      rewrite -> IHn.
      rewrite prop1.
      reflexivity.
Qed.

(* Inciso 'b' original. Usamos 'admitted' pues arriba lo demostramos
   reemplazando 'nat2bin' por 'nat2bin_alt', para facilitar el ejercicio. *)
Theorem prop2 : forall (n : nat), nat2bin(n + n) = doble (nat2bin n).
Proof.
Admitted.

(* Inciso 'c' pero utilizando la función 'nat2bin_alt' en vez de 'nat2bin'. *)
Theorem prop3_alt : forall (n : nat), nat2bin_Alt(n + n + 1) = incrementa(doble(nat2bin_Alt n)).
Proof.
  intros.
  induction n.
  - reflexivity.
  - rewrite suma_der.
    simpl.
    rewrite -> neutro_der.
    rewrite -> suma_suc.
    rewrite <- suma_asoc.
    rewrite -> IHn.
    rewrite -> prop1.
    reflexivity.
Qed.

(* Inciso 'c' original. Usamos 'admitted' pues arriba lo demostramos
   reemplazando 'nat2bin' por 'nat2bin_alt', para facilitar el ejercicio. *)
Theorem prop3 : forall (n : nat), nat2bin(n + n + 1) = incrementa(doble(nat2bin n)).
Proof.
Admitted.

(* Ejercicio 11. 
   El hecho de que convertir un número binario a natural y luego a binario de nuevo
   no necesariamente dé el mismo número binario, se debe a que la multiple representación del cero
   en binario. Definir la función normaliza tal que para cualquier número binario b, la conversión
   a natural y luego nuevamente a binario dé como resultado (normalizarb).

   Demuestra que lo anterior se cumple, es decir, que nat2bin (bin2nat b) = normaliza b.
   Sugerencia: Usa la definición de la función doble. *)

(* Auxiliar *)
Fixpoint doble_a_Suc (b : bin) : nat :=
  match b with
  | C => 0
  | D n => 2 * doble_a_Suc n
  | Suc n => 1 + doble_a_Suc n
  end.
      
(* Auxiliar *)
Fixpoint nat_a_Suc (n : nat) : bin :=
  match n with
  | 0 => C
  | S n' => Suc (nat_a_Suc n')
  end.

Definition normaliza(b : bin) : bin :=
  nat_a_Suc (doble_a_Suc b).

(* Ejemplos de que funciona normaliza *)

Compute normaliza(Suc(Suc(D(D(Suc C))))).

Compute normaliza(D(Suc(D(D(Suc C))))).

Compute normaliza(Suc(D(Suc(D(D(Suc C)))))).

Compute normaliza(Suc(D(D(D(D(Suc C)))))).

Compute normaliza(D(D(D(D(D(D C)))))).


(* Teorema: nat2bin (bin2nat b) = normaliza b *)

Theorem nat2bin__bin2nat_normaliza : forall (b : bin),
   nat2bin(bin2nat b) = normaliza b.
Proof.
intros b.
destruct b.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.
  
