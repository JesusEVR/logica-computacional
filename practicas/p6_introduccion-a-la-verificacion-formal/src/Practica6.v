Require Import Nat.
Require Import List.

(* Ejercicio 1 *)
(* Demuestra: (p → q → r) ⇔ (p ∧ q) → r *)

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

(* Ejercicio 2 *)
(* Demuestra: (p → q) → (q → r) → (p → r) *)

Lemma imp_trans : 
  forall P Q R : Prop, (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros P Q R.
  intros PimpQ QimpR evP.
  apply QimpR.
  apply PimpQ.
  apply evP.
Qed.

(* Ejercicio 3 *)
(* Demuestra (p ∨ q) ∧ ¬p → q *)

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

(* Ejercicio 4 *)
(* Demuestra ¬(p ∨ q) ⇔ (¬p ∧ ¬q) *)

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

(* Ejercicio 5 *)
(* Demuestra ∀n∈N, n + 1 = S(n) *)

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

(* Ejercicio 6 *)
(* Demuestra ∀n,m∈N, n + m = m + n *)

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
Theorem suma_der : forall n m:nat, n + S(m) = S(n + m).
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl.
    rewrite <- IHn'.
    reflexivity.
Qed.


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

(* Ejercicio 7 *)
(* Demuestra ∀n,m,p∈N, p·(n + m) = p·n + p·m *)

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

(* Ejercicio 8 *)
(* Implementa de manera recursiva una función que calcule 
   la suma de todos los números naturales hasta n. *)

Fixpoint gauss (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => S n' + gauss n'
  end.

(* Ejercicio 9 *)
(* Demuestra que tu implementación de gauss cumple que ∀n∈N, 2·gauss(n) = n·(n + 1). *)

(* Conmutatividad de la Multiplicacion *)
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


(* Ejercicio 10 *)
(* Demuestra que la operación de concatenación es asociativa en listas. *)

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
  
(* Ejercicio 11 *)
(* Usando la siguiente definición de reversa en Coq: *)

Fixpoint reversa {A : Type} (l : list A) :=
  match l with
  | nil => nil
  | cons x xs => reversa xs ++ (x :: nil)
  end.
      
(* Teorema auxiliar *)
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

(* Demuestra: *)
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

(* Ejercicio 12 *)
(* Define la función take, que toma una lista xs, un número natural n, 
   y regresa la lista con los primeros n elementos de xs. *)

Fixpoint take {A : Type} (n : nat) (l : list A) : list A :=
  match n, l with
  | 0, _ => nil
  | _, nil => nil
  | S n', cons x xs => x :: take n' xs
  end.

(* Ejercicio 13 *)
(* Define la función drop, que toma una lista xs, un número natural n,
   y regresa la lista sin los primeros n elementos de xs. *)

Fixpoint drop {A : Type} (n : nat) (l : list A) : list A :=
  match n,l with
  | 0, xs => xs
  | _, nil => nil
  | S n', x :: xs => drop n' xs
  end.

(* Ejercicio 14 *)
(* Demuestra: xs = take n xs ++ drop n xs *)

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

(* Ejercicio 15 *)
(* Demuestra: take m (drop n xs) = drop n (take (m + n) xs) *)

(* Auxiliar *)
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

(* Auxiliar *)
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

(* Ejercicio 16 *)
(* Demuestra: take m (take n xs) = take (min m n) xs *)

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
