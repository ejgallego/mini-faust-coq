Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.

(* Coq Faust Demo for LAC 2015 *)

(* Basic syntax

- Functions:

  fun x => x + x

  - takes a parameter named x, return x + x

- Application is just juxtaposition:

  f g

 *)

Eval compute in ([fun x => x + x] 2).

(* Datatypes and pattern matching

Inductive nat : Type :=
| 0    : nat
| n.+1 : nat -> nat

*)

Fixpoint is_even n :=
  match n with
  | 0    => true
  | n.+1 => ~~ (is_even n)
  end.

Eval compute in (is_even 3, is_even 2).

Lemma is_even4 : is_even 4 = true.
Proof.
  compute.
  reflexivity.
Qed.

Lemma is_even_mult2 : forall n, is_even (n.*2) = true.
Proof.
  elim=> [|n ihn].
  + done.
  + rewrite /=.
    rewrite negbK.
    rewrite ihn.
    done.
Qed.

(* Types:

Types are the most important part of Coq.

The key type is the function type, A → B,
which represents programs with input A and
output B.

The main typing or reasoning rule is:

Γ ⊢ f : A → B         Γ ⊢ x : A
───────────────────────────────
         Γ ⊢ f x : B

This codifies the rule of "modus ponens".

Another important rule is:

    Γ, x : A ⊢ e : B
────────────────────────
 Γ ⊢ fun x => e : A → B

This captures the act of
"reasoning under a hypothesis"

*)

(***********************************************)
(* Proof idioms                                *)

Definition trivial_1 P : P -> P :=
  fun x => x.

Definition trivial_2 P Q : P -> Q -> P :=
  fun x y => x.

(* Replace by y *)

(* We can build programs interactively *)
Lemma trivial_3 P Q : P -> Q -> P.
Proof.
  move=> p q.
  exact: p.
Qed.

Lemma trivial_4 P Q : P -> Q -> P.
Proof. exact: trivial_2. Qed.

(* Proof by Shuffling: move/apply
Bookeping a significant cost in formal proof.
*)

(* Proof by inspection: case/elim *)
Lemma OrC P Q : P \/ Q -> Q \/ P.
Proof.
  case.
  + right. done.
  + left. done.
Qed.

(* Naming: add naturals Commutative *)
Print plus.
(*
plus (n m : nat) :=
  match n with
  | 0 => m
  | p.+1 => (plus p m).+1
  end

Or
 - 0 + m    => m
 - n.+1 + m => (n+m).+1

Note no rule for m + 0!

*)

Lemma addn0 n : n + 0 = n.
(* Welcome to equality

   equality is a type, such that the only
   constructor is when programs are the same.

   erefl x : x = x

   When we know A = B, we can use rewrite to
   replace A by B!
 *)
Proof.
  elim: n => [ | n ihn] /=.
  - compute. done.
  - Check addSn.
    rewrite addSn.
    rewrite ihn. done.
Qed.

(* Equality works for more complicated things *)
Require Import ssralg.
Open Scope ring_scope.
Import GRing.Theory.

Lemma roots (N : fieldType) (x : N) :
  (x - 1) * (x - 1) = x ^+ 2 - x *+ 2 + 1.
Proof.
  rewrite !(mulrDl, mulrDr).
  Search _ (_ * -1).
  rewrite !(mulrN1, mulN1r).
  rewrite opprK mulr2n !addrA.
  rewrite opprD addrA.
  done.
Qed.

