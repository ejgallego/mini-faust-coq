(* Copyright (c) 2015, CRI, MINES ParisTech, PSL Research University

   All rights reserved.

   LICENSE: GPL-3
   See the LICENSE file for details on licensing.

   Tested in Coq 8.4, ssreflect/mathcomp 1.5
*)

(*

A Linux Audio Conference 2015 tutorial, by

* Emilio Jesús Gallego Arias
* Olivier Hermant
* Pierre Jouvelot

CRI, MINES ParisTech, PSL Research University

We present a toy semantic and logic for core Faust programs.

The file is organized in 4 main sections:

- FaustSyntax: We define the syntax of a minimal core Faust.

- FaustSemantics: We define a semantics for Faust stream processors as
  functions from fixed-length sequences to fixed-length sequences.

- SampleLogic: We define a sampled logic syntax and its semantics.

- Examples: We check stability for a simple low-pass filter.

The accompanion paper diverges sometimes in order to improve the presentation.

*)

Require Import Utf8.
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
Require Import tuple bigop ssralg ssrnum ssrint interval.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* We include some auxiliary definitions to make the file
 * self-contained. The reader can skip the Prelude section safely.
 *)

Section Prelude.

(* "V n T" is n copies of type T, noted T^n in the paper. *)
Section Vector.
Fixpoint V (n : nat) T {struct n} : Type :=
  match n with
  | 0    => unit
  | n.+1 => match n with
            | 0 => T
            | _ => (T * V n T)%type
            end
  end.

Definition vhead n T : V n.+1 T -> T :=
  match n with
  | 0    => fun t => t
  | n.+1 => fun t => fst t
  end.

Definition vtail n T : V n.+1 T -> V n T :=
  match n with
  | 0    => fun _ => tt
  | n.+1 => fun t => snd t
  end.

Fixpoint vfold2 T U W (x : W) (f : T -> U -> W -> W) n : V n T -> V n U -> W :=
  match n return V n T -> V n U -> W with
  | 0    => fun _ _   => x
  | n.+1 => fun t1 t2 => f (vhead t1) (vhead t2) (vfold2 x f (vtail t1) (vtail t2))
  end.

End Vector.

(* Additional lemmas on sequences *)
Section Seq.

Lemma take_take (T : eqType) m n (s : seq T) : m <= n ->
  take m (take n s) = take m s.
Proof. by elim: s n m => [|x s ihs] [|n] [|m] H //=; rewrite ihs. Qed.

Lemma all_take T n (s : seq T) P : all P s -> all P (take n s).
Proof. by rewrite -{1}[s](cat_take_drop n) all_cat; case/andP. Qed.

(* Auxiliary type cast *)
Definition sC T n (x : seq T) (p : (size x).+1 == n.+1) : n.-tuple T := Tuple p.

End Seq.
End Prelude.

(* Start of Faust formalization *)

Reserved Notation "i ↝ o" (at level 30, no associativity).

Section FaustSyntax.

Variable N : ringType.

Inductive fterm : nat -> nat -> Type :=
| mult : N -> 1 ↝ 1
| plus : 2 ↝ 1
| comp : 1 ↝ 1 -> 1 ↝ 1 -> 1 ↝ 1
| feed : 2 ↝ 1 -> 1 ↝ 1 -> 1 ↝ 1
where "i ↝ o" := (fterm i o).

End FaustSyntax.

(* We need to declare notations out of the sections again. *)
Notation "i ↝ o" := (fterm _ i o).

Arguments fterm [N] i o.
Arguments plus  [N].
Arguments mult  [N] c.
Arguments comp  [N] f g.
Arguments feed  [N] f g.

Notation "'+"      := plus.
Notation "'*( c )" := (mult c).
Notation "f ∶ g"   := (comp f g) (at level 75).
Notation "f ~ g"   := (feed f g) (at level 70).

Section SyntaxExample.

Variable N : numDomainType.

(* A simple low-pass filter *)
Definition smooth (c : N) := '*(1 - c) ∶ '+ ~ '*(c).
Print smooth.

End SyntaxExample.

Section FaustSemantics.

Local Open Scope ring_scope.

Variable N : numDomainType.
Variable x0 : N.

Notation "''S_' n" := (n.-tuple N)
  (at level 8, n at level 2, format "''S_' n").

Notation "''SP_' ( i , o )" := (forall n, V i 'S_n -> V o 'S_n)
  (at level 8, format "''SP_' ( i , o )").

Notation "i ↝ o" := (@fterm N i o).

(* We use a form of strong induction to get a nicer definition of the
 * feedback, in a size-preserving way.
 *
 * The reader may skip this section, as it is rather technical and of
 * little interest regarding audio issues.
 *)

Section FeedBack.

Local Open Scope nat.

Definition iter_dep (B : nat -> Type) n
           (f : forall m (H : m < n), B m -> B m.+1) (x : B 0) : B n.
Proof.
  elim: n f => [H| n ihn f]; first exact: x.
  pose f' m H bm := f m (ltn_trans H (ltnSn n)) bm.
  exact: (f n (ltnSn _) (ihn f')).
Defined.

(* Iteration is extensional on the iterator. *)
Lemma eq_iter_dep (B : nat -> Type) n
      (f g : forall m (H : m < n), B m -> B m.+1) (x : B 0)
      (Hfg : forall m (H : m < n) (a : B m), f m H a = g m H a) :
  iter_dep f x = iter_dep g x.
Proof.
  elim: n f g Hfg => //= n ihn f g Hfg.
  pose f' m H bm := f m (ltn_trans H (ltnSn n)) bm. 
  pose g' m H bm := g m (ltn_trans H (ltnSn n)) bm.
  have Hfg' m H0 a : f' m H0 a = g' m H0 a by rewrite /f' /g' /= Hfg.
  by rewrite Hfg (ihn f' g').
Qed.

(* Auxiliary constructors for the tuples. *)
Lemma size_take_S n (i : 'S_n) m (H : m < n) : size (take m.+1 i) == m.+1.
Proof. by rewrite size_takel ?size_tuple. Qed.

Lemma size_take_n n (i : 'S_n.+1) : size (take n i) == n.
Proof. by rewrite size_takel ?size_tuple. Qed.

Definition feedback_int
           (f : forall n, 'S_n * 'S_n -> 'S_n)
           (g : forall n, 'S_n -> 'S_n)
           (n : nat) (i : 'S_n) : 'S_n.
Proof.
  pose fb_it m Hm (fb : 'S_m) :=
    f _ (g _ [tuple of x0 :: fb], Tuple (size_take_S i Hm)).
  exact: iter_dep fb_it [tuple].
Defined.

(* Just a fancier version of:

Definition feedback_int (n : nat)
           (f : seq N * seq N -> seq N)
           (g : seq N -> seq N)
           (i : seq N) : seq N :=
  iteri n [fun n fb => f (g (x0 :: fb), i)] [::].

*)

(* The main unfolding lemma for the feedback.
 * The complication here is dealing with the proof terms, as always.
 *)

Lemma feedback_intS
           (f : forall n, 'S_n * 'S_n -> 'S_n)
           (g : forall n, 'S_n -> 'S_n)
           (n : nat) (i : 'S_n.+1) :
  let fo : 'S_n := feedback_int f g (Tuple (size_take_n i)) in
  feedback_int f g i = f _ (g _ [tuple of x0 :: fo], i).
Proof.
  rewrite /feedback_int /=; congr (f _ (g _ [tuple of _ :: _] , _)).
  + apply: eq_iter_dep => m H fb; congr (f _ (_, _)).
    by apply: val_inj; rewrite /= take_take.
  + by apply: val_inj; rewrite /= -{1}(size_tuple i) take_size.
Qed.

End FeedBack.

(* The main interpretation function *)
Fixpoint I {i o} (t : i ↝ o) : 'SP_(i, o) :=
  match t in fterm i o return 'SP_(i, o) with
  | mult n   => fun _ i => [tuple of map (fun x => n * x) i]
  | plus     => fun _ i => [tuple of map (fun x => x.1 + x.2) (zip i.1 i.2)]
  | comp f g => fun n i => (I g) n ((I f) n i)
  | feed f g => fun n i => feedback_int (I f) (I g) i
  end.

(* We check the Fusion of Multiplication Lemma shown in the paper. *)
Import GRing.Theory.
Lemma multF a b n (i : 'S_n) : I ('*(a) ∶ '*(b)) i = I ('*(a*b)) i.
Proof.
  apply: val_inj; case: i => s /= _.
  rewrite -map_comp; apply/eq_map=> x /=.
  by rewrite mulrCA mulrA.
Qed.

Check I (smooth 0).

(******************************************************************************)
(* Delays are interesting with this semantics.                                *)
(*                                                                            *)
(* The semantics is indexed by the number of execution steps of the           *)
(* program. Delays are represented by padding the current stream with         *)
(* the initial value. Thus, if a stream had value "d" at time 2, after        *)
(* a delay of 9, the value "d" must occur at time 11.                         *)
(*                                                                            *)
(* To that effect, we pad the stream with 9 values. Keep in mind that         *)
(* streams processors can use an arbitrary amount of memory to store          *)
(* the previous values of their input streams (denotationally, they have      *)
(* access to the full history of the stream), but thus they are               *)
(* bounded by the current number of steps.                                    *)
(******************************************************************************)

Definition delay n (t : 'S_n) : 'S_n := [tuple of belast x0 t].

End FaustSemantics.

Section SemanticsExample.

Require Import rat.
Local Open Scope ring_scope.
Local Open Scope rat_scope.

Let il := [:: 8%:Q; 1; 2%:Q; 3%:Q; 0; 0; 19%:Q; 0; 0].

(* Warning: this is not supposed to run efficiently! *)
Eval compute    in map val (delay 0 [tuple of il]).
Check                       I 0 (smooth (1%:Q/3%:Q)) [tuple of il].
Eval compute    in map val (I 0 (smooth (1%:Q/3%:Q)) [tuple of il]).
Eval vm_compute in map val (I 0 (smooth (1%:Q/3%:Q)) [tuple of il]).

End SemanticsExample.

(******************************************************************************)
(*                                                                            *)
(* A logic for one-sample predicates                                          *)
(*                                                                            *)
(******************************************************************************)

(* Judgements and soundness *)

Reserved Notation "''[[' J '']]'" (at level 0, J at level 6).
Reserved Notation "[ {  P  }  f {  Q  } ]"
         (at level 0, P at level 2, f at level 9, Q at level 2).

(* Reserved Notation "[ { P | i } f { o | Q } ]" (at level 0, P at
level 99, i ident, f at level 9, o at level 1, Q at level 2). *)

Section SampleLogic.

Local Open Scope ring_scope.
Variable N : numDomainType.
Variable x0 : N.

Notation "''S_' n" := (n.-tuple N)
  (at level 8, n at level 2, format "''S_' n").

Notation "i ↝ o" := (@fterm N i o).

(* Semantic soundness for primitives at a sample level *)
Definition plusT P Q   := ∀ (i : N * N), P.1 i.1 && P.2 i.2 ==> Q (i.1 + i.2).
Definition multT c P Q := ∀ (i : N ), P i ==> Q (c * i).

(* We define the rules of our logic; placing the term first helps type
 * inference.
 *)

Inductive sampleJ : ∀ (i o : nat), i ↝ o -> V i (pred N) -> V o (pred N) -> Type :=
  | sj_plus (P : (pred N * pred N)) (Q : pred N) : plusT P Q ->
                        [{ P }  '+   { Q }]

  | sj_mult c P Q : multT c P Q ->
                        [{ P } '*(c) { Q }]

  | sj_comp f g P Q R : [{ P }    f    { R }] ->
                        [{ R }    g    { Q }] ->
                        [{ P } (f ∶ g) { Q }]

  | sj_feed (f : 2 ↝ 1) (g : 1 ↝ 1) (P Q R : pred N) : Q x0 ->
                        [{(R, P)} f    { Q }] ->
                        [{ Q }    g    { R }] ->
                        [{ P } (f ~ g) { Q }]
where "[ {  P  } f {  Q  } ]" := (sampleJ f P Q).

(* Helper for interpreting judgements and vectors of predicates *)
Definition v_all m n : V n (pred N) -> V n 'S_m -> bool :=
  @vfold2 _ _ _ true [fun p => andb \o (all p \o val)] n.

Lemma v_all1 m (i : 'S_m) P : @v_all m 1 P i = all P i.
Proof. by rewrite /v_all /= andbT. Qed.

Lemma v_all2 m (i1 i2 : 'S_m) P1 P2 :
  @v_all m 2 (P1, P2) (i1, i2) = all P1 i1 && all P2 i2.
Proof. by rewrite /v_all /= andbT. Qed.

Definition v_allE := (v_all1, v_all2).

(* Soundess/interpretation of a judgment *)
Definition IJ i o (f : i ↝ o)
           (P : V i (pred N))
           (Q : V o (pred N))
           (J : [{ P } f { Q }] ) x0 :=
  forall n (i : V i 'S_n), v_all P i ==> v_all Q (I x0 f i).

Notation "''[[' J '']]'" := (IJ J).

(* Main theorem: existence of a derivation implies that, for all input
   samples that meet the precondition of the judgment, the output
   samples of f satisfy the postcondition.
 *)
Lemma sampleT i o (f : i ↝ o)
      (P : V i (pred N))
      (Q : V o (pred N))
      (J : [{ P } f { Q }] ) : '[[ J ']] x0.
Proof.
  elim: i o f P Q / J =>
    [ [P1 P2] /= Q Hsum
    | c   P      Q Hmult
    | f g P Q R     Jf ihf Jg ihg n i
    | f g P Q R Hx0 Jf ihf Jg ihg n i
    ].

  (* The cases for the primitives are similar and easy. *)
  - elim=> /= [|n ihn] [[[|a sa] Ha] [[|b sb] Hb]] //.
    apply/implyP=> /andP /= [/andP [HPa HPax] /andP [/andP [HPb HPbx]]] _.
    have /=   := Hsum (a,b).
    have{ihn} := ihn (sC Ha, sC Hb).
    by rewrite !v_allE HPa HPax HPb HPbx /= => ->->.

  - elim=> /= [|n ihn] [[|a sa] Ha] //.
    apply/implyP=> /andP /= [/andP [HPa HPax]] _.
    have /=   := Hmult a.
    have{ihn} := ihn (sC Ha).
    by rewrite !v_allE HPa HPax /= => ->->.

  (* Composition is straightforward. *)
  - apply/implyP=> HP /=.
    have{ihg} := ihg n (I x0 f i).
    have{ihf} := ihf n i.
    by rewrite HP /= => ->.

  (* The feedback rule goes through by induction on the number of steps. *)
  - rewrite !v_allE.
    elim: n i x0 Hx0 ihf ihg => [|n ihn] [[|i ix]] Hi x_0 Hx0 ihf ihg //=.
    apply/implyP=> /andP [Hx Hallx].
    rewrite feedback_intS.
    (* Apply IH from f *)
    set t1 := I x_0 g _.
    set t2 := Tuple _.
    have/implyP := ihf n.+1 (t1, t2).
    rewrite !v_allE /= Hx Hallx => -> //= {t2}.
    (* Apply IH from g *)
    set tfb := [tuple of x_0 :: _] in t1 *.
    have/implyP := ihg n.+1 tfb.
    rewrite !v_allE /= Hx0 => -> //= {t1 tfb}.
    (* Apply IH on number of steps *)
    set pi := Tuple _.
    have/implyP -> //= := ihn pi x_0 Hx0 ihf ihg => {pi ihf ihg ihn}.
    by rewrite (all_take n (s:=i::ix)) ?(eqP Hi) /= ?Hx.
Qed.

End SampleLogic.

Notation "''[[' J '']]'" := (IJ J).
Notation "[ { P }  f { Q } ]" := (sampleJ _ f P Q).

About sampleT.
Print Assumptions sampleT.

(* Simple tactic for rule-selection and intervals *)
Ltac ilogic := (
    (refine (@sj_plus _ _ (_, _) _ _);
     case=> [i1 i2] /=; apply/implyP=> /andP [Hi1 Hi2]) ||
    (refine (@sj_mult _ _ _ [pred i | i \in _] [pred o | o \in _] _);
     move=> i; apply/implyP=> /= Hi) ||
    (refine (sj_feed (R:=[pred r | r \in _]) _ _ _)) ||
    (refine (sj_comp (R:=[pred r | r \in _]) _ _))
  ).

(* Now we can verify smooth! *)
Section SmoothVerif.

(* We will define our property over intervals. *)
Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

(* We first set up the value domain. *)
Variable N : numDomainType.

(* Our initial value is 0. *)
Definition x0 : N := 0.

Local Notation "[ { P }  f { Q } ]" := (sampleJ x0 f P Q).

(* Our intervals and constants *)

Variable a b c : N.
Hypothesis Hc  : c \in `[0,1].
(* The interval is WF. *)
Hypothesis Hab : a <= b.

(* Also the init value should be in the output. *)
Hypothesis (H0ab : x0 \in `[a, b]).
Definition Pab := [pred x | x \in `[a,b] ].

(* We have to stablish the judgment. *)
Lemma smooth_deriv : [{ Pab } (smooth c) { Pab }].
Proof.
  (* The first rule of our proof tree is composition. *)
  ilogic.

  (* We use the multiplication rule here. *)
  + ilogic.

    (* We instantiate the correct predicate. *)
    instantiate (1 := `[(1-c)*a, (1-c)*b]) => /=.
    by rewrite ?itv_boundlr /=
               ?ler_wpmul2l ?ler_subr_addr ?add0r ?(itvP Hi) ?(itvP Hc).

  (* We apply the feedback rule. *)
  + ilogic => //; last first.

    (* Again the mult rule, this time with a different predicate *)
    - ilogic.
      instantiate (1 := `[c*a, c*b] ) => /=.
      by rewrite itv_boundlr /= ?ler_wpmul2l ?(itvP Hi) ?(itvP Hc).

    (* The remaining step to close the proof is to handle the addition
       proof obligation. *)
    - ilogic.
      have mulrcD x: x = x * c + x * (1 - c)
        by rewrite -mulrDr addrC addrNK mulr1.
      by rewrite itv_boundlr /=
                 [a]mulrcD [b]mulrcD !ler_add // mulrC ?(itvP Hi1) ?(itvP Hi2).
Qed.

(* sampleT implies that smooth is stable. *)
Lemma smooth_stable : '[[ smooth_deriv ']] x0.
Proof. exact/sampleT. Qed.

About smooth_deriv.
About smooth_stable.

(*

∀ (n : nat) (i : V 1 (n.-tuple N)),
  v_all Pab i ==> v_all Pab (I x0 (smooth c) i) = true

*)

End SmoothVerif.

About smooth_stable.
Print Assumptions smooth_stable.
