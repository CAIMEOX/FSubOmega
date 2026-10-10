From Fsubomega Require Export Binding.
From Fsubomega.FirstOrder Require Import Syntax.
Set Implicit Arguments.

(** Two independent de Bruijn namespaces: term variables and type variables.
    Type abstraction/application carry the kind explicitly. No operational
    semantics of terms is needed for judgmental conservativity. *)
Inductive term :=
| tm_var (x : nat)
| tm_abs (A : ty) (t : term)
| tm_app (f a : term)
| tm_tyabs (K : kind) (A : ty) (t : term)
| tm_tyapp (K : kind) (t : term) (A : ty).

Inductive old_term (n : nat) : term -> Prop :=
| ot_var x : old_term n (tm_var x)
| ot_abs A t : old n A -> old_term n t -> old_term n (tm_abs A t)
| ot_app f a : old_term n f -> old_term n a -> old_term n (tm_app f a)
| ot_tyabs A t : old n A -> old_term (S n) t -> old_term n (tm_tyabs Star A t)
| ot_tyapp t A : old_term n t -> old n A -> old_term n (tm_tyapp Star t A).

Definition term_context := list ty.
Definition lift_context (E : term_context) := map (rename shift) E.
Definition old_context n (E : term_context) := Forall (old n) E.

Lemma old_context_lookup n E x A : old_context n E -> nth_error E x = Some A -> old n A.
Proof.
  intros H Hx; eapply Forall_forall in H; [exact H | now apply nth_error_In in Hx].
Qed.

Lemma old_context_lift n E : old_context n E -> old_context (S n) (lift_context E).
Proof.
  intro H; induction H; cbn; constructor; auto.
  eapply old_rename; [exact H |]. intros y Hy; change (S y < S n); lia.
Qed.

Lemma old_abs_inv n A t : old_term n (tm_abs A t) -> old n A /\ old_term n t.
Proof. intro H; inversion H; auto. Qed.

Lemma old_app_inv n f a : old_term n (tm_app f a) -> old_term n f /\ old_term n a.
Proof. intro H; inversion H; auto. Qed.

Lemma old_tyabs_inv n K A t : old_term n (tm_tyabs K A t) ->
  K = Star /\ old n A /\ old_term (S n) t.
Proof. intro H; inversion H; auto. Qed.

Lemma old_tyapp_inv n K f A : old_term n (tm_tyapp K f A) ->
  K = Star /\ old_term n f /\ old n A.
Proof. intro H; inversion H; auto. Qed.
