From Fsubomega Require Export Terms.
From Fsubomega.FirstOrder Require Export Subtyping.
Set Implicit Arguments.

Inductive typing (G : context) (E : term_context) : term -> ty -> Prop :=
| ty_var x A : nth_error E x = Some A -> old (length G) A -> typing G E (tm_var x) A
| ty_abs A t B : old (length G) A -> typing G (A :: E) t B ->
    typing G E (tm_abs A t) (tarrow A B)
| ty_app f a A B : typing G E f (tarrow A B) -> typing G E a A ->
    typing G E (tm_app f a) B
| ty_tyabs A t B : old (length G) A ->
    typing (extend A G) (lift_context E) t B ->
    typing G E (tm_tyabs Star A t) (tall Star A B)
| ty_tyapp f C A B : typing G E f (tall Star A B) -> sub G C A ->
    typing G E (tm_tyapp Star f C) (substitute (C .: tvar) B)
| ty_sub t A B : typing G E t A -> sub G A B -> typing G E t B.

Lemma typing_regular G E t A : typing G E t A -> old (length G) A.
Proof.
  induction 1; auto using old_arrow.
  - inversion IHtyping1; subst; assumption.
  - constructor; auto. now rewrite extend_length in IHtyping.
  - inversion IHtyping; subst. eapply old_substitute; [eassumption |].
    intros [|x] Hx; cbn.
    + exact (proj1 (sub_regular H0)).
    + apply old_var; lia.
  - exact (proj2 (sub_regular H0)).
Qed.
