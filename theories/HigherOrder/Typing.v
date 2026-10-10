From Fsubomega Require Export Terms.
From Fsubomega.HigherOrder Require Export Subtyping.
Set Implicit Arguments.

Inductive htyping (G : hcontext) (E : term_context) : term -> ty -> Prop :=
| ht_var x A : nth_error E x = Some A -> kinding (kinds G) A Star -> htyping G E (tm_var x) A
| ht_abs A t B : kinding (kinds G) A Star -> htyping G (A :: E) t B ->
    htyping G E (tm_abs A t) (tarrow A B)
| ht_app f a A B : htyping G E f (tarrow A B) -> htyping G E a A ->
    htyping G E (tm_app f a) B
| ht_tyabs K A t B : kinding (kinds G) A K ->
    htyping (hextend K A G) (lift_context E) t B ->
    htyping G E (tm_tyabs K A t) (tall K A B)
| ht_tyapp K f C A B : htyping G E f (tall K A B) -> hsub G C A K ->
    htyping G E (tm_tyapp K f C) (substitute (C .: tvar) B)
| ht_sub t A B : htyping G E t A -> hsub G A B Star -> htyping G E t B.

Lemma htyping_regular G E t A : htyping G E t A -> kinding (kinds G) A Star.
Proof.
  induction 1; auto using k_arrow.
  - exact (proj2 (kinding_arrow_inv IHhtyping1)).
  - constructor; auto. now rewrite kinds_extend in IHhtyping.
  - destruct (kinding_all_inv IHhtyping) as [_ HB].
    eapply kinding_substitute; [exact HB |]. intros [|x] L Hx; cbn in *.
    + injection Hx as <-; exact (proj1 (hsub_regular H0)).
    + apply k_var; exact Hx.
  - exact (proj2 (hsub_regular H0)).
Qed.
