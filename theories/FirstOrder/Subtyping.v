From Fsubomega.FirstOrder Require Export Syntax.
Set Implicit Arguments.

(** Full F-sub, with declarative transitivity. In particular [sub_all] changes
    the bound contravariantly and checks the bodies under the right bound. *)
Inductive sub (G : context) : ty -> ty -> Prop :=
| sub_refl A : old (length G) A -> sub G A A
| sub_top A : old (length G) A -> sub G A ttop
| sub_var x A : nth_error G x = Some A -> old (length G) A -> sub G (tvar x) A
| sub_trans A B C : sub G A B -> sub G B C -> sub G A C
| sub_arrow A A' B B' : sub G A' A -> sub G B B' ->
    sub G (tarrow A B) (tarrow A' B')
| sub_all A A' B B' : sub G A' A -> sub (extend A' G) B B' ->
    sub G (tall Star A B) (tall Star A' B').

Lemma sub_regular G A B : sub G A B -> old (length G) A /\ old (length G) B.
Proof.
  induction 1 as [G A HA | G A HA | G x A Hx HA | G A B C H1 IH1 H2 IH2 |
    G A A' B B' H1 IH1 H2 IH2 | G A A' B B' H1 IH1 H2 IH2].
  - auto.
  - split; auto using old_top.
  - split; auto. constructor. now apply nth_error_Some_lt in Hx.
  - tauto.
  - destruct IH1, IH2; split; constructor; auto.
  - rewrite extend_length in IH2. destruct IH1, IH2; split; constructor; auto.
Qed.

Lemma sub_rename G A B : sub G A B ->
  forall D rho, context_ren G D rho -> sub D (rename rho A) (rename rho B).
Proof.
  induction 1; intros D rho Hr; cbn [rename ren_exp tvar tarrow tall].
  - apply sub_refl; eapply old_rename; [exact H | exact (proj1 Hr)].
  - apply sub_top; eapply old_rename; [exact H | exact (proj1 Hr)].
  - eapply sub_var; [eapply (proj2 Hr); eauto |].
    eapply old_rename; [exact H0 | exact (proj1 Hr)].
  - eapply sub_trans; eauto.
  - apply sub_arrow; auto.
  - apply sub_all; auto. apply IHsub2. now apply context_ren_extend.
Qed.

Lemma sub_weaken G A B U : sub G A B ->
  sub (extend U G) (rename shift A) (rename shift B).
Proof. intros H; eapply sub_rename; eauto using context_ren_shift. Qed.
