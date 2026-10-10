From Fsubomega Require Export Binding.
Set Implicit Arguments.

(** The old language is a grammar, not a predicate defined by convertibility.
    Both the scope and the absence of operator syntax are explicit. *)
Inductive old (n : nat) : ty -> Prop :=
| old_var x : x < n -> old n (tvar x)
| old_top : old n ttop
| old_arrow A B : old n A -> old n B -> old n (tarrow A B)
| old_all A B : old n A -> old (S n) B -> old n (tall Star A B).

Lemma old_rename n A : old n A ->
  forall m rho, scoped_ren n m rho -> old m (rename rho A).
Proof.
  induction 1; intros m rho Hr; cbn [rename ren_exp tvar tarrow tall].
  - constructor; auto.
  - constructor.
  - constructor; auto.
  - constructor; auto using scoped_ren_up.
Qed.

Lemma old_substitute n A : old n A ->
  forall m sigma, (forall x, x < n -> old m (sigma x)) -> old m (substitute sigma A).
Proof.
  induction 1; intros m sigma Hs; cbn [substitute subst_exp tvar tarrow tall].
  - auto.
  - constructor.
  - constructor; auto.
  - constructor; auto. apply IHold2. intros [|x] Hx; cbn.
    + apply old_var; change (0 < S m); lia.
    + apply old_rename with (n := m).
      * apply Hs; lia.
      * intros y Hy; change (S y < S m); lia.
Qed.

Lemma old_normal n A : old n A -> Normal step A.
Proof.
  induction 1.
  - apply normal_var.
  - apply normal_const.
  - apply normal_app_intro; [cbn; tauto | | exact IHold2].
    apply normal_app_intro; [cbn; tauto | apply normal_const | exact IHold1].
  - apply normal_app_intro; [cbn; tauto | | now apply normal_lam_intro].
    apply normal_app_intro; [cbn; tauto | apply normal_const | exact IHold1].
Qed.

Lemma old_convert_eq n m A B : old n A -> old m B -> convert A B -> A = B.
Proof.
  intros HA HB H.
  eapply equiv_unique_normal_forms.
  - apply confluence_step.
  - exact H.
  - exact (old_normal HA).
  - exact (old_normal HB).
Qed.

Lemma old_kinding n A : old n A -> kinding (repeat Star n) A Star.
Proof.
  induction 1; constructor; auto.
  rewrite nth_error_repeat; now destruct (lt_dec x n).
Qed.

(** All bounds in a context use the current scope. Extending a context shifts
    the new bound and every existing bound together. *)
Definition context := list ty.
Definition extend (A : ty) (G : context) : context := map (rename shift) (A :: G).

Lemma extend_length A G : length (extend A G) = S (length G).
Proof. unfold extend; now rewrite length_map. Qed.

Inductive context_wf : context -> Prop :=
| ctx_nil : context_wf []
| ctx_cons G A : context_wf G -> old (length G) A -> context_wf (extend A G).

Definition context_ren (G D : context) (rho : nat -> nat) :=
  scoped_ren (length G) (length D) rho /\
  forall x A, nth_error G x = Some A -> nth_error D (rho x) = Some (rename rho A).

Lemma context_ren_extend G D rho A :
  context_ren G D rho -> context_ren (extend A G) (extend (rename rho A) D) (up_ren rho).
Proof.
  intros [Hscope Hlookup]; split.
  - rewrite !extend_length; now apply scoped_ren_up.
  - intros [|x] B Hb; unfold extend in *; cbn in *.
    + inversion Hb; subst. f_equal. unfold rename. now asimpl.
    + rewrite nth_error_map in Hb.
      destruct (nth_error G x) as [C|] eqn: HC;
        cbn in Hb; try discriminate. injection Hb as <-.
      rewrite nth_error_map. rewrite (Hlookup _ _ HC). cbn.
      f_equal. unfold rename. now asimpl.
Qed.

Lemma context_ren_shift G A : context_ren G (extend A G) shift.
Proof.
  split.
  - rewrite extend_length; intros x Hx; change (S x < S (length G)); lia.
  - intros x B Hx; unfold extend; cbn. now rewrite nth_error_map, Hx.
Qed.

Lemma context_ren_id G : context_ren G G id.
Proof.
  split; [intros x Hx; exact Hx |].
  intros x A Hx; now rewrite rename_id.
Qed.

Lemma context_ren_comp G D E rho tau :
  context_ren G D rho -> context_ren D E tau -> context_ren G E (rho >> tau).
Proof.
  intros [Hr HL] [Ht HM]; split.
  - intros x Hx; apply Ht, Hr, Hx.
  - intros x A Hx; unfold funcomp. rewrite (HM _ _ (HL _ _ Hx)).
    now rewrite rename_comp.
Qed.

Lemma context_wf_bounds G : context_wf G ->
  forall x A, nth_error G x = Some A -> old (length G) A.
Proof.
  induction 1; intros x B Hx; [destruct x; discriminate |].
  rewrite extend_length. unfold extend in Hx; rewrite nth_error_map in Hx.
  destruct x as [|x]; cbn in Hx.
  - injection Hx as <-. eapply old_rename; [exact H0 |].
    intros y Hy; change (S y < S (length G)); lia.
  - destruct (nth_error G x) as [C|] eqn: HC; cbn in Hx; try discriminate.
    injection Hx as <-. eapply old_rename; [eapply IHcontext_wf; eauto |].
    intros y Hy; change (S y < S (length G)); lia.
Qed.
