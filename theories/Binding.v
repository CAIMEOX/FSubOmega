From Fsubomega Require Export Syntax.
Set Implicit Arguments.

(** Small adapter around the installed Autosubst API. *)
#[export] Hint Unfold rename substitute lift tvar tabs tapp : asimpl.

Lemma rename_id A : rename id A = A.
Proof. unfold rename; now asimpl. Qed.

Lemma substitute_id A : substitute tvar A = A.
Proof. unfold substitute, tvar; now asimpl. Qed.

Lemma rename_comp rho tau A :
  rename tau (rename rho A) = rename (rho >> tau) A.
Proof. unfold rename; now asimpl. Qed.

Lemma substitute_comp sigma tau A :
  substitute tau (substitute sigma A) =
  substitute (sigma >> substitute tau) A.
Proof. unfold substitute; now asimpl. Qed.

Lemma rename_substitute rho sigma A :
  rename rho (substitute sigma A) = substitute (sigma >> rename rho) A.
Proof. unfold rename, substitute; now asimpl. Qed.

Lemma substitute_rename rho sigma A :
  substitute sigma (rename rho A) = substitute (rho >> sigma) A.
Proof. unfold rename, substitute; now asimpl. Qed.

Lemma rename_ext rho tau A :
  (forall x, rho x = tau x) -> rename rho A = rename tau A.
Proof. intro H; exact (@extRen_exp signature rho tau H A). Qed.

Lemma substitute_ext sigma tau A :
  (forall x, sigma x = tau x) -> substitute sigma A = substitute tau A.
Proof. intro H; exact (@ext_exp signature sigma tau H A). Qed.

Lemma convert_rename rho A B : convert A B -> convert (rename rho A) (rename rho B).
Proof. apply ren_equiv. Qed.

Lemma convert_substitute sigma A B :
  convert A B -> convert (substitute sigma A) (substitute sigma B).
Proof. apply subst_equiv. Qed.

Lemma convert_arrow A A' B B' :
  convert A A' -> convert B B' -> convert (tarrow A B) (tarrow A' B').
Proof. unfold convert, tarrow; intros H H'; now rewrite H, H'. Qed.

Lemma convert_all K A A' B B' :
  convert A A' -> convert B B' -> convert (tall K A B) (tall K A' B').
Proof. unfold convert, tall; intros H H'; now rewrite H, H'. Qed.

Definition scoped_ren (n m : nat) (rho : nat -> nat) :=
  forall x, x < n -> rho x < m.

Lemma scoped_ren_up n m rho : scoped_ren n m rho -> scoped_ren (S n) (S m) (up_ren rho).
Proof.
  unfold scoped_ren; intros H [|x] Hx.
  - change (0 < S m); lia.
  - change (S (rho x) < S m); specialize (H x); lia.
Qed.

Lemma kinding_rename D A K : kinding D A K ->
  forall E rho,
    (forall x L, nth_error D x = Some L -> nth_error E (rho x) = Some L) ->
    kinding E (rename rho A) K.
Proof.
  induction 1; intros E rho Hren; cbn [rename ren_exp tarrow tall tabs tapp tvar].
  - constructor; auto.
  - constructor.
  - constructor; auto.
  - constructor; auto. apply IHkinding2. intros [|x] L Hx; cbn in *; eauto.
  - constructor. apply IHkinding. intros [|x] M Hx; cbn in *; eauto.
  - econstructor; eauto.
Qed.

Lemma convert_instantiated_abs sigma rho A C :
  convert (tapp (rename rho (substitute sigma (tabs A))) C)
    (substitute (C .: (sigma >> rename rho)) A).
Proof.
  unfold convert, tapp, tabs, rename, substitute; cbn [subst_exp ren_exp].
  apply equiv_rel. constructor. unfold beta. now asimpl.
Qed.

Lemma kinding_substitute D A K : kinding D A K ->
  forall E sigma,
    (forall x L, nth_error D x = Some L -> kinding E (sigma x) L) ->
    kinding E (substitute sigma A) K.
Proof.
  induction 1; intros E sigma Hs; cbn [substitute subst_exp tarrow tall tabs tapp tvar].
  - auto.
  - constructor.
  - constructor; auto.
  - constructor; auto. apply IHkinding2. intros [|x] L Hx; cbn in *.
    + injection Hx as <-; apply k_var; reflexivity.
    + eapply kinding_rename; [eapply Hs; eauto |]. intros y M Hy; exact Hy.
  - constructor. apply IHkinding. intros [|x] M Hx; cbn in *.
    + injection Hx as <-; apply k_var; reflexivity.
    + eapply kinding_rename; [eapply Hs; eauto |]. intros y N Hy; exact Hy.
  - econstructor; eauto.
Qed.

Lemma kinding_partial_arrow D A K : ~ kinding D (app (@const signature CArrow) A) K.
Proof.
  intro H; inversion H; subst.
  match goal with Hc : kinding _ (const _) _ |- _ => inversion Hc end.
Qed.

Lemma kinding_partial_all D J A K : ~ kinding D (app (@const signature (CAll J)) A) K.
Proof.
  intro H; inversion H; subst.
  match goal with Hc : kinding _ (const _) _ |- _ => inversion Hc end.
Qed.

Lemma kinding_arrow_inv D A B : kinding D (tarrow A B) Star ->
  kinding D A Star /\ kinding D B Star.
Proof.
  intro H; inversion H; subst; [auto |].
  exfalso; eapply kinding_partial_arrow; eauto.
Qed.

Lemma kinding_all_inv D K A B : kinding D (tall K A B) Star ->
  kinding D A K /\ kinding (K :: D) B Star.
Proof.
  intro H; inversion H; subst; [auto |].
  exfalso; eapply kinding_partial_all; eauto.
Qed.
