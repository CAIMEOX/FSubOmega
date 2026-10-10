From Fsubomega Require Export Projection.
From Fsubomega.FirstOrder Require Export Typing.
From Fsubomega.HigherOrder Require Export Typing.
Set Implicit Arguments.

Theorem typing_embedding G E t A : typing G E t A -> htyping (embed_context G) E t A.
Proof.
  induction 1.
  - apply ht_var; auto using embed_kinding.
  - apply ht_abs; auto using embed_kinding.
  - eapply ht_app; eauto.
  - apply ht_tyabs; auto using embed_kinding.
    now rewrite embed_extend in IHtyping.
  - eapply ht_tyapp; eauto using subtyping_embedding.
  - eapply ht_sub; eauto using subtyping_embedding.
Qed.

Lemma typing_projection_aux H E t A : htyping H E t A ->
  forall G, H = embed_context G -> context_wf G ->
    old_context (length G) E -> old_term (length G) t ->
    exists U, projects G A U /\ typing G E t U.
Proof.
  induction 1 as
    [H E x A Hx HK
    |H E A t B HK Hbody IHbody
    |H E f a A B Hf IHf Ha IHa
    |H E K A t B HK Hbody IHbody
    |H E K f C A B Hf IHf Hsub
    |H E t A B Ht IHt Hsub];
    intros G Heq HG HE Hterm; subst H.
  - assert (old (length G) A) as HA by (eapply old_context_lookup; eauto).
    exists A; split; auto using projects_old, ty_var.
  - destruct (old_abs_inv Hterm) as [HA Hold].
    destruct (IHbody G eq_refl HG (Forall_cons A HA HE) Hold) as (U & HU & Htu).
    exists (tarrow A U); split.
    + apply projects_arrow; auto using projects_old.
    + apply ty_abs; auto.
  - destruct (old_app_inv Hterm) as [Holdf Holda].
    destruct (IHf G eq_refl HG HE Holdf) as (Uf & HUf & Htf).
    destruct (IHa G eq_refl HG HE Holda) as (Ua & HUa & Hta).
    destruct (kinding_arrow_inv (htyping_regular Hf)) as [HKA HKB].
    destruct (projects_exists HG HKA) as (U & HU).
    destruct (projects_exists HG HKB) as (V & HV).
    assert (Uf = tarrow U V) as -> by (eapply projects_functional; eauto using projects_arrow).
    assert (Ua = U) as -> by (eapply projects_functional; eauto).
    exists V; split; auto. eapply ty_app; eauto.
  - destruct (old_tyabs_inv Hterm) as [-> [HA Hold]].
    assert (context_wf (extend A G)) as HG' by (constructor; auto).
    assert (old_context (length (extend A G)) (lift_context E)) as HE'.
    { rewrite extend_length; now apply old_context_lift. }
    assert (old_term (length (extend A G)) t) as Hold' by (now rewrite extend_length).
    destruct (IHbody _ (eq_sym (embed_extend G A)) HG' HE' Hold') as (U & HU & Htu).
    exists (tall Star A U); split.
    + apply projects_all; auto using projects_old.
    + apply ty_tyabs; auto.
  - destruct (old_tyapp_inv Hterm) as [-> [Hold HC]].
    destruct (IHf G eq_refl HG HE Hold) as (Uf & HUf & Htf).
    destruct (kinding_all_inv (htyping_regular Hf)) as [HKA HKB].
    destruct (projects_exists HG HKA) as (U & HU).
    assert (context_wf (extend U G)) as HG'.
    { constructor; [exact HG | exact (projected_old HU)]. }
    assert (kinding (kinds (embed_context (extend U G))) B Star) as HKB'.
    { rewrite embed_extend, kinds_extend; exact HKB. }
    destruct (projects_exists HG' HKB') as (V & HV).
    assert (Uf = tall Star U V) as -> by (eapply projects_functional; eauto using projects_all).
    exists (substitute (C .: tvar) V); split.
    + eapply projects_substitute; eauto.
    + eapply ty_tyapp; [exact Htf |].
      eapply projects_subtyping; eauto using projects_old.
  - destruct (IHt G eq_refl HG HE Hterm) as (U & HU & Htu).
    destruct (projects_exists HG (proj2 (hsub_regular Hsub))) as (V & HV).
    exists V; split; auto. eapply ty_sub; [exact Htu |].
    eapply projects_subtyping; eauto.
Qed.

Theorem typing_projection G E t A : context_wf G -> old_context (length G) E ->
  old_term (length G) t -> htyping (embed_context G) E t A ->
  exists U, projects G A U /\ typing G E t U.
Proof. intros; eapply typing_projection_aux; eauto. Qed.

Theorem typing_reflection G E t A : context_wf G -> old_context (length G) E ->
  old_term (length G) t -> old (length G) A ->
  htyping (embed_context G) E t A -> typing G E t A.
Proof.
  intros HG HE Ht HA Hty.
  destruct (typing_projection HG HE Ht Hty) as (U & HU & Htu).
  assert (U = A) as -> by (eapply projects_functional; eauto using projects_old).
  exact Htu.
Qed.

Theorem typing_conservative G E t A : context_wf G -> old_context (length G) E ->
  old_term (length G) t -> old (length G) A ->
  (htyping (embed_context G) E t A <-> typing G E t A).
Proof. intros; split; eauto using typing_reflection, typing_embedding. Qed.
