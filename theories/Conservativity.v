From Fsubomega Require Export Embedding.
From Fsubomega.Fundamental Require Export Subtyping.
Set Implicit Arguments.

Lemma identity_realizes G : context_wf G -> realizes (embed_context G) G tvar.
Proof.
  intros HG x K A Hx; unfold embed_context in Hx; rewrite nth_error_map in Hx.
  destruct (nth_error G x) as [U|] eqn: HU; cbn in Hx; try discriminate.
  injection Hx as <- <-.
  rewrite substitute_id, (erase_old (context_wf_bounds HG x HU)).
  apply related_old, sub_var; eauto using context_wf_bounds.
Qed.

(** Stronger than reflection: arbitrary higher-order endpoints can be
    projected, as long as the ambient context is from the old language. *)
Theorem subtyping_projection G A B : context_wf G ->
  hsub (embed_context G) A B Star ->
  exists U V, convert (erase A) U /\ convert (erase B) V /\ sub G U V.
Proof.
  intros HG Hsub.
  pose proof (subtyping_fundamental Hsub (identity_realizes HG)) as H.
  now rewrite !substitute_id in H.
Qed.

Theorem subtyping_reflection G A B : context_wf G ->
  old (length G) A -> old (length G) B ->
  hsub (embed_context G) A B Star -> sub G A B.
Proof.
  intros HG HA HB Hsub.
  destruct (subtyping_projection HG Hsub) as (U & V & HU & HV & HUV).
  rewrite (erase_old HA) in HU; rewrite (erase_old HB) in HV.
  assert (A = U) as ->.
  { eapply old_convert_eq; [exact HA | exact (proj1 (sub_regular HUV)) | exact HU]. }
  assert (B = V) as ->.
  { eapply old_convert_eq; [exact HB | exact (proj2 (sub_regular HUV)) | exact HV]. }
  exact HUV.
Qed.

Theorem subtyping_conservative G A B : context_wf G ->
  old (length G) A -> old (length G) B ->
  (hsub (embed_context G) A B Star <-> sub G A B).
Proof.
  intros; split; eauto using subtyping_reflection, subtyping_embedding.
Qed.

(** Normalization of the erased proper-type language, obtained from the
    kinding fundamental lemma. No algorithm for subtyping is involved. *)
Theorem projection_exists G A : context_wf G -> kinding (kinds (embed_context G)) A Star ->
  exists U, old (length G) U /\ convert (erase A) U.
Proof.
  intros HG HA.
  pose proof (kinding_fundamental HA (realizes_semantic (identity_realizes HG))) as H.
  rewrite substitute_id in H.
  destruct (related_base_representative H) as (U & HU & Hwf); eauto.
Qed.

Theorem projection_unique (G : context) A U V :
  old (length G) U -> old (length G) V ->
  convert (erase A) U -> convert (erase A) V -> U = V.
Proof.
  intros HU HV HA HB; eapply old_convert_eq; [exact HU | exact HV |].
  transitivity (erase A); [symmetry; exact HA | exact HB].
Qed.
