From Fsubomega Require Export Conservativity.
Set Implicit Arguments.

(** A proof-carrying normal form, expressed relationally so no choice axiom
    or executable normalization function is needed. *)
Record projects (G : context) (A U : ty) : Prop := {
  projected_old : old (length G) U;
  projected_convert : convert (erase A) U
}.

Lemma projects_exists G A : context_wf G -> kinding (kinds (embed_context G)) A Star ->
  exists U, projects G A U.
Proof. intros HG HA; destruct (projection_exists HG HA) as (U & HU & Hc); exists U; constructor; auto. Qed.

Lemma projects_old G A : old (length G) A -> projects G A A.
Proof. intro H; constructor; auto. rewrite (erase_old H); reflexivity. Qed.

Lemma projects_functional G A U V : projects G A U -> projects G A V -> U = V.
Proof. intros [HU HcU] [HV HcV]; eapply projection_unique; eauto. Qed.

Lemma projects_arrow G A B U V : projects G A U -> projects G B V ->
  projects G (tarrow A B) (tarrow U V).
Proof.
  intros [HU HcU] [HV HcV]; constructor; [constructor; auto |].
  rewrite erase_arrow; now apply convert_arrow.
Qed.

Lemma projects_all G A B U V : projects G A U -> projects (extend U G) B V ->
  projects G (tall Star A B) (tall Star U V).
Proof.
  intros [HU HcU] [HV HcV]; constructor.
  - constructor; auto. now rewrite extend_length in HV.
  - rewrite erase_all_base; now apply convert_all.
Qed.

Lemma projects_substitute G U B V C : projects (extend U G) B V -> old (length G) C ->
  projects G (substitute (C .: tvar) B) (substitute (C .: tvar) V).
Proof.
  intros [HV HcV] HC; constructor.
  - rewrite extend_length in HV. eapply old_substitute; [exact HV |].
    intros [|x] Hx; cbn; auto. apply old_var; lia.
  - rewrite erase_substitute.
    assert (forall x, ((C .: tvar) >> erase) x = (C .: tvar) x) as Heq.
    { intros [|x]; cbn; [exact (erase_old HC) | reflexivity]. }
    pose proof (convert_substitute (C .: tvar) HcV) as Hconverted.
    pose proof (substitute_ext _ _ (erase B) Heq) as Hsubst.
    rewrite <-Hsubst in Hconverted. exact Hconverted.
Qed.

Lemma projects_subtyping G A B U V : context_wf G ->
  projects G A U -> projects G B V -> hsub (embed_context G) A B Star -> sub G U V.
Proof.
  intros HG HU HV Hsub.
  destruct (subtyping_projection HG Hsub) as (U' & V' & HcU & HcV & HUV).
  assert (U = U') as ->.
  { eapply projects_functional; [exact HU |]. constructor; auto.
    exact (proj1 (sub_regular HUV)). }
  assert (V = V') as ->.
  { eapply projects_functional; [exact HV |]. constructor; auto.
    exact (proj2 (sub_regular HUV)). }
  exact HUV.
Qed.
