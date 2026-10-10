From Fsubomega.FirstOrder Require Export Subtyping.
Set Implicit Arguments.

(** At base kind we keep a concrete old representative on each side, up to
    beta conversion. At arrow kinds we test on the same computable argument.
    This is a partial equivalence-style logical relation: reflexivity for
    well-kinded expressions is proved by the fundamental lemma, not assumed. *)
Fixpoint related (K : kind) (G : context) (A B : ty) : Prop :=
  match K with
  | Star => exists A' B', convert A A' /\ convert B B' /\ sub G A' B'
  | KArr K L => forall D rho, context_ren G D rho ->
      forall C, related K D C C ->
      related L D (tapp (rename rho A) C) (tapp (rename rho B) C)
  end.

Lemma related_old G A B : sub G A B -> related Star G A B.
Proof. intro H; exists A, B; repeat split; try reflexivity; exact H. Qed.

Lemma related_regular K G A B : related K G A B ->
  related K G A A /\ related K G B B.
Proof.
  induction K as [|K IHK L IHL] in G, A, B |- *; cbn.
  - intros (A' & B' & HA & HB & Hsub).
    destruct (sub_regular Hsub) as [HwfA HwfB]; split.
    + exists A', A'; repeat split; auto using sub_refl.
    + exists B', B'; repeat split; auto using sub_refl.
  - intros H; split; intros D rho Hr C HC;
      specialize (H D rho Hr C HC); now apply IHL in H as [H1 H2].
Qed.

Lemma related_convert K G A B A' B' :
  convert A' A -> convert B' B -> related K G A B -> related K G A' B'.
Proof.
  induction K as [|K IHK L IHL] in G, A, B, A', B' |- *; cbn.
  - intros HA HB (U & V & HU & HV & Hsub).
    exists U, V; repeat split; try assumption.
    + transitivity A; assumption.
    + transitivity B; assumption.
  - intros HA HB H D rho Hr C HC; eapply IHL; [| | eapply H; eauto].
    + unfold convert, tapp; apply equiv_app_proper; [now apply convert_rename | reflexivity].
    + unfold convert, tapp; apply equiv_app_proper; [now apply convert_rename | reflexivity].
Qed.

Lemma related_rename K G D rho A B : context_ren G D rho ->
  related K G A B -> related K D (rename rho A) (rename rho B).
Proof.
  induction K as [|K IHK L IHL] in G, D, rho, A, B |- *; cbn.
  - intros Hr (U & V & HU & HV & Hsub).
    exists (rename rho U), (rename rho V); repeat split.
    + now apply convert_rename.
    + now apply convert_rename.
    + eapply sub_rename; eauto.
  - intros Hr H E tau Ht C HC. rewrite !rename_comp.
    apply H; [eapply context_ren_comp; eauto | exact HC].
Qed.

Lemma related_trans K G A B C : related K G A B -> related K G B C -> related K G A C.
Proof.
  induction K as [|K IHK L IHL] in G, A, B, C |- *; cbn.
  - intros (U & V & HU & HV & H1) (V' & W & HV' & HW & H2).
    assert (V = V') as ->.
    { eapply old_convert_eq.
      - exact (proj2 (sub_regular H1)).
      - exact (proj1 (sub_regular H2)).
      - transitivity B; [symmetry; exact HV | exact HV']. }
    exists U, W; repeat split; auto. eapply sub_trans; eauto.
  - intros H1 H2 D rho Hr T HT; eapply IHL; [eapply H1 | eapply H2]; eauto.
Qed.

Lemma related_base_representative G A : related Star G A A ->
  exists U, convert A U /\ old (length G) U.
Proof.
  intros (U & V & HU & HV & Hsub); exists U; split; auto.
  exact (proj1 (sub_regular Hsub)).
Qed.

Lemma related_top K G A : related K G A A -> related K G A (top K).
Proof.
  induction K as [|K IHK L IHL] in G, A |- *.
  - intros H; destruct (related_base_representative H) as (U & HU & Hwf).
    exists U, ttop; repeat split; auto using sub_top; reflexivity.
  - intros H D rho Hr C HC.
    specialize (H D rho Hr C HC). apply IHL in H.
    eapply related_convert; [reflexivity | | exact H].
    rewrite rename_top. change (convert (tapp (tabs (top L)) C) (top L)).
    pose proof (convert_beta (top L) C) as HB.
    now rewrite substitute_top in HB.
Qed.

Lemma related_apply K L G F F' A :
  related (KArr K L) G F F' -> related K G A A -> related L G (tapp F A) (tapp F' A).
Proof.
  intros HF HA; specialize (HF G id (context_ren_id G) A HA).
  now rewrite !rename_id in HF.
Qed.
