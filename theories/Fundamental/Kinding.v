From Fsubomega Require Export Erasure LogicalRelation.
Set Implicit Arguments.

Definition semantic_env (D : list kind) (G : context) (sigma : nat -> ty) :=
  forall x K, nth_error D x = Some K -> related K G (sigma x) (sigma x).

Lemma semantic_env_rename D G E rho sigma : context_ren G E rho ->
  semantic_env D G sigma -> semantic_env D E (sigma >> rename rho).
Proof. intros Hr H x K Hx; eapply related_rename; eauto. Qed.

Lemma semantic_env_cons D G sigma K C :
  semantic_env D G sigma -> related K G C C -> semantic_env (K :: D) G (C .: sigma).
Proof. intros H HC [|x] L Hx; cbn in *; [now injection Hx as <- | eauto]. Qed.

Lemma related_fresh G U : related Star (extend U G) (tvar 0) (tvar 0).
Proof.
  apply related_old, sub_refl, old_var; rewrite extend_length; lia.
Qed.

Lemma semantic_env_lift D G sigma U : semantic_env D G sigma ->
  semantic_env (Star :: D) (extend U G) (lift sigma).
Proof.
  intro H; apply semantic_env_cons.
  - eapply semantic_env_rename; [apply context_ren_shift | exact H].
  - apply related_fresh.
Qed.

(** This lemma simultaneously supplies the normalization witnesses needed
    for reflexivity and validates type-level beta computation. *)
Theorem kinding_fundamental D A K : kinding D A K ->
  forall G sigma, semantic_env D G sigma -> related K G (interpret sigma A) (interpret sigma A).
Proof.
  induction 1; intros G sigma Henv.
  - apply Henv; assumption.
  - apply related_old, sub_refl, old_top.
  - specialize (IHkinding1 _ _ Henv); specialize (IHkinding2 _ _ Henv).
    destruct (related_base_representative IHkinding1) as (U & HU & HwfU).
    destruct (related_base_representative IHkinding2) as (V & HV & HwfV).
    exists (tarrow U V), (tarrow U V); repeat split.
    + apply convert_arrow; assumption.
    + apply convert_arrow; assumption.
    + apply sub_refl, old_arrow; assumption.
  - destruct K as [|K L].
    + destruct (related_base_representative (IHkinding1 _ _ Henv)) as (U & HU & HwfU).
      specialize (IHkinding2 _ _ (semantic_env_lift U Henv)).
      destruct (related_base_representative IHkinding2) as (V & HV & HwfV).
      rewrite extend_length in HwfV.
      rewrite erase_all_base.
      exists (tall Star U V), (tall Star U V); repeat split.
      * apply convert_all; assumption.
      * apply convert_all; assumption.
      * apply sub_refl, old_all; assumption.
    + assert (convert (interpret sigma (tall (KArr K L) A B)) ttop) as Htop.
      { pose proof (convert_substitute sigma (erase_all_higher K L A B)) as Hc.
        exact Hc. }
      exists ttop, ttop; repeat split; auto using sub_refl, old_top.
  - intros E rho Hr C HC. rewrite erase_abs.
    eapply related_convert.
    + apply convert_instantiated_abs.
    + apply convert_instantiated_abs.
    + apply IHkinding, semantic_env_cons; [| exact HC].
      eapply semantic_env_rename; eauto.
  - eapply related_apply; [apply IHkinding1 | apply IHkinding2]; exact Henv.
Qed.
