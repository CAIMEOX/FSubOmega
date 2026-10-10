From Fsubomega.Fundamental Require Export Contexts.
Set Implicit Arguments.

(** Soundness in the old syntactic preorder. Transitivity of the higher-order
    system is interpreted directly, without any restriction on its cut type. *)
Theorem subtyping_fundamental G A B K : hsub G A B K ->
  forall D sigma, realizes G D sigma -> related K D (interpret sigma A) (interpret sigma B).
Proof.
  induction 1; intros D sigma Hr.
  - eapply kinding_fundamental; eauto using realizes_semantic.
  - rewrite erase_top_kind, substitute_top.
    apply related_top. eapply kinding_fundamental; eauto using realizes_semantic.
  - apply Hr; exact H.
  - eapply related_trans; eauto.
  - destruct (IHhsub1 _ _ Hr) as (U & V & HU & HV & HUV).
    destruct (IHhsub2 _ _ Hr) as (W & Z & HW & HZ & HWZ).
    exists (tarrow V W), (tarrow U Z); repeat split.
    + apply convert_arrow; assumption.
    + apply convert_arrow; assumption.
    + apply sub_arrow; assumption.
  - destruct K as [|K L].
    + destruct (IHhsub1 _ _ Hr) as (U & V & HU & HV & HUV).
      pose proof (realizes_base_extend A' Hr HU (proj1 (sub_regular HUV))) as Hext.
      destruct (IHhsub2 _ _ Hext) as (W & Z & HW & HZ & HWZ).
      rewrite !erase_all_base.
      exists (tall Star V W), (tall Star U Z); repeat split.
      * apply convert_all; assumption.
      * apply convert_all; assumption.
      * apply sub_all; assumption.
    + exists ttop, ttop; repeat split.
      * exact (convert_substitute sigma (erase_all_higher K L A B)).
      * exact (convert_substitute sigma (erase_all_higher K L A' B')).
      * apply sub_refl, old_top.
  - intros E rho Hren C HC. rewrite !erase_abs.
    eapply related_convert.
    + apply convert_instantiated_abs.
    + apply convert_instantiated_abs.
    + apply IHhsub, realizes_cons.
      * eapply realizes_rename; eauto.
      * rewrite erase_top_kind, substitute_top. now apply related_top.
  - eapply related_apply; [eapply IHhsub; exact Hr |].
    eapply kinding_fundamental; eauto using realizes_semantic.
  - eapply related_convert.
    + reflexivity.
    + symmetry. apply convert_substitute, erase_convert; exact H1.
    + eapply kinding_fundamental; eauto using realizes_semantic.
Qed.
