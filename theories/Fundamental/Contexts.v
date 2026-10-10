From Fsubomega.Fundamental Require Export Kinding.
From Fsubomega.HigherOrder Require Export Subtyping.
Set Implicit Arguments.

Definition realizes (G : hcontext) (D : context) (sigma : nat -> ty) :=
  forall x K A, nth_error G x = Some (K, A) ->
    related K D (sigma x) (interpret sigma A).

Lemma realizes_semantic G D sigma : realizes G D sigma -> semantic_env (kinds G) D sigma.
Proof.
  intros H x K Hx. unfold kinds in Hx; rewrite nth_error_map in Hx.
  destruct (nth_error G x) as [[L A]|] eqn: Hlookup; cbn in Hx; try discriminate.
  injection Hx as <-. exact (proj1 (related_regular L D _ _ (H _ _ _ Hlookup))).
Qed.

Lemma realizes_rename G D E rho sigma : context_ren D E rho ->
  realizes G D sigma -> realizes G E (sigma >> rename rho).
Proof.
  intros Hr H x K A Hx; unfold funcomp at 1.
  rewrite <-rename_substitute. apply related_rename with (G := D); auto.
Qed.

Lemma realizes_cons G D sigma K A C :
  realizes G D sigma -> related K D C (interpret sigma A) ->
  realizes (hextend K A G) D (C .: sigma).
Proof.
  intros H HC [|x] L B Hx; unfold hextend in Hx; cbn in Hx.
  - injection Hx as <- <-. rewrite interpret_shift; exact HC.
  - rewrite nth_error_map in Hx.
    destruct (nth_error G x) as [[M U]|] eqn: HU; cbn in Hx; try discriminate.
    injection Hx as <- <-. rewrite interpret_shift. apply H; exact HU.
Qed.

Lemma realizes_base_extend G D sigma A U : realizes G D sigma ->
  convert (interpret sigma A) U -> old (length D) U ->
  realizes (hextend Star A G) (extend U D) (lift sigma).
Proof.
  intros H HA HU; apply realizes_cons.
  - eapply realizes_rename; [apply context_ren_shift | exact H].
  - exists (tvar 0), (rename shift U); repeat split; [reflexivity | |].
    + rewrite <-rename_substitute; now apply convert_rename.
    + apply sub_var; [reflexivity |].
      rewrite extend_length. eapply old_rename; [exact HU |].
      intros x Hx; change (S x < S (length D)); lia.
Qed.
