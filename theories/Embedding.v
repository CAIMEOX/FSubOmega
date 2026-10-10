From Fsubomega.FirstOrder Require Export Subtyping.
From Fsubomega.HigherOrder Require Export Subtyping.
From Fsubomega Require Export Erasure.
Set Implicit Arguments.

Definition embed_context (G : context) : hcontext := map (fun A => (Star, A)) G.

Lemma embed_kinds G : kinds (embed_context G) = repeat Star (length G).
Proof.
  unfold kinds, embed_context; rewrite map_map; induction G; cbn.
  - reflexivity.
  - f_equal; exact IHG.
Qed.

Lemma embed_extend G A : embed_context (extend A G) = hextend Star A (embed_context G).
Proof.
  unfold embed_context, extend, hextend; cbn. f_equal.
  rewrite !map_map; reflexivity.
Qed.

Lemma embed_kinding G A : old (length G) A -> kinding (kinds (embed_context G)) A Star.
Proof. rewrite embed_kinds; apply old_kinding. Qed.

Lemma embed_context_wf G : context_wf G -> hcontext_wf (embed_context G).
Proof.
  induction 1; [constructor |]. rewrite embed_extend.
  constructor; auto using embed_kinding.
Qed.

Lemma erase_old n A : old n A -> erase A = A.
Proof.
  induction 1; try reflexivity.
  - now rewrite erase_arrow, IHold1, IHold2.
  - now rewrite erase_all_base, IHold1, IHold2.
Qed.

Theorem subtyping_embedding G A B : sub G A B -> hsub (embed_context G) A B Star.
Proof.
  induction 1.
  - apply hs_refl; now apply embed_kinding.
  - change (hsub (embed_context G) A (top Star) Star).
    apply hs_top; now apply embed_kinding.
  - eapply hs_var; [| now apply embed_kinding].
    unfold embed_context; now rewrite nth_error_map, H.
  - eapply hs_trans; eauto.
  - apply hs_arrow; auto.
  - apply hs_all; auto. now rewrite embed_extend in IHsub2.
Qed.
