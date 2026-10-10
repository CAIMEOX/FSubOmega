From Fsubomega Require Export Binding.
Set Implicit Arguments.

Definition hcontext := list (kind * ty).
Definition kinds (G : hcontext) := map fst G.
Definition shift_binding (b : kind * ty) := (fst b, rename shift (snd b)).
Definition hextend K A (G : hcontext) := map shift_binding ((K, A) :: G).

Lemma kinds_extend K A G : kinds (hextend K A G) = K :: kinds G.
Proof. unfold kinds, hextend; cbn. rewrite map_map. reflexivity. Qed.

Inductive hcontext_wf : hcontext -> Prop :=
| hctx_nil : hcontext_wf []
| hctx_cons G K A : hcontext_wf G -> kinding (kinds G) A K ->
    hcontext_wf (hextend K A G).

(** Full bounded quantification, unbounded operator abstraction, pointwise
    application, and beta conversion. No variance rule for arguments. *)
Inductive hsub (G : hcontext) : ty -> ty -> kind -> Prop :=
| hs_refl A K : kinding (kinds G) A K -> hsub G A A K
| hs_top A K : kinding (kinds G) A K -> hsub G A (top K) K
| hs_var x A K : nth_error G x = Some (K, A) -> kinding (kinds G) A K ->
    hsub G (tvar x) A K
| hs_trans A B C K : hsub G A B K -> hsub G B C K -> hsub G A C K
| hs_arrow A A' B B' : hsub G A' A Star -> hsub G B B' Star ->
    hsub G (tarrow A B) (tarrow A' B') Star
| hs_all A A' B B' K : hsub G A' A K -> hsub (hextend K A' G) B B' Star ->
    hsub G (tall K A B) (tall K A' B') Star
| hs_abs A B K L : hsub (hextend K (top K) G) A B L ->
    hsub G (tabs A) (tabs B) (KArr K L)
| hs_app F F' A K L : hsub G F F' (KArr K L) -> kinding (kinds G) A K ->
    hsub G (tapp F A) (tapp F' A) L
| hs_convert A B K : kinding (kinds G) A K -> kinding (kinds G) B K ->
    convert A B -> hsub G A B K.

Lemma hsub_regular G A B K : hsub G A B K ->
  kinding (kinds G) A K /\ kinding (kinds G) B K.
Proof.
  induction 1.
  - auto.
  - split; auto using kinding_top.
  - split; auto. apply k_var; unfold kinds. now rewrite nth_error_map, H.
  - tauto.
  - destruct IHhsub1, IHhsub2; split; constructor; auto.
  - rewrite kinds_extend in IHhsub2. destruct IHhsub1, IHhsub2; split; constructor; auto.
  - rewrite kinds_extend in IHhsub. destruct IHhsub; split; constructor; auto.
  - destruct IHhsub; split; econstructor; eauto.
  - auto.
Qed.
