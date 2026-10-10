From Fsubomega Require Import TypingConservativity.
Set Implicit Arguments.

Definition endo := tarrow ttop ttop.

Lemma old_endo n : old n endo.
Proof. constructor; constructor. Qed.

Lemma kinding_endo D : kinding D endo Star.
Proof. constructor; constructor. Qed.

(** The bounds really differ: this exercises the full quantifier rule. *)
Example full_quantifier : sub [] (tall Star ttop ttop) (tall Star endo ttop).
Proof. apply sub_all; [apply sub_top, old_endo | apply sub_refl, old_top]. Qed.

(** A declarative cut can contain a type operator application even though
    both endpoints and the context belong to the second-order language. *)
Example higher_order_cut : hsub [] endo ttop Star.
Proof.
  eapply hs_trans with (B := tapp (tabs (tvar 0)) endo).
  - apply hs_convert.
    + apply kinding_endo.
    + eapply k_app; [apply k_abs, k_var; reflexivity | apply kinding_endo].
    + symmetry; apply convert_beta.
  - change (hsub [] (tapp (tabs (tvar 0)) endo) (top Star) Star).
    apply hs_top; eapply k_app; [apply k_abs, k_var; reflexivity | apply kinding_endo].
Qed.

Example reflected_cut : sub [] endo ttop.
Proof.
  eapply subtyping_reflection; [constructor | apply old_endo | constructor |].
  exact higher_order_cut.
Qed.

Definition operator_quantifier :=
  tall (KArr Star Star) (top (KArr Star Star)) (tapp (tvar 0) ttop).

Example higher_quantifier_kinded : kinding [] operator_quantifier Star.
Proof.
  apply k_all; [apply kinding_top |].
  eapply k_app; [apply k_var; reflexivity | constructor].
Qed.

Example higher_quantifier_erased : convert (erase operator_quantifier) ttop.
Proof. apply erase_all_higher. Qed.

Definition polymorphic_identity := tm_tyabs Star ttop (tm_abs (tvar 0) (tm_var 0)).
Definition identity_type := tall Star ttop (tarrow (tvar 0) (tvar 0)).

Example identity_in_old_system : typing [] [] polymorphic_identity identity_type.
Proof.
  apply ty_tyabs; [constructor |].
  apply ty_abs; [apply old_var; cbn; lia |].
  apply ty_var; [reflexivity | apply old_var; cbn; lia].
Qed.

Example identity_in_higher_system : htyping [] [] polymorphic_identity identity_type.
Proof. exact (typing_embedding identity_in_old_system). Qed.

Example identity_instantiated : typing [] [] (tm_tyapp Star polymorphic_identity endo) (tarrow endo endo).
Proof.
  change (typing [] [] (tm_tyapp Star polymorphic_identity endo)
    (substitute (endo .: tvar) (tarrow (tvar 0) (tvar 0)))).
  eapply ty_tyapp; [exact identity_in_old_system | apply sub_top, old_endo].
Qed.

Lemma top_has_no_other_supertype G A B : sub G A B -> A = ttop -> B = ttop.
Proof. induction 1; intro Heq; try assumption; try reflexivity; try discriminate; auto. Qed.

(** Negative integration check: adding higher-order intermediates does not
    make Top a subtype of an arrow. *)
Example no_top_to_arrow : ~ hsub [] ttop endo Star.
Proof.
  intro H; assert (sub [] ttop endo) as Hs.
  { eapply subtyping_reflection; [constructor | constructor | apply old_endo | exact H]. }
  pose proof (top_has_no_other_supertype Hs eq_refl) as Hbad; discriminate.
Qed.
