From Fsubomega Require Export Prelude.
Set Implicit Arguments.

(** Simple kinds. Bounds never participate in kind equality. *)
Inductive kind :=
| Star
| KArr (domain codomain : kind).

Fixpoint simple_kind (K : kind) : terms.type :=
  match K with
  | Star => typevar 0
  | KArr K L => arr (simple_kind K) (simple_kind L)
  end.

(** Reuse the library's binding algebra. The proper-type constructors are
    represented by reserved constants; [kinding] below admits only their
    fully applied forms. The lambda in [tall] represents its bound variable. *)
Inductive symbol := CTop | CArrow | CAll (K : kind).

Definition symbol_eq_dec : forall x y : symbol, {x = y} + {x <> y}.
Proof. decide equality; decide equality. Defined.

Definition symbol_type (c : symbol) : terms.type :=
  match c with
  | CTop => simple_kind Star
  | CArrow => arr (simple_kind Star) (arr (simple_kind Star) (simple_kind Star))
  | CAll K => arr (simple_kind K)
      (arr (arr (simple_kind K) (simple_kind Star)) (simple_kind Star))
  end.

Definition signature : Const :=
  {| const_type := symbol; const_dis := symbol_eq_dec; ctype := symbol_type |}.

Abbreviation ty := (exp signature).
Definition tvar : nat -> ty := var_exp.
Definition ttop : ty := @const signature CTop.
Definition tarrow (A B : ty) : ty := app (app (@const signature CArrow) A) B.
Definition tall (K : kind) (A B : ty) : ty :=
  app (app (@const signature (CAll K)) A) (lam B).
Definition tabs : ty -> ty := lam.
Definition tapp : ty -> ty -> ty := app.

Definition rename := @ren_exp signature.
Definition substitute := @subst_exp signature.
Definition lift := @up_exp_exp signature.
Definition convert := equiv (@step signature).

Fixpoint top (K : kind) : ty :=
  match K with Star => ttop | KArr _ L => tabs (top L) end.

Inductive kinding (D : list kind) : ty -> kind -> Prop :=
| k_var x K : nth_error D x = Some K -> kinding D (tvar x) K
| k_top : kinding D ttop Star
| k_arrow A B : kinding D A Star -> kinding D B Star ->
    kinding D (tarrow A B) Star
| k_all K A B : kinding D A K -> kinding (K :: D) B Star ->
    kinding D (tall K A B) Star
| k_abs K L A : kinding (K :: D) A L -> kinding D (tabs A) (KArr K L)
| k_app K L F A : kinding D F (KArr K L) -> kinding D A K ->
    kinding D (tapp F A) L.

Lemma kinding_top D K : kinding D (top K) K.
Proof. induction K in D |- *; cbn; constructor; auto. Qed.

Lemma rename_top rho K : rename rho (top K) = top K.
Proof.
  unfold rename; induction K in rho |- *.
  - reflexivity.
  - change (lam (ren_exp (up_ren rho) (top K2)) = lam (top K2)).
    now rewrite IHK2.
Qed.

Lemma substitute_top sigma K : substitute sigma (top K) = top K.
Proof.
  unfold substitute; induction K in sigma |- *.
  - reflexivity.
  - change (lam (subst_exp (lift sigma) (top K2)) = lam (top K2)).
    now rewrite IHK2.
Qed.

Lemma convert_beta A B : convert (tapp (tabs A) B) (substitute (B .: tvar) A).
Proof. apply equiv_rel. constructor. reflexivity. Qed.
