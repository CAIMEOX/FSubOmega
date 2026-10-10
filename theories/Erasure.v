From Fsubomega Require Export Binding.
From Undecidability.HOU.concon Require Import conservativity_constants.
Set Implicit Arguments.

(** Erase only quantifiers over operators. Their two arguments (the bound
    and the abstracted body) are discarded by a closed lambda term. *)
Definition erase_symbol (c : symbol) : ty :=
  match c with
  | CAll (KArr _ _) => tabs (tabs ttop)
  | _ => @const signature c
  end.

Definition erase : ty -> ty := @subst_consts signature signature erase_symbol.

Abbreviation interpret sigma A := (substitute sigma (erase A)).

Lemma erase_symbol_rename rho c : rename rho (erase_symbol c) = erase_symbol c.
Proof. destruct c as [| | [|K L]]; reflexivity. Qed.

Lemma erase_var x : erase (tvar x) = tvar x.
Proof. reflexivity. Qed.

Lemma erase_top : erase ttop = ttop.
Proof. reflexivity. Qed.

Lemma erase_app F A : erase (tapp F A) = tapp (erase F) (erase A).
Proof. reflexivity. Qed.

Lemma erase_abs A : erase (tabs A) = tabs (erase A).
Proof.
  unfold erase, tabs; cbn. f_equal. f_equal.
  fext; intro c; apply erase_symbol_rename.
Qed.

Lemma erase_arrow A B : erase (tarrow A B) = tarrow (erase A) (erase B).
Proof. reflexivity. Qed.

Lemma erase_all_base A B : erase (tall Star A B) = tall Star (erase A) (erase B).
Proof. unfold tall.
  change (app (app (@const signature (CAll Star)) (erase A)) (erase (tabs B)) =
    app (app (@const signature (CAll Star)) (erase A)) (tabs (erase B))).
  now rewrite erase_abs.
Qed.

Lemma erase_all_higher K L A B :
  convert (erase (tall (KArr K L) A B)) ttop.
Proof.
  change (convert (tapp (tapp (tabs (tabs ttop)) (erase A)) (erase (tabs B))) ttop).
  unfold convert. transitivity (tapp (tabs ttop) (erase (tabs B))).
  - apply equiv_app_proper; [apply convert_beta | reflexivity].
  - apply convert_beta.
Qed.

Lemma erase_rename rho A : erase (rename rho A) = rename rho (erase A).
Proof.
  unfold erase, rename. rewrite <-ren_subst_consts_commute.
  f_equal. fext; intro c; symmetry; apply erase_symbol_rename.
Qed.

Lemma erase_substitute sigma A :
  erase (substitute sigma A) = substitute (sigma >> erase) (erase A).
Proof.
  induction A in sigma |- *.
  - reflexivity.
  - destruct c as [| | [|K L]]; reflexivity.
  - change (erase (tabs (substitute (lift sigma) A)) =
      substitute (sigma >> erase) (erase (tabs A))).
    rewrite !erase_abs.
    change (lam (erase (substitute (lift sigma) A)) =
      lam (substitute (lift (sigma >> erase)) (erase A))).
    apply f_equal. rewrite IHA. apply substitute_ext. intros [|x]; cbn; [reflexivity |].
    apply erase_rename.
  - change (tapp (erase (substitute sigma A1)) (erase (substitute sigma A2)) =
      tapp (substitute (sigma >> erase) (erase A1)) (substitute (sigma >> erase) (erase A2))).
    now rewrite IHA1, IHA2.
Qed.

Lemma erase_convert A B : convert A B -> convert (erase A) (erase B).
Proof. apply equiv_subst_consts; reflexivity. Qed.

Lemma erase_top_kind K : erase (top K) = top K.
Proof. induction K; cbn [top]; [reflexivity | now rewrite erase_abs, IHK2]. Qed.

Lemma interpret_shift C sigma A :
  interpret (C .: sigma) (rename shift A) = interpret sigma A.
Proof. rewrite erase_rename, substitute_rename; reflexivity. Qed.
