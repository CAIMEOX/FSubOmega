From Fsubomega Require Import TypingConservativity.

(** This output is checked by [dune runtest]. Any new assumption changes the
    golden file, even when ordinary compilation would still succeed. *)
Print Assumptions subtyping_conservative.
Print Assumptions typing_conservative.
