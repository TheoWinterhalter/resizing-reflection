(** Global definitions of de Bruijn indices and PTS rules. *)

Definition Vars := nat.

Definition Sorts := nat.
Definition Ax : Sorts -> Sorts -> Type :=
  fun s1 s2 => s1 < s2.
Definition Rel : Sorts -> Sorts -> Sorts -> Type :=
  fun s1 s2 s3 => s1 <= s3 /\ s2 <= s3.


