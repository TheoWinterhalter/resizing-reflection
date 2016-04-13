Definition exo1 : true <> false :=
  fun b =>
    match b in _ = y
          return (match y with
                   | true => True
                   | false => False
                 end)
    with
      | eq_refl => I
    end.

(* Definition exo2 : forall (b : bool) (p q : true = b), p = q := *)
(*   fun b p q => *)
(*     match p as e in (_ = b) return *)
(*           match b with *)
(*             | true => match q as f in (_ = true) *)
(*                      with eq_refl => e = eq_refl end *)
(*             | false => False *)
(*           end *)
(*     with eq_refl => *)
(*          match q as f in (_ = true) return eq_refl = f *)
(*          with eq_refl => eq_refl end *)
(*     end. *)

(* Definition exo2 : forall (b : bool) (p q : true = b), p = q := *)
(*   fun b p q => *)
(*     match p as e in (_ = b) return *)
(*           match q as f in (_ = c) *)
(*           with eq_refl => e = e end *)
(*     with eq_refl => match q as f in (_ = true) return eq_refl = f *)
(*                    with eq_refl => eq_refl *)
(*                    end *)
(*     end. *)

Inductive Vec (A : Type) : nat -> Type :=
| nil : Vec A 0
| cons : forall {n} (x : A) (v : Vec A n), Vec A (S n).

Arguments nil {A}.
Arguments cons {A n} x v.

Definition exo3 {A} : forall v : Vec A 0, v = nil :=
  fun v =>
    match v as u in Vec _ p return
          match p with
            | 0 => fun w => w = nil
            | S m => fun _ => True
          end u
    with
      | nil => eq_refl
      | @cons _ m x w => I
    end.

Fixpoint exo4 {A} :
  forall P : (forall n, Vec A n -> Vec A n -> Type),
    P 0 nil nil ->
    (forall n x y v1 v2, P n v1 v2 -> P (S n) (cons x v1) (cons y v2)) ->
    forall n v1 v2, P n v1 v2 :=
  fun P P0 ihP n v1 v2 =>
    match n with
      | 0 => match v1 as u1 in Vec _ p return
                  match v2 as u2 in Vec _ q return
                        match p with
                          | 0 => fun w1 w2 => P 0 w1 w2
                          | S m => fun _ _ => True
                        end u1 u2
                  with
                    | nil => P0
                    | cons _ _ => I
                  end
            with
              | nil => match v2 as u2 in Vec _ q return
                            match q with
                              | 0 => fun w => P 0 nil w
                              | S m => fun _ => True
                            end u2
                      with
                        | nil => P0
                        | cons _ _ => I
                      end
              | cons _ _ => I
            end
      | S m => _
    end.

