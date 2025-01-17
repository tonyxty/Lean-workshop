inductive N where
  | Z : N
  | S : N → N

open N

def Nadd (m n : N) : N :=
  match n with
  | Z => m
  | S n' => S (Nadd m n')

theorem Nzero_add : ∀ n, Nadd Z n = n := by
  intro n
  induction n
  case Z => rfl
  case S n' IH =>
    unfold Nadd
    rewrite [IH]
    rfl

theorem NS_add : ∀ m n, Nadd (S m) n = S (Nadd m n) := by
  intro m n
  induction n
  case Z => rfl
  case S n' IH =>
    unfold Nadd
    rewrite [IH]
    rfl
