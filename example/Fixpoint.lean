def f (x : Unit ⊕ Nat) : Nat :=
  match x with
  | .inl _ => 0
  | .inr n => n + 1

def g (x : Nat) : Unit ⊕ Nat :=
  match x with
  | 0 => .inl .unit
  | .succ n => .inr n

theorem f_g_id : ∀ x, f (g x) = x := by
  intro x
  cases x
  case zero => rfl
  case succ _ => rfl

theorem g_f_id : ∀ x, g (f x) = x := by sorry
