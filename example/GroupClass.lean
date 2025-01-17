class Group (G : Type) : Type where
  mul : G → G → G
  one : G
  inv : G → G
  assoc (a b c : G) : mul a (mul b c) = mul (mul a b) c
  one_mul (a : G) : mul one a = a
  inv_mul_cancel (a : G) : mul (inv a) a = one

open Group
#check mul
theorem mul_inv_cancel {G : Type} [Group G] (a : G) : mul a (inv a) = one := sorry
