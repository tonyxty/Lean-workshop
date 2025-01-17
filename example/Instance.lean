class Group (G : Type) : Type where
  mul : G → G → G
  one : G
  inv : G → G
  assoc (a b c : G) : mul (mul a b) c = mul a (mul b c)
  one_mul (a : G) : mul one a = a
  inv_mul_cancel (a : G) : mul (inv a) a = one

open Group
instance : Group Int := {
  mul := (· + ·)
  one := 0
  inv := (-·)
  assoc := Int.add_assoc
  one_mul := Int.zero_add
  inv_mul_cancel := Int.add_left_neg
}

instance [Group G] [Group H] : Group (G × H) := {
  mul := fun (a₁, b₁) (a₂, b₂) => (mul a₁ a₂, mul b₁ b₂)
  one := (one, one)
  inv := fun (a, b) => (inv a, inv b)
  assoc := sorry
  one_mul := sorry
  inv_mul_cancel := sorry
}

def ProductGroup : Group (Int × Int) := inferInstance
