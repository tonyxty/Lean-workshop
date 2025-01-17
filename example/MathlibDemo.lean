-- 本文件需要用 lake 建立一个项目并在其中安装 mathlib 后才能运行
import Mathlib

-- 使用 mathlib 中的定理
#check le_antisymm
#check le_min
#check min_le_left

example : ∀ {α : Type*} [LinearOrder α] (a b : α), min a b = min b a := by
  intro α _
  have : ∀ (x y : α), min x y ≤ min y x := by
    intro x y
    apply le_min
    · apply min_le_right
    · apply min_le_left
  intro a b
  apply le_antisymm
  · apply this
  · apply this

-- `dsimp`: 按定义展开（递归）
-- `linarith`: 处理线性规划
def UpperBound (f : ℝ → ℝ) (a : ℝ) := ∀ x, f x ≤ a

example {f g : ℝ → ℝ} {a b : ℝ} :
    UpperBound f a → UpperBound g b → UpperBound (f + g) (a + b) := by
  intro hf hg
--  dsimp [UpperBound] at *
  intro x
  dsimp
  -- rw [Pi.add_apply]
  linarith [hf x, hg x]

-- 不使用 tactic 证明
#check add_le_add
example {f g : ℝ → ℝ} {a b : ℝ}
    (hf : UpperBound f a) (hg : UpperBound g b) : UpperBound (f + g) (a + b) :=
  fun x => add_le_add (hf x) (hg x)

-- `rcases`: 深度展开归纳类型
-- `use`: 处理只有一个 constructor 的目标类型，常用于证明存在性
-- `ring_nf`: 去括号、合并同类项
-- `ring`: 对两边应用 `ring_nf` 后尝试 `rfl`
section

variable {α : Type u} [CommRing α]

/-- x is a sum of squares -/
def IsSOS (x : α) := ∃ a b, x = a ^ 2 + b ^ 2

example {x y : α} (hx : IsSOS x) (hy : IsSOS y) : IsSOS (x * y) := by
  dsimp [IsSOS] at *
  rcases hx with ⟨ a, b, hx ⟩
  rcases hy with ⟨ c, d, hy ⟩
  use a * c - b * d, a * d + b * c
  rw [hx, hy]
  ring

end

-- `simp`, `simp?`, `simp only`: 根据给定的等式改写目标（递归）
-- `@[simp]`, `simp` 数据库
example {c : ℝ} : Function.Surjective fun x => x + c := by
  unfold Function.Surjective
  intro y
  use y - c
  simp only [sub_add_cancel]

-- ⟨ ⟩: 不指名地使用唯一的 constructor
-- `by` tactic 可以作为子表达式
example {c : ℝ} : Function.Surjective fun x => x + c :=
  fun y => ⟨ y - c, by simp ⟩

-- Iff
#print Iff
#check Iff.mp

-- `¬p := p → False`
-- `rintro`: `intro` + `rcases` 的组合
-- `assumption`: 自动寻找合适的假设
-- `all_goals t`: 对所有目标执行某 tactic `t`
example {x y : ℝ} (h : x ≤ y) : ¬y ≤ x ↔ x ≠ y := by
  constructor
  -- · intro h e
  --   apply h
  --   rewrite [e]
  --   rfl
  · rintro h rfl
    apply h
    rfl
  · intro h₁ h₂
    apply h₁
    apply le_antisymm
    all_goals assumption

-- `exact`: 填入某表达式
-- `refine`: 填入某表达式，但把其中待补全的部分（未被解出的元变量）转化为新的目标
example {x y : ℝ} (h : x ≤ y) : ¬y ≤ x ↔ x ≠ y := by
  refine ⟨ fun h₁ h₂ => ?a, fun h₁ h₂ => ?b ⟩
  · rw [h₂] at h₁
    exact h₁ le_rfl
  · exact h₁ (le_antisymm h h₂)

-- `left`, `right`: 处理恰有两个 constructor 的目标类型，常用于证明析取
example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h
    left
    exact h
  · rw [abs_of_neg h]
    intro h
    right
    exact h

-- `decide`: 若命题可判定，则通过执行判定过程来证明之
example : 3 ≤ 4 := by
  decide

-- `trivial`: 根据目标命题的形式，反复使用 `True.intro`, `And.intro`, `rfl`, `assumption`, `decide`

-- 集合的处理
section
variable {α : Type*}
variable (s t u : Set α)
open Set

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  dsimp [subset_def] at *
  simp only [mem_inter_iff]
  rintro x ⟨ xs, xu ⟩
  exact ⟨ h x xs, xu ⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rintro x ⟨ xs, xu ⟩
  exact ⟨ h xs, xu ⟩

end

set_option pp.fieldNotation false
-- == 例：√2 是无理数
-- `t₁ <;> t₂`: 对 tactic t₁ 得到的所有目标都应用 tactic t₂
lemma even_of_even_sqr {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m := by
  rw [pow_two] at h
  rw [Nat.Prime.dvd_mul] at h
  · cases h <;> assumption
  · exact Nat.prime_two

-- `let`: 定义变量
example {m n : ℕ} (coprime_mn : Nat.Coprime m n) : m ^ 2 ≠ 2 * n ^ 2 := by
  intro sqr_eq
  have : 2 ∣ m := by
    apply even_of_even_sqr
    exact ⟨ _, sqr_eq ⟩
  let ⟨ k, meq ⟩ := this
  have : 2 * (2 * k ^ 2) = 2 * n ^ 2 := by
    rw [← sqr_eq, meq]
    ring
  have : 2 * k ^ 2 = n ^ 2 :=
    Nat.eq_of_mul_eq_mul_left (by decide) this
  have : 2 ∣ n := by
    apply even_of_even_sqr
    exact ⟨ _, this.symm ⟩
  have : 2 ∣ Nat.gcd m n := by
    apply Nat.dvd_gcd <;> assumption
  have : 2 ∣ 1 := by
    rwa [coprime_mn] at this
  norm_num at this

-- == 例：Gauss 整数
-- `@[ext]`: 生成对应的外延性定理
@[ext]
structure GaussInt where
  re : ℤ
  im : ℤ

set_option pp.fieldNotation true

#check GaussInt.ext

-- 对 `GaussInt` 使用 +, -, *, 0, 1 等符号
instance : Zero GaussInt := {
  zero := ⟨ 0, 0 ⟩
}

instance : One GaussInt := {
  one := ⟨ 1, 0 ⟩
}

-- `Add` 本身是 structure, 而 structure 可以使用 ⟨ ⟩ 语法调用其 constructor
instance : Add GaussInt :=
  ⟨ fun x y => ⟨x.re + y.re, x.im + y.im⟩ ⟩

instance : Neg GaussInt :=
  ⟨ fun x => ⟨-x.re, -x.im⟩ ⟩

instance : Mul GaussInt :=
  ⟨ fun x y => ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩ ⟩

-- 注册 `simp` 可以使用的等式
@[simp]
theorem zero_re : (0 : GaussInt).re = 0 :=
  rfl

@[simp]
theorem zero_im : (0 : GaussInt).im = 0 :=
  rfl

@[simp]
theorem one_re : (1 : GaussInt).re = 1 :=
  rfl

@[simp]
theorem one_im : (1 : GaussInt).im = 0 :=
  rfl

@[simp]
theorem add_re (x y : GaussInt) : (x + y).re = x.re + y.re :=
  rfl

@[simp]
theorem add_im (x y : GaussInt) : (x + y).im = x.im + y.im :=
  rfl

@[simp]
theorem neg_re (x : GaussInt) : (-x).re = -x.re :=
  rfl

@[simp]
theorem neg_im (x : GaussInt) : (-x).im = -x.im :=
  rfl

@[simp]
theorem mul_re (x y : GaussInt) : (x * y).re = x.re * y.re - x.im * y.im :=
  rfl

@[simp]
theorem mul_im (x y : GaussInt) : (x * y).im = x.re * y.im + x.im * y.re :=
  rfl

-- 对运算律的验证非常简单
instance : CommRing GaussInt where
  zero := 0
  one := 1
  add := (· + ·)
  neg x := -x
  mul := (· * ·)
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc := by
    intros
    ext <;> simp <;> ring
  zero_add := by
    intro
    ext <;> simp
  add_zero := by
    intro
    ext <;> simp
  neg_add_cancel := by
    intro
    ext <;> simp
  add_comm := by
    intros
    ext <;> simp <;> ring
  mul_assoc := by
    intros
    ext <;> simp <;> ring
  one_mul := by
    intro
    ext <;> simp
  mul_one := by
    intro
    ext <;> simp
  left_distrib := by
    intros
    ext <;> simp <;> ring
  right_distrib := by
    intros
    ext <;> simp <;> ring
  mul_comm := by
    intros
    ext <;> simp <;> ring
  zero_mul := by
    intros
    ext <;> simp
  mul_zero := by
    intros
    ext <;> simp

#check Filter
#check Filter.atTop
#check nhds
#check Filter.Tendsto
