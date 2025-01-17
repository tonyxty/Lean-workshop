inductive BinaryTree where
  | empty : BinaryTree
  | node : Nat → BinaryTree → BinaryTree → BinaryTree

open BinaryTree
def BinaryTree.size (bt : BinaryTree) : Nat :=
  match bt with
  | empty => 0
  | node _ l r => 1 + l.size + r.size

def leaf (n : Nat) : BinaryTree := node n empty empty

theorem leaf_size : ∀ n : Nat, size (leaf n) = 1 := by
  intro n
  unfold leaf
  rfl

def T₁ : BinaryTree := node 3 empty (leaf 4)
#eval T₁.size

def T : BinaryTree := node 2 (leaf 1) T₁

theorem T_size : T.size = 4 := by rfl

def BinaryTree.sum (bt : BinaryTree) : Nat :=
  match bt with
  | empty => 0
  | node n l r => n + l.sum + r.sum

/-- 是否二叉树中所有元素都满足谓词 P -/
def BinaryTree.all (bt : BinaryTree) (P : Nat → Prop) : Prop :=
  match bt with
  | empty => True
  | node n l r => P n ∧ l.all P ∧ r.all P

def BinaryTree.ordered (bt : BinaryTree) : Prop :=
  match bt with
  | empty => True
  | node n l r =>
      l.all (· ≤ n) ∧
      r.all (· ≥ n) ∧
      l.ordered ∧ r.ordered

theorem T_ordered : T.ordered := by
  -- dsimp [T, T₁, BinaryTree.ordered, BinaryTree.all]
  trivial
