inductive List' (A : Type) : Type
  | nil : List' A
  | cons : A → List' A → List' A

def singleton (A : Type) (x : A) : List' A :=
  .cons x .nil

def List'.fold (A : Type) (l : List' A) (op : A → A → A) (a : A) :=
  match l with
  | .nil => a
  | .cons x xs => op x (fold A xs op a)
