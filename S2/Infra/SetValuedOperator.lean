module

public import ReasLib.Analysis.SetValuedOperator

public section

open scoped Pointwise

universe u v

variable {X : Type u} {Y : Type v}

#check (SetValuedOperator : Type u → Type v → Type (max u v))

#check (SetValuedOperator.graph :
  SetValuedOperator X Y → SetRel X Y)

#check (SetValuedOperator.mem_graph :
  ∀ (A : SetValuedOperator X Y) (x : X) (y : Y),
    (x, y) ∈ A.graph ↔ y ∈ A x)

#check (SetValuedOperator.dom :
  SetValuedOperator X Y → Set X)

#check (SetValuedOperator.mem_dom :
  ∀ (A : SetValuedOperator X Y) (x : X),
    x ∈ A.dom ↔ (A x).Nonempty)

variable [Add Y]

#check (Pi.add_apply :
  ∀ (A B : SetValuedOperator X Y) (x : X),
    (A + B) x = A x + B x)

/- Infrastructure D.5 (Multivalued operators and graph pointwise sums):
membership in the graph of a pointwise sum decomposes into summand values. -/
#check (SetValuedOperator.mem_graph_add :
  ∀ (A B : SetValuedOperator X Y) (x : X) (y : Y),
    (x, y) ∈ (A + B).graph ↔
      ∃ y₁ ∈ A x, ∃ y₂ ∈ B x, y₁ + y₂ = y)
