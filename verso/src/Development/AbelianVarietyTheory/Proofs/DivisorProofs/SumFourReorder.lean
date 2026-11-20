import Mathlib

namespace GlobalTheory.FourTermSumReorder

/- English proof (translation)
Chain the equalities or inequalities of the calculation. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem sum_four_reorder {R α β : Type} [AddCommMonoid R] [Fintype α] [Fintype β]
    (f : α → β → α → β → R) :
    ∑ a : α, ∑ b : β, ∑ c : α, ∑ e : β, f a b c e
      = ∑ c : α, ∑ e : β, ∑ b : β, ∑ a : α, f a b c e := by
  calc ∑ a : α, ∑ b : β, ∑ c : α, ∑ e : β, f a b c e
      = ∑ b : β, ∑ a : α, ∑ c : α, ∑ e : β, f a b c e := Finset.sum_comm
    _ = ∑ p : β × α, ∑ q : α × β, f p.2 p.1 q.1 q.2 := by
        simp only [Fintype.sum_prod_type]
    _ = ∑ q : α × β, ∑ p : β × α, f p.2 p.1 q.1 q.2 := Finset.sum_comm
    _ = ∑ c : α, ∑ e : β, ∑ b : β, ∑ a : α, f a b c e := by
        simp only [Fintype.sum_prod_type]

end GlobalTheory.FourTermSumReorder
