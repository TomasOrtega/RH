import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Assume the negation of the conclusion and derive a contradiction.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_notMem_of_ncard_lt_card {H : Type} [Finite H] (S : Set H)
    (h : S.ncard < Nat.card H) : ∃ x : H, x ∉ S := by
  by_contra hx
  have hS : S = Set.univ := by
    ext x
    simp only [Set.mem_univ, iff_true]
    by_contra hx'
    exact hx ⟨x, hx'⟩
  rw [hS, Set.ncard_univ] at h
  exact lt_irrefl _ h

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Supply the required witnesses or components.
-/
theorem exists_pair_avoiding_small_sets :
    ∀ (H : Type) [CommGroup H] [Finite H] (B₀ B₁ : Set H), 6 * Nat.card B₀ < Nat.card H →
      6 * Nat.card B₁ < Nat.card H →
      ∃ b c : H, b ∉ B₀ ∧ c ∉ B₀ ∧ b * c ∉ B₀ ∧ b ∉ B₁ ∧ c ∉ B₁ ∧ b * c ∉ B₁ := by
  intro H _ _ B₀ B₁ h₀ h₁
  rw [Nat.card_coe_set_eq] at h₀ h₁
  have hS : (B₀ ∪ B₁).ncard ≤ B₀.ncard + B₁.ncard := Set.ncard_union_le _ _
  obtain ⟨b, hb⟩ := exists_notMem_of_ncard_lt_card (B₀ ∪ B₁) (by omega)
  have hT : ((fun x => b⁻¹ * x) '' (B₀ ∪ B₁)).ncard ≤ (B₀ ∪ B₁).ncard :=
    Set.ncard_image_le (Set.toFinite _)
  have hU : ((B₀ ∪ B₁) ∪ (fun x => b⁻¹ * x) '' (B₀ ∪ B₁)).ncard ≤
      (B₀ ∪ B₁).ncard + ((fun x => b⁻¹ * x) '' (B₀ ∪ B₁)).ncard := Set.ncard_union_le _ _
  obtain ⟨c, hc⟩ := exists_notMem_of_ncard_lt_card
    ((B₀ ∪ B₁) ∪ (fun x => b⁻¹ * x) '' (B₀ ∪ B₁)) (by omega)
  have hbc : b * c ∉ B₀ ∪ B₁ := fun h => hc (Or.inr ⟨b * c, h, by simp⟩)
  exact ⟨b, c, fun h => hb (Or.inl h), fun h => hc (Or.inl (Or.inl h)), fun h => hbc (Or.inl h),
    fun h => hb (Or.inr h), fun h => hc (Or.inl (Or.inr h)), fun h => hbc (Or.inr h)⟩

end GlobalTheory
