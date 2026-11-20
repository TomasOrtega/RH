import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.BI

open Polynomial in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the hypotheses and the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Clear the denominators using the available nonvanishing facts. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem _root_.GlobalTheory.BI.char_coset_sum_eq_zero :
    ∀ (G : Type) [Group G] [Finite G] (χ : G → ℂ), _root_.GlobalTheory.BI.IsChar ℂ ℂ χ → ∀ H : Subgroup G,
      ∑ᶠ u : H, χ u = 0 → ∀ g : G, ∑ᶠ u : H, χ (g * u) = 0 := by
  intro G _ _ χ hχc H hH g
  obtain ⟨n, ρ, hρ⟩ := hχc
  have := Fintype.ofFinite H
  have hχ : ∀ x, χ x = LinearMap.trace ℂ _ (ρ x) := fun x => by
    simp [hρ, Representation.character]
  rw [finsum_eq_sum_of_fintype] at hH ⊢
  simp only [hχ] at hH ⊢
  rw [← map_sum] at hH
  set S : Module.End ℂ (Fin n → ℂ) := ∑ u : H, ρ u with hS
  have habs : ∀ v : H, ρ v * S = S := by
    intro v
    rw [hS, Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft v) _ _ (fun u => ?_)
    simp [map_mul]
  have hcard : (Fintype.card H : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hSS : S * S = (Fintype.card H : ℂ) • S := by
    conv_lhs => arg 1; rw [hS]
    rw [Finset.sum_mul]
    simp only [habs, Finset.sum_const, Finset.card_univ]
    rw [Nat.cast_smul_eq_nsmul]
  have hidem : IsIdempotentElem ((Fintype.card H : ℂ)⁻¹ • S) := by
    unfold IsIdempotentElem
    rw [smul_mul_smul, hSS, smul_smul]
    congr 1
    field_simp
  have hP : (Fintype.card H : ℂ)⁻¹ • S = 0 :=
    (LinearMap.IsIdempotentElem.trace_eq_zero_iff hidem).1 (by rw [map_smul, hH, smul_zero])
  have hS0 : S = 0 := by simpa [hcard] using hP
  have hsum : ∑ u : H, LinearMap.trace ℂ _ (ρ (g * u)) = LinearMap.trace ℂ _ (ρ g * S) := by
    rw [Finset.mul_sum, map_sum]
    simp [map_mul]
  rw [hsum, hS0, mul_zero, map_zero]

end GlobalTheory.BI
