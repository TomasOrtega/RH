import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Cval
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeInvariantsPeriodPairDictionary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormNatCastLe
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.HalfPeriod

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Move the embeddings inside the algebraic operations. Take a linear combination of the given relations to obtain the conclusion. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem half_comb_not_mem (w₁ w₂ : ℂ) (hind : LinearIndependent ℝ ![w₁, w₂]) (a b : ℤ)
    (hab : ¬ (2 ∣ a ∧ 2 ∣ b)) :
    ((a : ℂ) * w₁ + (b : ℂ) * w₂) / 2 ∉ AddSubgroup.closure ({w₁, w₂} : Set ℂ) := by
  intro h
  rw [AddSubgroup.mem_closure_pair] at h
  obtain ⟨m, n, hmn⟩ := h
  rw [LinearIndependent.pair_iff] at hind
  have key : ((a - 2 * m : ℤ) : ℝ) • w₁ + ((b - 2 * n : ℤ) : ℝ) • w₂ = 0 := by
    rw [zsmul_eq_mul, zsmul_eq_mul] at hmn
    simp only [Complex.real_smul]
    push_cast
    linear_combination (-2 : ℂ) * hmn
  obtain ⟨h1, h2⟩ := hind _ _ key
  have h1' : a - 2 * m = 0 := by exact_mod_cast h1
  have h2' : b - 2 * n = 0 := by exact_mod_cast h2
  exact hab ⟨⟨m, by omega⟩, ⟨n, by omega⟩⟩

/- English proof (translation)
Assume the hypotheses and unpack their components. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Consider separately whether the proposition holds or fails.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion.

Expand and normalize the polynomial expressions, which then agree. Supply the required witnesses or components.
-/
theorem exists_other_half_period : ∀ (Λ : AddSubgroup ℂ), GlobalTheory.EvenTheta.IsLat Λ → ∀ P : ℂ,
    2 * P ∈ Λ → P ∉ Λ → ∃ P' : ℂ, 2 * P' ∈ Λ ∧ P' ∉ Λ ∧ P - P' ∉ Λ := by
  rintro Λ ⟨w₁, w₂, hind, rfl⟩ P _ _
  have hw₁ : w₁ ∈ AddSubgroup.closure ({w₁, w₂} : Set ℂ) :=
    AddSubgroup.subset_closure (by simp)
  have hw₂ : w₂ ∈ AddSubgroup.closure ({w₁, w₂} : Set ℂ) :=
    AddSubgroup.subset_closure (by simp)
  have n₁ : w₁ / 2 ∉ AddSubgroup.closure ({w₁, w₂} : Set ℂ) := by
    have := half_comb_not_mem w₁ w₂ hind 1 0 (by decide)
    simpa using this
  have n₂ : w₂ / 2 ∉ AddSubgroup.closure ({w₁, w₂} : Set ℂ) := by
    have := half_comb_not_mem w₁ w₂ hind 0 1 (by decide)
    simpa using this
  have n₃ : (w₁ - w₂) / 2 ∉ AddSubgroup.closure ({w₁, w₂} : Set ℂ) := by
    have := half_comb_not_mem w₁ w₂ hind 1 (-1) (by decide)
    convert this using 2
    push_cast; ring
  by_cases hP : P - w₁ / 2 ∈ AddSubgroup.closure ({w₁, w₂} : Set ℂ)
  · refine ⟨w₂ / 2, by rw [mul_div_cancel₀ _ two_ne_zero]; exact hw₂, n₂, ?_⟩
    intro h
    apply n₃
    have := AddSubgroup.sub_mem _ h hP
    convert this using 1
    ring
  · exact ⟨w₁ / 2, by rw [mul_div_cancel₀ _ two_ne_zero]; exact hw₁, n₁, hP⟩

end GlobalTheory.HalfPeriod
