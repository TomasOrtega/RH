import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

open Polynomial

noncomputable section

namespace GlobalTheory.JR.Spec

variable {F : Type} [NontriviallyNormedField F] [IsUltrametricDist F]
  {k : Type} [Field k] [Algebra F k]

/- English proof (translation)
Establish `hyF : IsIntegral F y` using `Algebra.IsIntegral.isIntegral y`. Rewrite `h` using `[spectralNorm, spectralValue_le_one_iff (minpoly.monic hyF)]`. Establish `hl : minpoly F y ∈ lifts (algebraMap (NormedField.valuation (K` using `F)).integer F) := by`. Rewrite using `[lifts_iff_coeff_lifts]`. Introduce `n`.

Use `⟨⟨_, ?_⟩, rfl⟩` and prove the remaining obligations. Rewrite using `[Valuation.mem_integer_iff, NormedField.valuation_apply]`. Conclude with `h n` after adjusting the coercions. Take `⟨q, hq, -, hqm⟩` from `lifts_and_natDegree_eq_and_monic hl (minpoly.monic hyF)`. Use `⟨q, hqm, ?_⟩` and prove the remaining obligations.

Rewrite using `[← aeval_def, ← aeval_map_algebraMap F, hq, minpoly.aeval]`.
-/
theorem isIntegral_integer_of_spectralNorm_le_one [FiniteDimensional F k] {y : k}
    (h : spectralNorm F k y ≤ 1) : IsIntegral (NormedField.valuation (K := F)).integer y := by
  have hyF : IsIntegral F y := Algebra.IsIntegral.isIntegral y
  rw [spectralNorm, spectralValue_le_one_iff (minpoly.monic hyF)] at h
  have hl : minpoly F y ∈ lifts (algebraMap (NormedField.valuation (K := F)).integer F) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    refine ⟨⟨_, ?_⟩, rfl⟩
    rw [Valuation.mem_integer_iff, NormedField.valuation_apply]
    exact_mod_cast h n
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic hl (minpoly.monic hyF)
  refine ⟨q, hqm, ?_⟩
  rw [← aeval_def, ← aeval_map_algebraMap F, hq, minpoly.aeval]

/- English proof (translation)
Introduce `F _ _ _ k _ _ _ y hy0`. Establish `hmul : spectralNorm F k y * spectralNorm F k y⁻¹ = 1`. Use `spectralAlgNorm_mul (K := F) (L := k) y y⁻¹` as an intermediate fact. Rewrite `this` using `[spectralAlgNorm_def, spectralAlgNorm_def, spectralAlgNorm_def, mul_inv_cancel₀ hy0, spectralNorm_one]`. Conclude with `this.symm`.

Distinguish the cases in `h : spectralNorm F k y ≤ 1`. Conclude with `Or.inl (isIntegral_integer_of_spectralNorm_le_one h)`. Use `right`. Apply `isIntegral_integer_of_spectralNorm_le_one` to reduce the goal to its premises. Establish `h1 : 1 < spectralNorm F k y` using `lt_of_not_ge h`.

Assume the negation of the conclusion as `h2`. Establish `h2 : 1 < spectralNorm F k y⁻¹` using `lt_of_not_ge h2`. Establish `: 1 < spectralNorm F k y * spectralNorm F k y⁻¹` using `one_lt_mul_of_lt_of_le h1 h2.le`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem isIntegral_or_isIntegral_inv : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F]
    [CompleteSpace F] (k : Type) [Field k] [Algebra F k] [FiniteDimensional F k] (y : k), y ≠ 0 →
    IsIntegral (NormedField.valuation (K := F)).integer y ∨
      IsIntegral (NormedField.valuation (K := F)).integer y⁻¹ := by
  intro F _ _ _ k _ _ _ y hy0
  have hmul : spectralNorm F k y * spectralNorm F k y⁻¹ = 1 := by
    have := spectralAlgNorm_mul (K := F) (L := k) y y⁻¹
    rw [spectralAlgNorm_def, spectralAlgNorm_def, spectralAlgNorm_def, mul_inv_cancel₀ hy0,
      spectralNorm_one] at this
    exact this.symm
  by_cases h : spectralNorm F k y ≤ 1
  · exact Or.inl (isIntegral_integer_of_spectralNorm_le_one h)
  · right
    apply isIntegral_integer_of_spectralNorm_le_one
    have h1 : 1 < spectralNorm F k y := lt_of_not_ge h
    by_contra h2
    have h2 : 1 < spectralNorm F k y⁻¹ := lt_of_not_ge h2
    have : 1 < spectralNorm F k y * spectralNorm F k y⁻¹ := one_lt_mul_of_lt_of_le h1 h2.le
    linarith

end GlobalTheory.JR.Spec
