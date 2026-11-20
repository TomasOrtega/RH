import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

/- English proof (translation)
Introduce `R T ι _ _ f N' h`. Establish `hl : N' ∈ Polynomial.lifts (MvPolynomial.map (σ` using `ι) f) := by`. Rewrite using `[Polynomial.lifts_iff_coeff_lifts]`. Introduce `a`. Rewrite using `[MvPolynomial.mem_range_map_iff_coeffs_subset]`.

Introduce `c hc`. Take `⟨m, -, rfl⟩` from `MvPolynomial.mem_coeffs_iff.mp hc`. Conclude with `h a m`. Rewrite `hl` using `[Polynomial.lifts_iff_set_range]`. Take `⟨N, hN⟩` from `hl`.

Conclude with `⟨N, hN⟩`.
-/
theorem UpperTheory.Gal.crystallineComparison.liftingProperty :
    LiftP := by
  intro R T ι _ _ f N' h
  have hl : N' ∈ Polynomial.lifts (MvPolynomial.map (σ := ι) f) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro a
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro c hc
    obtain ⟨m, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hc
    exact h a m
  rw [Polynomial.lifts_iff_set_range] at hl
  obtain ⟨N, hN⟩ := hl
  exact ⟨N, hN⟩
