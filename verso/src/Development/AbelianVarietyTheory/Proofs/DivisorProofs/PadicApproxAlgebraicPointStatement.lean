import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicApproxAlgebraicPoint
import Mathlib
open Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AlgPointsDense.exists_algebraic_approx` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPadicApproxAlgebraicPoint.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.padic_approx_algebraic_point : ∀ (K : Type) [Field K] [NumberField K] (R : Type) [CommRing R] [Algebra K R] [Algebra.FiniteType K R] (p : ℕ) [Fact p.Prime] (ε : R →+* ℂ_[p]) (s : Finset R) (η : ℝ), 0 < η → ∃ (ι : AlgebraicClosure K →+* ℂ_[p]) (φ : R →ₐ[K] AlgebraicClosure K), ∀ h ∈ s, ‖ι (φ h) - ε h‖ < η := by
  first | exact @GlobalTheory.AlgPointsDense.exists_algebraic_approx | exact GlobalTheory.AlgPointsDense.exists_algebraic_approx | (intros; apply GlobalTheory.AlgPointsDense.exists_algebraic_approx <;> assumption)
