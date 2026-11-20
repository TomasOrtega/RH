import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteOfFiniteProjectiveAlgebra
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsAdicCompleteOfFiniteProjectiveAlgebra.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.isAdicComplete_of_finite_projective_algebra : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Algebra O A] [Module.Finite O A] [Module.Projective O A] [IsAdicComplete (Ideal.span {(p : O)}) O], IsAdicComplete (Ideal.span {(p : A)}) A := by
  first | exact @GlobalTheory.FinProjComplete.isAdicComplete_of_finite_projective | exact GlobalTheory.FinProjComplete.isAdicComplete_of_finite_projective | (intros; apply GlobalTheory.FinProjComplete.isAdicComplete_of_finite_projective <;> assumption)
