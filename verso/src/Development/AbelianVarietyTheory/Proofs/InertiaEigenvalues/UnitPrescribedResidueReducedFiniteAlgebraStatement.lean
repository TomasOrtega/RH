import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitPrescribedResidueReducedFiniteAlgebra
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FUnitPrescribedResidueReducedFiniteAlgebra.lean&line=37#L37)
-/
theorem _root_.GlobalTheory.T.unit_prescribed_residue_reduced_finite_algebra : ∀ (K : UQ) (B : InvAlg K), IsReduced B.A → ∀ (m : MaximalSpectrum B.A) (z : B.A ⧸ m.asIdeal), z ≠ 0 → ∃ y : B.Aˣ, Ideal.Quotient.mk m.asIdeal (y : B.A) = z ∧ ∀ m' : MaximalSpectrum B.A, m' ≠ m → Ideal.Quotient.mk m'.asIdeal (y : B.A) = 1 := by
  first | exact @GlobalTheory.UnitLemma.unit_prescribed_residue | exact GlobalTheory.UnitLemma.unit_prescribed_residue | (intros; apply GlobalTheory.UnitLemma.unit_prescribed_residue <;> assumption)
