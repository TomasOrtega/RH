import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaOddPrimePhaseConjInvariant
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableComb
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GalThetaSign.wPh_conj` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FThetaOddPrimePhaseConjInvariant.lean&line=68#L68)
-/
theorem _root_.GlobalTheory.T.thetaOddPrimePhase_conj_invariant : ∀ (D : D7) (T T' : Tor D) (N N' : ℕ) (x x' : VC D N N') (σ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ) (p k : ℕ) (m : ℤ), p.Prime → p ≠ 2 → (p : ℝ) ^ k * qH D T x = (m : ℝ) → cj ⊤ σ (wdPh D T x) = wdPh D T' x' → wPh D T p x = (-1 : ℂ) ^ m ∧ wPh D T' p x' = (-1 : ℂ) ^ m := by
  first | exact @GlobalTheory.GalThetaSign.wPh_conj | exact GlobalTheory.GalThetaSign.wPh_conj | (intros; apply GlobalTheory.GalThetaSign.wPh_conj <;> assumption)
