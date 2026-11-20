import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalL2NormOneIsometry
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
import GroundTheory.AutomorphicForms.CuspidalDiscreteness
open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.CuspTransfer.transfer` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCuspidalL2NormOneIsometry.lean&line=215#L215)
-/
theorem _root_.GlobalTheory.T.cuspidal_L2_norm_one_isometry : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 0 < a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (ν : Measure (GroundTheory.Automorphic.Reduction.normOneGL E a)) [ν.IsHaarMeasure], ∃ (Φ : L2cusp μ →L[ℂ] GroundTheory.Automorphic.CuspidalSpectrum.cuspidalL2 ν) (c : ℝ), 0 < c ∧ (∀ F, ‖Φ F‖ = c * ‖F‖) ∧ ∀ f : GA E a → ℂ, Continuous f → HasCompactSupport f → ∃ f₁ : CompactlySupportedContinuousMap (GroundTheory.Automorphic.Reduction.normOneGL E a) ℂ, Φ ∘L repOp (Rcusp μ) μ f = (GroundTheory.Automorphic.CuspidalSpectrum.cuspRep ν).integrated ν (GroundTheory.Automorphic.UnitaryRep.ccToL1 ν f₁) ∘L Φ := by
  first | exact @GlobalTheory.CompanionTheory.CuspTransfer.transfer | exact GlobalTheory.CompanionTheory.CuspTransfer.transfer | (intros; apply GlobalTheory.CompanionTheory.CuspTransfer.transfer <;> assumption)
