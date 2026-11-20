import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalConvolutionCompact
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
import GroundTheory.AutomorphicForms.CuspidalDiscreteness
open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCuspidalConvolutionCompact.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.cuspidal_convolution_compact : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (f : GA E a → ℂ), Continuous f → HasCompactSupport f → IsCompactOperator (repOp (Rcusp μ) μ f) := by
  first | exact @GlobalTheory.CompanionTheory.CuspidalCompact.isCompactOperator_repOp_Rcusp | exact GlobalTheory.CompanionTheory.CuspidalCompact.isCompactOperator_repOp_Rcusp | (intros; apply GlobalTheory.CompanionTheory.CuspidalCompact.isCompactOperator_repOp_Rcusp <;> assumption)
