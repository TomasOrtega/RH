import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DerivativeClosedClassBoundedByInverseLeastSize
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingReindex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SobolevIteratedOneParameterSubgroupsWords
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RiemannianHaarGaugeExistsPosUnique
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizeLipschitzProperties
open MeasureTheory NumberField Matrix Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FDerivativeClosedClassBoundedByInverseLeastSize.lean&line=116#L116)
-/
theorem _root_.GlobalTheory.T.derivativeClosedClass_bounded_by_inverseLeastSize : ∀ (B : RowsAut), 1 ≤ B.I.n → 1 ≤ B.g → ∃ m : ℕ, ∀ W : Set (B.I.GA → ℂ), (∀ f ∈ W, (∃ F, GlobalTheory.Dec.IsContRep B F f) ∧ (∀ k ∈ B.I.Kg B.g, ∀ y, f (y * (1, k)) = f y) ∧ ∀ (v : InfinitePlace B.I.F) (E : GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie (B.I.ε v)), ∃ f' ∈ W, ∀ y, HasDerivAt (fun t : ℝ => f (y * GlobalTheory.SobolevBound.onePar B (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.atPlace B v E) t)) (f' y) 0) → ∀ f ∈ W, ∃ C : ℝ, ∀ y, ‖f y‖ ≤ C * (GlobalTheory.Count.tau1 B.I y)⁻¹ ^ m := by
  first | exact @GlobalTheory.SobolevBound.derivative_closed_class_bound | exact GlobalTheory.SobolevBound.derivative_closed_class_bound | (intros; apply GlobalTheory.SobolevBound.derivative_closed_class_bound <;> assumption)
