import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KFiniteVectorsDense
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FKFiniteVectorsDense.lean&line=298#L298)
-/
theorem _root_.GlobalTheory.T.K_finite_vectors_dense : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (H : Submodule ℂ (L2 (latticeGL E a) μ)), IsSubrep (R (latticeGL E a) μ) H → H ≤ (Submodule.span ℂ {F | F ∈ H ∧ IsKFinL2 μ F}).topologicalClosure := by
  first | exact @GlobalTheory.CompanionTheory.DenseKFin.le_closure_span_K_finite | exact GlobalTheory.CompanionTheory.DenseKFin.le_closure_span_K_finite | (intros; apply GlobalTheory.CompanionTheory.DenseKFin.le_closure_span_K_finite <;> assumption)
