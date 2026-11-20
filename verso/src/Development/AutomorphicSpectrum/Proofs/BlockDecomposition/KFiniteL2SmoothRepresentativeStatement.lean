import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KFiniteL2SmoothRepresentative
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FKFiniteL2SmoothRepresentative.lean&line=302#L302)
-/
theorem _root_.GlobalTheory.T.K_finite_L2_smooth_representative : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (H : Submodule ℂ (L2 (latticeGL E a) μ)), H ≤ L2cusp μ → IsIrredSubrep (R (latticeGL E a) μ) H → ∀ F ∈ H, IsKFinL2 μ F → ∃ φ : Sm E a, lift (latticeGL E a) F =ᵐ[μ] φ.1 ∧ MemL2Quotient (latticeGL E a) μ φ.1 ∧ (∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g) ∧ (∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) ∧ IsOpen {k | finRep E a k φ = φ} ∧ FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)) ∧ FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a)) := by
  first | exact @GlobalTheory.CompanionTheory.SmoothRep.smoothRep | exact GlobalTheory.CompanionTheory.SmoothRep.smoothRep | (intros; apply GlobalTheory.CompanionTheory.SmoothRep.smoothRep <;> assumption)
