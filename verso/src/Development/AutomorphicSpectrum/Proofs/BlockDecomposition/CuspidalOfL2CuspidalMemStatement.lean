import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalOfL2CuspidalMem
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.CuspL2.isCuspidal_of_toL2_mem` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCuspidalOfL2CuspidalMem.lean&line=107#L107)
-/
theorem _root_.GlobalTheory.T.cuspidal_of_L2_cuspidal_mem : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (φ : GA E a → ℂ), Continuous φ → (∀ γ g, φ (ratGL E a γ * g) = φ g) → (∀ t g, φ (splitCentre E a t * g) = φ g) → ∀ h : MemL2Quotient (latticeGL E a) μ φ, h.toL2 ∈ L2cusp μ → IsCuspidal φ := by
  first | exact @GlobalTheory.CompanionTheory.CuspL2.isCuspidal_of_toL2_mem | exact GlobalTheory.CompanionTheory.CuspL2.isCuspidal_of_toL2_mem | (intros; apply GlobalTheory.CompanionTheory.CuspL2.isCuspidal_of_toL2_mem <;> assumption)
