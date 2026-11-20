import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryKTypeFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FUnitaryKTypeFinite.lean&line=145#L145)
-/
theorem _root_.GlobalTheory.T.unitary_K_type_finite : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : GL (Fin a) (Cinf E) →* (H →L[ℂ] H)), IsUnitaryRep σ → IsTopIrreducible σ → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Kinf E a) W), FiniteDimensional ℂ ↥(⨆ (T : W →ₗ[ℂ] H) (_ : ∀ k w, T (ρ k w) = σ (Unitary.toUnits k) (T w)), LinearMap.range T : Submodule ℂ H) := by
  first | exact @GlobalTheory.CompanionTheory.AdmGL.admissible_GL_Cinf | exact GlobalTheory.CompanionTheory.AdmGL.admissible_GL_Cinf | (intros; apply GlobalTheory.CompanionTheory.AdmGL.admissible_GL_Cinf <;> assumption)
