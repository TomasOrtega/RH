import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBoundAbsLocalLatticeCompletionEntries
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.absFin_latLoc_le` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FExistsBoundAbsLocalLatticeCompletionEntries.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.exists_bound_abs_localLatticeCompletion_entries : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L] (v : HeightOneSpectrum (𝓞 F)), ∃ C : ℝ≥0, ∀ y ∈ latLoc F L v, ∀ i, absFin F v (y i) ≤ C := by
  first | exact @GlobalTheory.absFin_latLoc_le | exact GlobalTheory.absFin_latLoc_le | (intros; apply GlobalTheory.absFin_latLoc_le <;> assumption)
