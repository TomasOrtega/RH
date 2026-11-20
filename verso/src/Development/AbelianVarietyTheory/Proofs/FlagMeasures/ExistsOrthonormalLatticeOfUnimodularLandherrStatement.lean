import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalLatticeOfUnimodularLandherr
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mass.exists_orthoLattice_of_unimodular` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FExistsOrthonormalLatticeOfUnimodularLandherr.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.exists_orthonormalLattice_of_unimodular_landherr : ∀ (K : Type) [Field K] [NumberField K] [StarRing K], IsCMUnram K → (∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (k : W →ₗ⋆[K] W →ₗ[K] K), k.IsSymm → PD k → (∃ L : Submodule (𝓞 K) W, Submodule.IsLattice K L ∧ IsUnimodular k L) → ∃ I : Submodule (𝓞 K) W, IsOrthoLattice k I (Module.finrank K W)) := by
  first | exact @GlobalTheory.Mass.exists_orthoLattice_of_unimodular | exact GlobalTheory.Mass.exists_orthoLattice_of_unimodular | (intros; apply GlobalTheory.Mass.exists_orthoLattice_of_unimodular <;> assumption)
