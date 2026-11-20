import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.FiniteOfTorsion

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

noncomputable section

namespace LevelTowerAlt

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem isotropic_submodule_nonzero_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (I : Submodule (𝓞 E) Λ), IsCMFam σ → IsIsoSub R.form I → I ≠ ⊥ → (∃ r v, IsNzFamily I r v) ∧ ∀ r v, IsNzFamily I r v → R.nz σ I = R.nzOf σ I v ∧ 0 < R.nz σ I ∧ r = Module.finrank (𝓞 E) I := by
  intro E _ _ _ g Λ _ _ Ψ _ R σ I hσ hI hne
  have := R.free
  have := R.fin
  refine ⟨exists_family hne, fun r v hv => ⟨nz_eq R hσ hv, ?_, family_rank hv⟩⟩
  rw [nz_eq R hσ hv]
  exact nzOf_pos R σ hI hv

end LevelTowerAlt
