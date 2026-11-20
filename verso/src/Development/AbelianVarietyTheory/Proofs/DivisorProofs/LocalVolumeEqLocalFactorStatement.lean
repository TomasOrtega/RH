import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalVolumeEqLocalFactor
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTamagawa
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Filter Topology
open scoped TensorProduct ENNReal
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdLat GlobalTheory.Published
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLocalVolumeEqLocalFactor.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.local_volume_eq_local_factor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)), 2 ≤ r → Unr E → SelfDualLat G Λ → ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), locVol (IsCMField.complexConj E).toAlgHom Gᵀ Λ v = locFactor E r v := by
  first | exact @GlobalTheory.TamSU.locVol_selfDual_eq_locFactor | exact GlobalTheory.TamSU.locVol_selfDual_eq_locFactor | (intros; apply GlobalTheory.TamSU.locVol_selfDual_eq_locFactor <;> assumption)
