import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceModelStandardLatticeValuesAreTheta
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TiedAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TensorOneApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FPlaceModelStandardLatticeValuesAreTheta.lean&line=249#L249)
-/
theorem _root_.GlobalTheory.T.placeModel_standardLattice_values_are_theta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (E₂ : AE D), IsIdemSum E₂ Q → ∀ (f₀ : WO S T → ℂ) (T' : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsThetaFunO ψ S T f₀ → IsLatVac (heisO ψ S T) (stdHom S T) f₀ → IsPlaceModel ψ (symplO S T) (heisO ψ S T) E₂ (stdHom S T) 1 f₀ T' → ∀ Φ, IsSBHalf E₂ (stdHom S T) Φ → IsThetaFunO ψ S T (T' Φ) := by
  first | exact @GlobalTheory.LocMod.StdTheta.theta_placeModel_std | exact GlobalTheory.LocMod.StdTheta.theta_placeModel_std | (intros; apply GlobalTheory.LocMod.StdTheta.theta_placeModel_std <;> assumption)
