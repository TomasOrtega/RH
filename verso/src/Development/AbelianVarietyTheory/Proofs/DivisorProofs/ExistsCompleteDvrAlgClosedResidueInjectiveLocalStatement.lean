import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDvrAlgClosedResidueInjectiveLocal
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompleteClosedDvr.exists_complete_dvr_isAlgClosed` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsCompleteDvrAlgClosedResidueInjectiveLocal.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.exists_complete_dvr_algClosed_residue_injective_local : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V], ¬ IsField V → Nonempty (ℚ →+* V) → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (ρ : V →+* W), IsAdicComplete (maximalIdeal W) W ∧ IsAlgClosed (ResidueField W) ∧ Function.Injective ρ ∧ IsLocalHom ρ := by
  first | exact @GlobalTheory.CompleteClosedDvr.exists_complete_dvr_isAlgClosed | exact GlobalTheory.CompleteClosedDvr.exists_complete_dvr_isAlgClosed | (intros; apply GlobalTheory.CompleteClosedDvr.exists_complete_dvr_isAlgClosed <;> assumption)
