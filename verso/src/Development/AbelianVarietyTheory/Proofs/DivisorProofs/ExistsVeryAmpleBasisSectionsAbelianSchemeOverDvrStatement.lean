import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVeryAmpleBasisSectionsAbelianSchemeOverDvr
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsVeryAmpleBasisSectionsAbelianSchemeOverDvr.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.exists_veryAmple_basis_sections_abelianScheme_over_dvr : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ (M : LB G.left) (m : ℕ) (t₀ : Fin (m + 1) → M.Sec), M.IsLB → GlobalTheory.AbLaw.VeryAmpleBy G.hom M t₀ → ∃ (N : ℕ) (t : Fin (N + 1) → M.Sec), GlobalTheory.AbLaw.VeryAmpleBy G.hom M t ∧ ∀ u : M.Sec, ∃! c : Fin (N + 1) → W, u = ∑ j, GlobalTheory.AbLaw.cst G.hom ⊤ (c j) • t j := by
  first | exact @GlobalTheory.exists_veryAmpleBy_basis_of_dvr | exact GlobalTheory.exists_veryAmpleBy_basis_of_dvr | (intros; apply GlobalTheory.exists_veryAmpleBy_basis_of_dvr <;> assumption)
