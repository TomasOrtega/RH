import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiUnitOnUnivOfPullbackGenerating
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QkIsPullFLeftIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPsiUnitOnUnivOfPullbackGenerating.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.psiUnitOn_univ_of_pullback_generating : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D : DegPre R) (D' : DegPre R'), IsPullDeg φ D D' → (∀ χ, PsiUnitOn D χ Set.univ) → ∀ x, PsiUnitOn D' x Set.univ := by
  first | exact @GlobalTheory.PullGenAll.pullgen | exact GlobalTheory.PullGenAll.pullgen | (intros; apply GlobalTheory.PullGenAll.pullgen <;> assumption)
