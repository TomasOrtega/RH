import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiEvenTauBimultDescendOfInjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsQkPullEquiv
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsScalarFormTraceForm
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDegenerationProofs%2FPsiEvenTauBimultDescendOfInjective.lean&line=118#L118)
-/
theorem _root_.GlobalTheory.T.psiEven_tauBimult_descend_of_injective : GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R'), Function.Injective φ → ∀ (D : DegPre R) (D' : DegPre R') (_ : IsPullDeg φ D D'), (D'.PsiEven → D.PsiEven) ∧ (D'.TauBimult → D.TauBimult) := by
  first | exact @GlobalTheory.psiEven_tauBimult_of_isPullDeg_injective | exact GlobalTheory.psiEven_tauBimult_of_isPullDeg_injective | (intros; apply GlobalTheory.psiEven_tauBimult_of_isPullDeg_injective <;> assumption)
