import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAbelianPartIsoThetaSectionScale
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsFib
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.Ex.AbPartIso
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Ex.AbPartIso.exists_th_scale` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDegenerationProofs%2FExistsAbelianPartIsoThetaSectionScale.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.exists_abelianPartIso_theta_section_scale : AllIso fun {_} _ _ {_} {_} {F} _ _ {N} {N'} ν ν' {_} w f => ∃ lm : F, ∀ x, N'.th (f x) = lm * wVal ν ν' w f x * N.th x := by
  first | exact @GlobalTheory.Ex.AbPartIso.exists_th_scale | exact GlobalTheory.Ex.AbPartIso.exists_th_scale | (intros; apply GlobalTheory.Ex.AbPartIso.exists_th_scale <;> assumption)
