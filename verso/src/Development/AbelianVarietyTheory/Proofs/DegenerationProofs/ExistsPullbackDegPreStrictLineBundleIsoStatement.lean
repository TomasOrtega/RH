import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsStrict
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.StrictPull.exists_isPullDeg_strict` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDegenerationProofs%2FExistsPullbackDegPreStrictLineBundleIso.lean&line=104#L104)
-/
theorem _root_.GlobalTheory.T.exists_pullback_degPre_strict_lineBundle_iso : Laws → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D : DegPre R) (W : (Spec (CommRingCat.of R)).Opens), Nonempty (PsiOn D W) → (specOf φ).base (genericPoint (Spec (CommRingCat.of R'))) ∈ W → ∃ (D' : DegPre R') (hD : IsPullDeg φ D D'), D'.P.g = D.P.g ∧ Strict hD.w := by
  first | exact @GlobalTheory.StrictPull.exists_isPullDeg_strict | exact GlobalTheory.StrictPull.exists_isPullDeg_strict | (intros; apply GlobalTheory.StrictPull.exists_isPullDeg_strict <;> assumption)
