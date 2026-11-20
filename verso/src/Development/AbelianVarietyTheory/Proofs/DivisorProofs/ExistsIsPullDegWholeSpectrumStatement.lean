import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullDegWholeSpectrum
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PullDegWhole.exists_isPullDeg_top` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsIsPullDegWholeSpectrum.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.exists_isPullDeg_whole_spectrum : ∀ {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {i : R →+* R'} {D : DegPre R} {D' : DegPre R'} (p : IsPullDeg i D D'), Nonempty (PsiOn D ⊤) → ∃ p' : IsPullDeg i D D', p'.W = ⊤ ∧ p'.e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) = p.e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) ∧ ∀ x, p'.xe x = p.xe x := by
  first | exact @GlobalTheory.PullDegWhole.exists_isPullDeg_top | exact GlobalTheory.PullDegWhole.exists_isPullDeg_top | (intros; apply GlobalTheory.PullDegWhole.exists_isPullDeg_top <;> assumption)
