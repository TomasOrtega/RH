import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteNormalisationProjectiveQuasiFinite
import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsFiniteNormalisationProjectiveQuasiFinite.lean&line=86#L86)
-/
theorem _root_.GlobalTheory.T.exists_finite_normalisation_projective_quasiFinite : ∀ (o : Type) [CommRing o] [IsNoetherianRing o] [Algebra.FiniteType ℤ o] (N : ℕ) (X : Scheme.{0}) (s : X ⟶ Sp o) (f : X ⟶ PSpace o N), IsIntegral X → Geo.Tor.IsNormalScheme X → LocallyOfFiniteType s → QuasiCompact s → IsSeparated s → f ≫ PSpace.str o N = s → QFin f → ∃ (Z : Scheme.{0}) (p : Z ⟶ PSpace o N) (i : X ⟶ Z), IsFinite p ∧ IsOpenImmersion i ∧ i ≫ p = f ∧ Geo.Tor.IsNormalScheme Z ∧ IsIntegral Z ∧ Dense (Set.range i) := by
  first | exact @GlobalTheory.SiegMin.exists_finite_openImmersion_of_qFin | exact GlobalTheory.SiegMin.exists_finite_openImmersion_of_qFin | (intros; apply GlobalTheory.SiegMin.exists_finite_openImmersion_of_qFin <;> assumption)
