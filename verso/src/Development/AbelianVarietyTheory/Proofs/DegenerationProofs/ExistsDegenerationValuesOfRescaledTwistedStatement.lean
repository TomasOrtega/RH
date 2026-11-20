import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDegenerationValuesOfRescaledTwisted
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsStrict
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RescaleValues.exists_numOf_rescale` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDegenerationProofs%2FExistsDegenerationValuesOfRescaledTwisted.lean&line=32#L32)
-/
theorem _root_.GlobalTheory.T.exists_degenerationValues_of_rescaled_twisted : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : NumD F) (ν : NumOf D F N) (k : ℕ) (β : N.Form k) (u : Fˣ) (q : D.X → (FractionRing R)ˣ), (∀ y, algebraMap (FractionRing R) F (q (ν.eX y)) = ((u ^ (β.be y y / 2) : Fˣ) : F)) → ∃ ν' : NumOf (TauTwist.rescale D q) F (N.twist β u), (∀ y : N.X, ν'.eX y = ν.eX y) ∧ ∀ x : N.A, ν'.eA x = ν.eA x := by
  first | exact @GlobalTheory.RescaleValues.exists_numOf_rescale | exact GlobalTheory.RescaleValues.exists_numOf_rescale | (intros; apply GlobalTheory.RescaleValues.exists_numOf_rescale <;> assumption)
