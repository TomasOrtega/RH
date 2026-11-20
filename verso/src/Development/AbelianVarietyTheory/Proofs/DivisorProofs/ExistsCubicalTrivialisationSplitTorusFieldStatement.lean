import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubicalTrivialisationSplitTorusField
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mum.TorusCubTriv.exists_cubTriv` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsCubicalTrivialisationSplitTorusField.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.exists_cubicalTrivialisation_splitTorus_field : ∀ (k : Type) [CommRing k], IsField k → ∀ (G₀ : Over (Sp k)) [GrpObj G₀] [IsCommMonObj G₀] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (P₀ : GlobalTheory.UU.CP G₀) (i : splitTorus (Sp k) X ⟶ G₀), IsMonHom i → Nonempty (GlobalTheory.UU.CubTriv P₀.c i) := by
  first | exact @GlobalTheory.Mum.TorusCubTriv.exists_cubTriv | exact GlobalTheory.Mum.TorusCubTriv.exists_cubTriv | (intros; apply GlobalTheory.Mum.TorusCubTriv.exists_cubTriv <;> assumption)
