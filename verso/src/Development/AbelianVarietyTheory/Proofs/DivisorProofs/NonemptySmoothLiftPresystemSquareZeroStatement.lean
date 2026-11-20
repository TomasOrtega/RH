import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptySmoothLiftPresystemSquareZero
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Obs.pre_nonempty` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FNonemptySmoothLiftPresystemSquareZero.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.nonempty_smoothLiftPresystem_squareZero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀), (∀ T, Algebra.Smooth R₀ (F.obj T)) → Nonempty (Pre I π F) := by
  first | exact @GlobalTheory.Obs.pre_nonempty | exact GlobalTheory.Obs.pre_nonempty | (intros; apply GlobalTheory.Obs.pre_nonempty <;> assumption)
