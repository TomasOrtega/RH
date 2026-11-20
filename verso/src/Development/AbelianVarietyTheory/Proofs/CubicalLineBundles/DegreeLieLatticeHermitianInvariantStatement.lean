import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.DegreeLieLatticeHermitianInvariant
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FibIndep.deg_lieLat_eq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FCubicalLineBundles%2FDegreeLieLatticeHermitianInvariant.lean&line=105#L105)
-/
theorem _root_.GlobalTheory.T.degree_lie_lattice_hermitian_invariant : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (F' : GenFib P) (h : HermFam K (Fin F.P₀.g → K)) (h' : HermFam K (Fin F'.P₀.g → K)), F.IsHerm h → F'.IsHerm h' → deg h F.lieLat = deg h' F'.lieLat ∧ ∀ (O : Type) [CommRing O] (act : OAct O P.A) (τ : O →+* 𝓞 K), deg h (F.eigLat act τ) = deg h' (F'.eigLat act τ) := by
  first | exact @GlobalTheory.FibIndep.deg_lieLat_eq | exact GlobalTheory.FibIndep.deg_lieLat_eq | (intros; apply GlobalTheory.FibIndep.deg_lieLat_eq <;> assumption)
