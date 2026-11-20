import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateWeilLocal
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenWeil
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FHodgeTateWeilLocal.lean&line=172#L172)
-/
theorem _root_.GlobalTheory.T.hodge_tate_weil_local : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → Flat.NormalCpt ξ → ∀ (G : Over X) [GrpObj G], IsSemiAbelian G → ∀ (L : LB G.left) (n : ℕ), 1 ≤ n → FullTorsion G ξ n → ∀ e, GenWeil G L ξ n e → ∀ (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (q : Cpt ξ), (∃ U : X.Opens, q.1 ∈ U ∧ ∃ w : (Over.mk ξ ⟶ G) → Module.Dual Ω E, ∀ y, y ^ n = 1 → ∀ q' : Cpt ξ, q'.1 ∈ U → M.IsHTAt L n y q' (w y)) ∧ ∀ (y : Over.mk ξ ⟶ G) (w w' : Module.Dual Ω E), y ^ n = 1 → M.IsHTAt L n y q w → (M.IsHTAt L n y q w' ↔ ∃ u ∈ M.omLat q, w' = w + n • u) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.htLat_exists_lifts | exact GlobalTheory.CompanionTheory.Ar.htLat_exists_lifts | (intros; apply GlobalTheory.CompanionTheory.Ar.htLat_exists_lifts <;> assumption)
