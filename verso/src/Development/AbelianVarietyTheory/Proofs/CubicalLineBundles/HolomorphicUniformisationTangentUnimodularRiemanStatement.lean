import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HolomorphicUniformizationTangentUnimodularRiemann
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane
/- English proof (citation)
Apply `GlobalTheory.AnyUnif.tangent_and_unimodular` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FCubicalLineBundles%2FHolomorphicUniformizationTangentUnimodularRiemann.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.holomorphicUniformisation_tangent_unimodular_riemannForm : ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g), (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) ∧ ∀ (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ), u.IsAH Hm χ → ∃ Ef : LinearMap.BilinForm ℤ u.Λ, (∀ a b : u.Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) ∧ Function.Bijective Ef := by
  first | exact @GlobalTheory.AnyUnif.tangent_and_unimodular | exact GlobalTheory.AnyUnif.tangent_and_unimodular | (intros; apply GlobalTheory.AnyUnif.tangent_and_unimodular <;> assumption)
