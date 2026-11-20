import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGoodTorsionTranslateOfSection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnitThetaConstantsGenerateIntegralTorsionImports
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDegenerationProofs%2FExistsGoodTorsionTranslateOfSection.lean&line=37#L37)
-/
theorem _root_.GlobalTheory.T.exists_good_torsion_translate_of_section : PolBaseChangeSt → GoodPtSt → ∀ (S : Scheme.{0}) (P : PolAV S) (θ : LB.Sec P.L) (κ : Type) [Field κ] [IsAlgClosed κ] (r : Sp κ ⟶ S) (n : ℕ), 2 ≤ n → (n : κ) ≠ 0 → (∃ z ∈ nonzeroLocus θ, P.A.hom z ∈ Set.range r) → ∀ b : Over.mk r ⟶ P.A, ∃ x : Over.mk r ⟶ P.A, x ^ n = 1 ∧ ⊤ ≤ (b * x).left ⁻¹ᵁ nonzeroLocus θ := by
  first | exact @GlobalTheory.UnitTheta.exists_good_point_of_sec | exact GlobalTheory.UnitTheta.exists_good_point_of_sec | (intros; apply GlobalTheory.UnitTheta.exists_good_point_of_sec <;> assumption)
