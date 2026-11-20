import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsComplexCmAbelianObject
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FModuliProofs%2FExistsComplexCmAbelianObject.lean&line=33#L33)
-/
theorem _root_.GlobalTheory.T.exists_complex_cm_abelian_object : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q → ∀ l : Level H, ∃ (b : Base l ℂ) (o : Obj D l b (𝟙 (Sp ℂ))), b.ρ = H.rt0 ∧ b.ζ = zeta l.A ∧ SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q)) o.t.G.hom ∧ ∃ x : 𝟙_ (Over (Sp ℂ)) ⟶ o.t.G, x ≠ 1 := by
  first | exact @GlobalTheory.exists_obj_complex | exact GlobalTheory.exists_obj_complex | (intros; apply GlobalTheory.exists_obj_complex <;> assumption)
