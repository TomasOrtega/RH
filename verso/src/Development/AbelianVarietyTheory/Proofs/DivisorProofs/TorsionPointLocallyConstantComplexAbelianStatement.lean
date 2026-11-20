import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointLocallyConstantComplexAbelian
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTorsionPointLocallyConstantComplexAbelian.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.torsionPoint_locally_constant_complexAbelian : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (N : ℕ), 1 ≤ N → ∀ (T : Over (Sp ℂ)) (x : T ⟶ A), x ^ N = 1 →
    ∀ t : T.left, ∃ (U : T.left.Opens) (y : 𝟙_ (Over (Sp ℂ)) ⟶ A), t ∈ U ∧ U.ι ≫ x.left = U.ι ≫ T.hom ≫ y.left := by
  first | exact @GlobalTheory.TorsionLocal.locally_eq_const_of_pow_eq_one | exact GlobalTheory.TorsionLocal.locally_eq_const_of_pow_eq_one | (intros; apply GlobalTheory.TorsionLocal.locally_eq_const_of_pow_eq_one <;> assumption)
