import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertUnimodularRiemannForm
import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsAppellHumbertUnimodularRiemannForm.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.exists_appellHumbert_unimodular_riemannForm : ∀ (h : ℕ) (P : Out.PolAV (Sp ℂ)), P.g = h → ∃ (u : HolUnif P.A P.L h) (Hm : Matrix (Fin h) (Fin h) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ), u.IsAH Hm χ ∧ (∀ x y : u.Λ, (Ef x y : ℝ) = (hermForm Hm x y).im) ∧ Function.Bijective Ef ∧ (∀ x, Ef x x = 0) ∧ Module.Free ℤ u.Λ ∧ Module.Finite ℤ u.Λ ∧ Module.finrank ℤ u.Λ = 2 * h ∧ ∀ (n : ℕ) (x y : u.Λ) (e : ℂˣ), 0 < n → (e : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (Ef x y : ℂ) / n) → Out.WeilIs P.A P.L n (u.ex ((n : ℂ)⁻¹ • (x : Fin h → ℂ))) (u.ex ((n : ℂ)⁻¹ • (y : Fin h → ℂ))) (unitOn e) := by
  first | exact @GlobalTheory.PolUnif.exists_unif_riemannForm | exact GlobalTheory.PolUnif.exists_unif_riemannForm | (intros; apply GlobalTheory.PolUnif.exists_unif_riemannForm <;> assumption)
