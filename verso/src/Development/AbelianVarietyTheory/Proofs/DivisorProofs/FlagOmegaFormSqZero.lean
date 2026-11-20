import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
open GlobalTheory.HermFrame

namespace GlobalTheory.LineForm

/- English proof (translation)
Simplify using `only [ofValues, map_sum, map_smul, Finset.sum_mul_sum, AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_smul, smul_mul_smul_comm]`. Both sides reduce to the same expression.
-/
theorem coe_ofValues_mul {n : ℕ} (u v : ReciprocityTheory.L2DbarEstimates.V n → ℂ) :
    ((ofValues (fun ξ η => u ξ * v η) : Ev n) : Alt n) =
      ExteriorAlgebra.ι ℂ (∑ a, u (GlobalTheory.GoodMetric.coordVec a) • Pi.single (Sum.inl a) (1 : ℂ) : Fin n ⊕ Fin n → ℂ) *
      ExteriorAlgebra.ι ℂ (∑ b, v (GlobalTheory.GoodMetric.coordVec b) • Pi.single (Sum.inr b) (1 : ℂ) : Fin n ⊕ Fin n → ℂ) := by
  simp only [ofValues, map_sum, map_smul, Finset.sum_mul_sum, AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_smul,
    smul_mul_smul_comm]
  rfl

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Subalgebra.coe_mul, coe_ofValues_mul]`. Generalize the expression as in `(∑ a, u (GlobalTheory.GoodMetric.coordVec a) • Pi.single (Sum.inl a) (1 : ℂ) : Fin n ⊕ Fin n → ℂ) = x`. Generalize the expression as in `(∑ b, v (GlobalTheory.GoodMetric.coordVec b) • Pi.single (Sum.inr b) (1 : ℂ) : Fin n ⊕ Fin n → ℂ) = y`. Establish `h` using `Subalgebra.mem_center_iff.1 (ι_mul_ι_mem_center x y) (ExteriorAlgebra.ι ℂ y)`.

Rewrite using `[mul_assoc, h, mul_assoc (ExteriorAlgebra.ι ℂ x), ExteriorAlgebra.ι_sq_zero]`. Simplify using the standard rewrite rules.
-/
theorem ofValues_mul_sq {n : ℕ} (u v : ReciprocityTheory.L2DbarEstimates.V n → ℂ) :
    (ofValues (fun ξ η => u ξ * v η) : Ev n) * ofValues (fun ξ η => u ξ * v η) = 0 := by
  apply Subtype.ext
  rw [Subalgebra.coe_mul, coe_ofValues_mul]
  generalize (∑ a, u (GlobalTheory.GoodMetric.coordVec a) • Pi.single (Sum.inl a) (1 : ℂ) : Fin n ⊕ Fin n → ℂ) = x
  generalize (∑ b, v (GlobalTheory.GoodMetric.coordVec b) • Pi.single (Sum.inr b) (1 : ℂ) : Fin n ⊕ Fin n → ℂ) = y
  have h := Subalgebra.mem_center_iff.1 (ι_mul_ι_mem_center x y) (ExteriorAlgebra.ι ℂ y)
  rw [mul_assoc, h, mul_assoc (ExteriorAlgebra.ι ℂ x), ExteriorAlgebra.ι_sq_zero]
  simp

/- English proof (translation)
Establish `e : extTrace G z = fun ξ η => (kappa * extFormAdj G z ξ 0 0) * extForm G z η 0 0`. Use function extensionality and compare the values at `ξ η`. Simplify using `[extTrace, Matrix.trace, Matrix.mul_apply, mul_assoc]`. Rewrite using `[e]`. Conclude with `ofValues_mul_sq _ _`.
-/
theorem ofValues_extTrace_sq {n : ℕ} (G : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ)
    (z : ReciprocityTheory.L2DbarEstimates.V n) : (ofValues (extTrace G z) : Ev n) * ofValues (extTrace G z) = 0 := by
  have e : extTrace G z = fun ξ η => (kappa * extFormAdj G z ξ 0 0) * extForm G z η 0 0 := by
    funext ξ η
    simp [extTrace, Matrix.trace, Matrix.mul_apply, mul_assoc]
  rw [e]
  exact ofValues_mul_sq _ _

/- English proof (translation)
Introduce `k _ X _ p D hX σ E h _ fl`. Use function extensionality and compare the values at `x`. Conclude with `ofValues_extTrace_sq _ _`.
-/
theorem omF_mul_self : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (σ : k →+* ℂ),
    ∀ (E : X.Modules) (h : VMetric p E 2) (H : h.IsCInf) (fl : Vert.Flag E 2), omF hX σ h fl * omF hX σ h fl = 0 := by
  intro k _ X _ p D hX σ E h _ fl
  funext x
  exact ofValues_extTrace_sq _ _

end GlobalTheory.LineForm
