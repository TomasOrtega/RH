import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Introduce `H U _ _ W sL sM cL cM rL rM hr hs hc x y`. Establish `h1` using `hc x y y⁻¹`. Rewrite `h1` using `[mul_inv_cancel, mul_inv_cancel_right]`. Establish `h2 : sM y = W y⁻¹ * sL y * (W y)⁻¹` using `eq_mul_inv_of_mul_eq (hs y)`. Establish `h3 : cM x y y⁻¹ = W x * W x * W y * W y⁻¹ * cL x y y⁻¹ * (W (x * y) * W (x * y⁻¹) * W 1 * W 1)⁻¹`.

Apply `eq_mul_inv_of_mul_eq` to reduce the goal to its premises. Rewrite using `[← h1]`. Simplify using `only [_root_.mul_assoc]`. Rewrite using `[h2, h3, hr]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises.

Simplify using `only [ofMul_mul, ofMul_inv, ofMul_pow]`. Normalize the expressions using the abelian group laws.
-/
theorem addition_factor_through_cubical_even_iso : ∀ (H U : Type) [CommGroup H] [CommGroup U] (W sL sM : H → U) (cL cM : H → H → H → U) (rL rM : U), rM = W 1 * rL → (∀ x, sM x * W x = W x⁻¹ * sL x) → (∀ x y u, cM x y u * W (x * y) * W (x * u) * W (y * u) * W 1 = W (x * y * u) * W x * W y * W u * cL x y u) → ∀ x y, W x ^ 2 * W y ^ 2 * (cL x y y⁻¹ * (sL y)⁻¹ * rL ^ 2) = cM x y y⁻¹ * (sM y)⁻¹ * rM ^ 2 * (W (x * y) * W (x * y⁻¹)) := by
  intro H U _ _ W sL sM cL cM rL rM hr hs hc x y
  have h1 := hc x y y⁻¹
  rw [mul_inv_cancel, mul_inv_cancel_right] at h1
  have h2 : sM y = W y⁻¹ * sL y * (W y)⁻¹ := eq_mul_inv_of_mul_eq (hs y)
  have h3 : cM x y y⁻¹ = W x * W x * W y * W y⁻¹ * cL x y y⁻¹ *
      (W (x * y) * W (x * y⁻¹) * W 1 * W 1)⁻¹ := by
    apply eq_mul_inv_of_mul_eq
    rw [← h1]
    simp only [_root_.mul_assoc]
  rw [h2, h3, hr]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow]
  abel

end GlobalTheory
