import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Spread

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ValInj

/- English proof (translation)
Introduce `A _ g L u hA U b hb`. Use `haveI : Smooth A.hom := hA.smooth`. Use `haveI : IsReduced A.left := isReduced_of_smooth A.hom`. Use `GlobalTheory.ComplexPoints.eq_of_valAt'_eq A.hom U b 0 fun x hx hxU => ?_` and prove the remaining obligations. Take `⟨z, hz⟩` from `u.ex_onto (Over.homMk x hx)`.

Establish `hzx : (u.ex z).left = x` using `by rw [hz]; rfl`. Establish `h1 : val u.ex U b z = 0` using `hb z (by show ⊤ ≤ (u.ex z).left ⁻¹ᵁ U; rw [hzx]; exact hxU)`. Rewrite `h1` using `[show val u.ex U b z = valAt' (u.ex z).left U b from rfl, hzx]`. Rewrite using `[h1]`. Unfold `valAt' valAt`.

Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem eq_zero_of_val_eq_zero : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A →
    ∀ (U : A.left.Opens) (b : Γ(A.left, U)), (∀ z ∈ pre u.ex U, val u.ex U b z = 0) → b = 0 := by
  intro A _ g L u hA U b hb
  haveI : Smooth A.hom := hA.smooth
  haveI : IsReduced A.left := isReduced_of_smooth A.hom
  refine GlobalTheory.ComplexPoints.eq_of_valAt'_eq A.hom U b 0 fun x hx hxU => ?_
  obtain ⟨z, hz⟩ := u.ex_onto (Over.homMk x hx)
  have hzx : (u.ex z).left = x := by rw [hz]; rfl
  have h1 : val u.ex U b z = 0 := hb z (by show ⊤ ≤ (u.ex z).left ⁻¹ᵁ U; rw [hzx]; exact hxU)
  rw [show val u.ex U b z = valAt' (u.ex z).left U b from rfl, hzx] at h1
  rw [h1]
  unfold valAt' valAt
  split_ifs <;> simp

end GlobalTheory.ValInj
