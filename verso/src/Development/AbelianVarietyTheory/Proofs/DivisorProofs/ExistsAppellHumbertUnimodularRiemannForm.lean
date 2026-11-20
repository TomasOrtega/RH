import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam

namespace GlobalTheory.PolUnif

/- English proof (translation)
Establish `h` using `hH.im_star_dotProduct_mulVec_self (star x)`. Rewrite `h` using `[star_star]`. Conclude with `h`.
-/
theorem hermForm_self_im {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (x : Fin g → ℂ) :
    (hermForm Hm x x).im = 0 := by
  have h := hH.im_star_dotProduct_mulVec_self (star x)
  rw [star_star] at h
  exact h

/- English proof (translation)
Introduce `h P hg`. Substitute `hg` using the available equality. Take `⟨rig, hrig⟩` from `P.rigid`. Take `⟨u, Hm, χ, Ef, hAH, -, -, -, -, -, hE, hbij, hW⟩` from `GlobalTheory.thetaUnifAV_all P rig hrig`. Use `haveI : DiscreteTopology u.Λ := u.discrete`.

Use `haveI : IsZLattice ℝ u.Λ := ⟨u.full⟩`. Use `⟨u, Hm, χ, Ef, hAH, hE, hbij, fun x => ?_, ZLattice.module_free ℝ u.Λ, ZLattice.module_finite ℝ u.Λ, ?_, hW⟩` and prove the remaining obligations. Establish `h1` using `hE x x`. Rewrite `h1` using `[hermForm_self_im hAH.1]`. Conclude with `h1` after adjusting the coercions.

Rewrite using `[ZLattice.rank ℝ u.Λ, Module.finrank_pi_fintype]`. Simplify using `[mul_comm]`.
-/
theorem exists_unif_riemannForm : ∀ (h : ℕ) (P : Out.PolAV (Sp ℂ)), P.g = h → ∃ (u : HolUnif P.A P.L h) (Hm : Matrix (Fin h) (Fin h) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ), u.IsAH Hm χ ∧ (∀ x y : u.Λ, (Ef x y : ℝ) = (hermForm Hm x y).im) ∧ Function.Bijective Ef ∧ (∀ x, Ef x x = 0) ∧ Module.Free ℤ u.Λ ∧ Module.Finite ℤ u.Λ ∧ Module.finrank ℤ u.Λ = 2 * h ∧ ∀ (n : ℕ) (x y : u.Λ) (e : ℂˣ), 0 < n → (e : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (Ef x y : ℂ) / n) → Out.WeilIs P.A P.L n (u.ex ((n : ℂ)⁻¹ • (x : Fin h → ℂ))) (u.ex ((n : ℂ)⁻¹ • (y : Fin h → ℂ))) (unitOn e) := by
  intro h P hg
  subst hg
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨u, Hm, χ, Ef, hAH, -, -, -, -, -, hE, hbij, hW⟩ := GlobalTheory.thetaUnifAV_all P rig hrig
  haveI : DiscreteTopology u.Λ := u.discrete
  haveI : IsZLattice ℝ u.Λ := ⟨u.full⟩
  refine ⟨u, Hm, χ, Ef, hAH, hE, hbij, fun x => ?_, ZLattice.module_free ℝ u.Λ, ZLattice.module_finite ℝ u.Λ, ?_, hW⟩
  · have h1 := hE x x
    rw [hermForm_self_im hAH.1] at h1
    exact_mod_cast h1
  · rw [ZLattice.rank ℝ u.Λ, Module.finrank_pi_fintype]
    simp [mul_comm]

end GlobalTheory.PolUnif
