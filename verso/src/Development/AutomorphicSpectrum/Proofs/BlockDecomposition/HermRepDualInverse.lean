import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedA
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSmoothHermConstLine

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict

/- English proof (translation)
Unfold `CxPts.ev ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR`. Use `split_ifs with h`. Rewrite using `[← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]`. Conclude with `(h hy).elim`.
-/
theorem ev_unit_inv_mul {m : ℕ} {n : Fin (m + 1) → ℕ} {U : (MP ℤ m n).Opens} (v : Γ(MP ℤ m n, U)ˣ)
    (y : CxPts (mpStr ℤ m n) σ₀) (hy : y ∈ ptsIn (mpStr ℤ m n) σ₀ U) :
    CxPts.ev (mpStr ℤ m n) σ₀ U (↑v⁻¹ : Γ(MP ℤ m n, U)) y *
      CxPts.ev (mpStr ℤ m n) σ₀ U (v : Γ(MP ℤ m n, U)) y = 1 := by
  unfold CxPts.ev ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR
  split_ifs with h
  · rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]
  · exact (h hy).elim

/- English proof (translation)
Introduce `m n M A hA`. Take `⟨u, h1, h2, h3⟩` from `hA`. Use `⟨fun i c => (u i c)⁻¹, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `(i : M.B.ι) (j : M.B.ι) c`. Express the relevant statement in the definitionally equal form `Semi.res _ (u j c)⁻¹ = Semi.res _ (M.B.g i j)⁻¹ * Semi.res _ (u i c)⁻¹`.

Rewrite using `[map_inv, map_inv, map_inv, ← mul_inv]`. Conclude with `congrArg (·⁻¹) (h1 i j c)`. Introduce and unpack `(i : M.B.ι) c c'`. Express the relevant statement in the definitionally equal form `Semi.res _ (u i c)⁻¹ = Semi.res _ (u i c')⁻¹ * ∏ k, blockUnit (c k) (c' k) _ ^ (-A.a k)`. Rewrite using `[map_inv, map_inv]`.

Establish `h` using `congrArg (·⁻¹) (h2 i c c')`. Simplify using `only [mul_inv, ← Finset.prod_inv_distrib, ← zpow_neg] at h`. Conclude with `h`. Introduce and unpack `(i : M.B.ι) c y z hz (hyin : y ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c))`. Express the relevant statement in the definitionally equal form `(A.h z)⁻¹ = (∏ k, ‖z ⟨k, c k⟩‖ ^ (-A.a k)) * ‖CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c) (↑(u i c)⁻¹) y‖ * Real.exp (-(M.φ σ₀).φ i y / 2)`.

Establish `e : CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c) (↑(u i c)⁻¹) y = (CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c) (↑(u i c)) y)⁻¹` using `eq_inv_of_mul_eq_one_left (ev_unit_inv_mul (u i c) y hyin)`. Rewrite using `[h3 i c y z hz hyin]`. Simplify using `only [zpow_neg, Finset.prod_inv_distrib, neg_div, Real.exp_neg, mul_inv]`. Use `congr 2`. Rewrite using `[e, norm_inv]`.
-/
theorem isHermRep_dual : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (M : HermLB (mpStr ℤ m n)) (A : Geo.HermLine (Bk n)),
    IsHermRep M A → IsHermRep M.dual A.inv := by
  intro m n M A hA
  obtain ⟨u, h1, h2, h3⟩ := hA
  refine ⟨fun i c => (u i c)⁻¹, ?_, ?_, ?_⟩
  · rintro (i : M.B.ι) (j : M.B.ι) c
    change Semi.res _ (u j c)⁻¹ = Semi.res _ (M.B.g i j)⁻¹ * Semi.res _ (u i c)⁻¹
    rw [map_inv, map_inv, map_inv, ← mul_inv]
    exact congrArg (·⁻¹) (h1 i j c)
  · rintro (i : M.B.ι) c c'
    change Semi.res _ (u i c)⁻¹ = Semi.res _ (u i c')⁻¹ * ∏ k, blockUnit (c k) (c' k) _ ^ (-A.a k)
    rw [map_inv, map_inv]
    have h := congrArg (·⁻¹) (h2 i c c')
    simp only [mul_inv, ← Finset.prod_inv_distrib, ← zpow_neg] at h
    exact h
  · rintro (i : M.B.ι) c y z hz (hyin : y ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c))
    change (A.h z)⁻¹ = (∏ k, ‖z ⟨k, c k⟩‖ ^ (-A.a k)) *
      ‖CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c) (↑(u i c)⁻¹) y‖ * Real.exp (-(M.φ σ₀).φ i y / 2)
    have e : CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c) (↑(u i c)⁻¹) y =
        (CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c) (↑(u i c)) y)⁻¹ :=
      eq_inv_of_mul_eq_one_left (ev_unit_inv_mul (u i c) y hyin)
    rw [h3 i c y z hz hyin]
    simp only [zpow_neg, Finset.prod_inv_distrib, neg_div, Real.exp_neg, mul_inv]
    congr 2
    rw [e, norm_inv]

end GlobalTheory.CompanionTheory.MPDict
