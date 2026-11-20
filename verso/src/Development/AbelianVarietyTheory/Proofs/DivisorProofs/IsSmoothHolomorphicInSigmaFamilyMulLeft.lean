import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory.HeckeTwoMul

/- English proof (translation)
Use function extensionality and compare the values at `z`. Establish `h : fderiv ℝ (fun z => c * g z) z = c • fderiv ℝ g z`. Use `congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := g) c) z` as an intermediate fact. Simplify `this` using `[Pi.smul_def, smul_eq_mul]`. Simplify using `only [wirt, h, ContinuousLinearMap.smul_apply, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem wirt_const_mul {Φ : Type} [Fintype Φ] (τ : Φ) (bar : Bool) (c : ℂ) (g : (Φ → ℂ) → ℂ) :
    wirt τ bar (fun z => c * g z) = fun z => c * wirt τ bar g z := by
  funext z
  have h : fderiv ℝ (fun z => c * g z) z = c • fderiv ℝ g z := by
    have := congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := g) c) z
    simpa [Pi.smul_def, smul_eq_mul] using this
  simp only [wirt, h, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Proceed by induction on `ws with`. Consider the case `nil => rfl`. Consider the case `cons w ws ih => rw [wirtWord_cons, wirtWord_cons, ih, wirt_const_mul]`.
-/
theorem wirtWord_const_mul {Φ : Type} [Fintype Φ] (ws : List (Φ × Bool)) (c : ℂ) (g : (Φ → ℂ) → ℂ) :
    wirtWord ws (fun z => c * g z) = fun z => c * wirtWord ws g z := by
  induction ws with
  | nil => rfl
  | cons w ws ih => rw [wirtWord_cons, wirtWord_cons, ih, wirt_const_mul]

/- English proof (translation)
Take `⟨h1, h2⟩` from `hP`. Use `⟨fun σ hσ => contDiffOn_const.mul (h1 σ hσ), fun w z hz => ?_⟩` and prove the remaining obligations. Simplify using `only [wirtWord_const_mul]`. Conclude with `hk.mul (h2 w z hz)`.
-/
theorem isGood_mul (F : Type) [Field F] [NumberField F] (k : ℂ → ℂ)
    (P : ℂ → (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) → ℂ) (hk : DifferentiableOn ℂ k GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.halfPlane)
    (hP : GlobalTheory.HeckeTwo.IsGood P) : GlobalTheory.HeckeTwo.IsGood (fun σ z => k σ * P σ z) := by
  obtain ⟨h1, h2⟩ := hP
  refine ⟨fun σ hσ => contDiffOn_const.mul (h1 σ hσ), fun w z hz => ?_⟩
  simp only [wirtWord_const_mul]
  exact hk.mul (h2 w z hz)

end GlobalTheory.HeckeTwoMul
