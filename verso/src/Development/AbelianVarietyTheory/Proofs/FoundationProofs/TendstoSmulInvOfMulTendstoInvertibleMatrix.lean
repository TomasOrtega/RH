import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.OddFrame

/- English proof (translation)
Establish `hdet : Tendsto (fun τ => (A τ * U τ).det) atImInfty (𝓝 L.det)` using `((continuous_id.matrix_det).tendsto L).comp hAU`. Establish `hev : ∀ᶠ τ in atImInfty, (A τ * U τ).det ≠ 0` using `hdet.eventually_ne hL`. Establish `hinvdet : Tendsto (fun τ => Ring.inverse (A τ * U τ).det) atImInfty (𝓝 (Ring.inverse L.det))`. Simplify using `only [Ring.inverse_eq_inv']`. Conclude with `hdet.inv₀ hL`.

Establish `hadj : Tendsto (fun τ => (A τ * U τ).adjugate) atImInfty (𝓝 L.adjugate)` using `((continuous_id.matrix_adjugate).tendsto L).comp hAU`. Establish `hinv : Tendsto (fun τ => (A τ * U τ)⁻¹) atImInfty (𝓝 L⁻¹)`. Simplify using `only [Matrix.inv_def]`. Conclude with `hinvdet.smul hadj`. Establish `hlim : Tendsto (fun τ => (d τ • U τ) * (A τ * U τ)⁻¹) atImInfty (𝓝 0)`.

Use `hdU.mul hinv` as an intermediate fact. Simplify using `using this`. Use `hlim.congr' ?_` and prove the remaining obligations. Use `filter_upwards [hev] with τ hτ`. Establish `hu : IsUnit (A τ * U τ).det` using `isUnit_iff_ne_zero.mpr hτ`.

Establish `h1 : A τ * (U τ * (A τ * U τ)⁻¹) = 1`. Rewrite using `[← mul_assoc]`. Conclude with `Matrix.mul_nonsing_inv _ hu`. Rewrite using `[Matrix.inv_eq_right_inv h1, Matrix.smul_mul]`.
-/
theorem tendsto_smul_inv_of_mul_tendsto_invertible (r : ℕ) (A U : ℍ → Matrix (Fin r) (Fin r) ℂ)
    (L : Matrix (Fin r) (Fin r) ℂ) (d : ℍ → ℂ) (hL : L.det ≠ 0)
    (hAU : Tendsto (fun τ => A τ * U τ) atImInfty (𝓝 L))
    (hdU : Tendsto (fun τ => d τ • U τ) atImInfty (𝓝 0)) :
    Tendsto (fun τ => d τ • (A τ)⁻¹) atImInfty (𝓝 0) := by
  have hdet : Tendsto (fun τ => (A τ * U τ).det) atImInfty (𝓝 L.det) :=
    ((continuous_id.matrix_det).tendsto L).comp hAU
  have hev : ∀ᶠ τ in atImInfty, (A τ * U τ).det ≠ 0 := hdet.eventually_ne hL

  have hinvdet : Tendsto (fun τ => Ring.inverse (A τ * U τ).det) atImInfty (𝓝 (Ring.inverse L.det)) := by
    simp only [Ring.inverse_eq_inv']
    exact hdet.inv₀ hL
  have hadj : Tendsto (fun τ => (A τ * U τ).adjugate) atImInfty (𝓝 L.adjugate) :=
    ((continuous_id.matrix_adjugate).tendsto L).comp hAU
  have hinv : Tendsto (fun τ => (A τ * U τ)⁻¹) atImInfty (𝓝 L⁻¹) := by
    simp only [Matrix.inv_def]
    exact hinvdet.smul hadj
  have hlim : Tendsto (fun τ => (d τ • U τ) * (A τ * U τ)⁻¹) atImInfty (𝓝 0) := by
    have := hdU.mul hinv
    simpa using this
  refine hlim.congr' ?_
  filter_upwards [hev] with τ hτ
  have hu : IsUnit (A τ * U τ).det := isUnit_iff_ne_zero.mpr hτ
  have h1 : A τ * (U τ * (A τ * U τ)⁻¹) = 1 := by
    rw [← mul_assoc]; exact Matrix.mul_nonsing_inv _ hu
  rw [Matrix.inv_eq_right_inv h1, Matrix.smul_mul]

end GlobalTheory.OddFrame
