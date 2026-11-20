import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.LocalLog

/- English proof (translation)
Use `letI : NormedRing (Mx n) := Matrix.linftyOpNormedRing`. Use `letI : NormedAlgebra ℂ (Mx n) := Matrix.linftyOpNormedAlgebra`. Establish `h : HasStrictFDerivAt (NormedSpace.exp : Mx n → Mx n) ((ContinuousLinearEquiv.refl ℂ (Mx n) : Mx n ≃L[ℂ] Mx n) : Mx n →L[ℂ] Mx n) 0` using `hasStrictFDerivAt_exp_zero (𝕂 := ℂ)`. Establish `h0 : NormedSpace.exp (0 : Mx n) = 1` using `NormedSpace.exp_zero`. Use `⟨h.localInverse _ _ _, ?_, ?_, ?_, h.eventually_left_inverse⟩` and prove the remaining obligations.

Use `h.localInverse_continuousAt` as an intermediate fact. Rewrite `this` using `[h0]`. Then use the resulting hypothesis. Use `h.localInverse_apply_image` as an intermediate fact. Rewrite `this` using `[h0]`. Then use the resulting hypothesis. Use `h.eventually_right_inverse` as an intermediate fact.

Rewrite `this` using `[h0]`. Then use the resulting hypothesis.
-/
theorem exists_local_log (n : ℕ) : ∃ L : Mx n → Mx n, ContinuousAt L 1 ∧ L 1 = 0 ∧
    (∀ᶠ g in 𝓝 (1 : Mx n), NormedSpace.exp (L g) = g) ∧
    ∀ᶠ X in 𝓝 (0 : Mx n), L (NormedSpace.exp X) = X := by
  letI : NormedRing (Mx n) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Mx n) := Matrix.linftyOpNormedAlgebra
  have h : HasStrictFDerivAt (NormedSpace.exp : Mx n → Mx n)
      ((ContinuousLinearEquiv.refl ℂ (Mx n) : Mx n ≃L[ℂ] Mx n) : Mx n →L[ℂ] Mx n) 0 :=
    hasStrictFDerivAt_exp_zero (𝕂 := ℂ)
  have h0 : NormedSpace.exp (0 : Mx n) = 1 := NormedSpace.exp_zero
  refine ⟨h.localInverse _ _ _, ?_, ?_, ?_, h.eventually_left_inverse⟩
  · have := h.localInverse_continuousAt
    rwa [h0] at this
  · have := h.localInverse_apply_image
    rwa [h0] at this
  · have := h.eventually_right_inverse
    rwa [h0] at this

/- English proof (translation)
Introduce `n ε`. Take `⟨L, hc, h1, hr, hl⟩` from `exists_local_log n`. Use `⟨L, hc, h1, ?_⟩` and prove the remaining obligations. Establish `hJ` using `Jm_mul_self ε`. Establish `ht : Tendsto (fun g => Jm ε * (-(L g)ᴴ) * Jm ε) (𝓝 1) (𝓝 0)`.

Establish `hcont : Continuous fun X : Mx n => Jm ε * (-Xᴴ) * Jm ε` using `by fun_prop`. Use `(hcont.tendsto 0).comp (h1 ▸ hc.tendsto)` as an intermediate fact. Simplify `this` using `[Function.comp_def]`. Use `filter_upwards [hr, ht.eventually hl] with g hg hg' hU`. Use `⟨?_, hg⟩` and prove the remaining obligations.

Establish `hU' : gᴴ * Jm ε * g = Jm ε` using `hU`. Establish `hinv : (Jm ε)⁻¹ = Jm ε` using `Matrix.inv_eq_left_inv hJ`. Establish `he : NormedSpace.exp (Jm ε * (-(L g)ᴴ) * Jm ε) = g`. Establish `h2` using `Matrix.exp_conj (Jm ε) (-(L g)ᴴ) (isUnit_Jm ε)`. Rewrite `h2` using `[hinv, Matrix.exp_neg, Matrix.exp_conjTranspose, hg]`.

Rewrite using `[h2]`. Establish `h3 : (gᴴ)⁻¹ = Jm ε * g * Jm ε`. Apply `Matrix.inv_eq_right_inv` to reduce the goal to its premises. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, hU', hJ]`. Rewrite using `[h3]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite `hg'` using `[he]`. Use `show (L g)ᴴ * Jm ε + Jm ε * L g = 0`. Use `nth_rewrite 2 [hg']`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, hJ]`.

Simplify using the standard rewrite rules.
-/
theorem local_log_UJ : ∀ (n : ℕ) (ε : Fin n → Bool), ∃ L : Mx n → Mx n, ContinuousAt L 1 ∧ L 1 = 0 ∧
    ∀ᶠ g in 𝓝 (1 : Mx n), g ∈ UJset ε → L g ∈ lieSet ε ∧ NormedSpace.exp (L g) = g := by
  intro n ε
  obtain ⟨L, hc, h1, hr, hl⟩ := exists_local_log n
  refine ⟨L, hc, h1, ?_⟩
  have hJ := Jm_mul_self ε
  have ht : Tendsto (fun g => Jm ε * (-(L g)ᴴ) * Jm ε) (𝓝 1) (𝓝 0) := by
    have hcont : Continuous fun X : Mx n => Jm ε * (-Xᴴ) * Jm ε := by fun_prop
    have := (hcont.tendsto 0).comp (h1 ▸ hc.tendsto)
    simpa [Function.comp_def] using this
  filter_upwards [hr, ht.eventually hl] with g hg hg' hU
  refine ⟨?_, hg⟩
  have hU' : gᴴ * Jm ε * g = Jm ε := hU
  have hinv : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_left_inv hJ
  have he : NormedSpace.exp (Jm ε * (-(L g)ᴴ) * Jm ε) = g := by
    have h2 := Matrix.exp_conj (Jm ε) (-(L g)ᴴ) (isUnit_Jm ε)
    rw [hinv, Matrix.exp_neg, Matrix.exp_conjTranspose, hg] at h2
    rw [h2]
    have h3 : (gᴴ)⁻¹ = Jm ε * g * Jm ε := by
      apply Matrix.inv_eq_right_inv
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU', hJ]
    rw [h3]
    calc Jm ε * (Jm ε * g * Jm ε) * Jm ε = (Jm ε * Jm ε) * g * (Jm ε * Jm ε) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [hJ]; simp
  rw [he] at hg'
  show (L g)ᴴ * Jm ε + Jm ε * L g = 0
  nth_rewrite 2 [hg']
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hJ]
  simp

end GlobalTheory.LocalLog
