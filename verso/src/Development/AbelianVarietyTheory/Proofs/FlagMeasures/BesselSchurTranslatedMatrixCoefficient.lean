import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Formalism.FormalDegreeBessel.FinalG
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

/- English proof (translation)
Introduce `k r H _ _ _ σ w a μG d hStd u u₁ v t ht`. Take `⟨_, ⟨⟨h1, hmul⟩, hiso, _⟩, _, _, ⟨_, _, hnull, _⟩, ⟨_, hS⟩, _⟩` from `hStd`. Establish `hH : IsUnit (Hpk k r).det` using `Matrix.isUnit_det_of_right_inverse (hpkFacts k r).2.1`. Establish `hgrp` using `uHGroup _ (Hpk k r) hH`. Establish `htu : IsUnit t.det` using `(hgrp.2.2 t ht).1`.

Establish `hti : t⁻¹ ∈ GG k r` using `(hgrp.2.2 t ht).2`. Establish `htt : t * t⁻¹ = 1` using `Matrix.mul_nonsing_inv t htu`. Set `L : H →ₗᵢ[ℂ] H` to `⟨(σ t : H →ₗ[ℂ] H), fun x => hiso t ht x⟩`. Establish `hinv : σ t (σ t⁻¹ v) = v`. Use `hmul t ht t⁻¹ hti` as an intermediate fact.

Rewrite `this` using `[htt, h1]`. Establish `h'` using `congrArg (fun f : H →L[ℂ] H => f v) this`. Simplify using `using h'.symm`. Establish `hadj : ∀ x : H, ⟪v, σ t x⟫_ℂ = ⟪σ t⁻¹ v, x⟫_ℂ`. Introduce `x`.

Use `L.inner_map_map (σ t⁻¹ v) x` as an intermediate fact. Use `conv_lhs => rw [← hinv]`. Conclude with `this`. Establish `hae : ∀ᵐ y ∂μG, coef σ u v (Matrix.of y) * star (coef σ u₁ v (t * Matrix.of y)) = coef σ u v (Matrix.of y) * star (coef σ u₁ (σ t⁻¹ v) (Matrix.of y))`. Establish `hmem : ∀ᵐ y ∂μG, Matrix.of y ∈ GG k r` using `ae_iff.2 hnull`.

Use `filter_upwards [hmem] with y hy`. Use `congr 2`. Simplify using `only [coef]`. Rewrite using `[hmul t ht _ hy, ContinuousLinearMap.comp_apply, hadj]`. Rewrite using `[integral_congr_ae hae]`.

Conclude with `(hS u v u₁ (σ t⁻¹ v)).2`.
-/
theorem schur_translated_coef : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ), Std σ w a μG d → ∀ u u₁ v : H, ∀ t ∈ GG k r, ∫ y, coef σ u v (Matrix.of y) * star (coef σ u₁ v (t * Matrix.of y)) ∂μG = ⟪u₁, u⟫_ℂ * ⟪v, σ t⁻¹ v⟫_ℂ / (d : ℂ) := by
  intro k r H _ _ _ σ w a μG d hStd u u₁ v t ht
  obtain ⟨_, ⟨⟨h1, hmul⟩, hiso, _⟩, _, _, ⟨_, _, hnull, _⟩, ⟨_, hS⟩, _⟩ := hStd
  have hH : IsUnit (Hpk k r).det := Matrix.isUnit_det_of_right_inverse (hpkFacts k r).2.1
  have hgrp := uHGroup _ (Hpk k r) hH
  have htu : IsUnit t.det := (hgrp.2.2 t ht).1
  have hti : t⁻¹ ∈ GG k r := (hgrp.2.2 t ht).2
  have htt : t * t⁻¹ = 1 := Matrix.mul_nonsing_inv t htu
  let L : H →ₗᵢ[ℂ] H := ⟨(σ t : H →ₗ[ℂ] H), fun x => hiso t ht x⟩
  have hinv : σ t (σ t⁻¹ v) = v := by
    have := hmul t ht t⁻¹ hti
    rw [htt, h1] at this
    have h' := congrArg (fun f : H →L[ℂ] H => f v) this
    simpa using h'.symm
  have hadj : ∀ x : H, ⟪v, σ t x⟫_ℂ = ⟪σ t⁻¹ v, x⟫_ℂ := by
    intro x
    have := L.inner_map_map (σ t⁻¹ v) x
    conv_lhs => rw [← hinv]
    exact this
  have hae : ∀ᵐ y ∂μG, coef σ u v (Matrix.of y) * star (coef σ u₁ v (t * Matrix.of y)) =
      coef σ u v (Matrix.of y) * star (coef σ u₁ (σ t⁻¹ v) (Matrix.of y)) := by
    have hmem : ∀ᵐ y ∂μG, Matrix.of y ∈ GG k r := ae_iff.2 hnull
    filter_upwards [hmem] with y hy
    congr 2
    simp only [coef]
    rw [hmul t ht _ hy, ContinuousLinearMap.comp_apply, hadj]
  rw [integral_congr_ae hae]
  exact (hS u v u₁ (σ t⁻¹ v)).2

end GlobalTheory.SgInf
