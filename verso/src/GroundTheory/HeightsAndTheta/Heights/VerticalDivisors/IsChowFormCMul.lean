import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.IntToFracInjective
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LogGaussNormSupportFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

/- English proof (translation)
Use `⟨mul_ne_zero (C_ne_zero.mpr hc) hf.1, fun g => ?_⟩` and prove the remaining obligations. Establish `hu : IsUnit (C c : MvPolynomial (Fin k × Fin n) F)` using `hc.isUnit.map C`. Rewrite using `[hf.2 g, IsUnit.mul_left_dvd hu]`.
-/
theorem isChowForm_C_mul {F : Type*} [Field F] {n k : ℕ} {I : Ideal (MvPolynomial (Fin n) F)}
    {f : MvPolynomial (Fin k × Fin n) F} (hf : IsChowForm I k f) {c : F} (hc : c ≠ 0) :
    IsChowForm I k (C c * f) := by
  refine ⟨mul_ne_zero (C_ne_zero.mpr hc) hf.1, fun g => ?_⟩
  have hu : IsUnit (C c : MvPolynomial (Fin k × Fin n) F) := hc.isUnit.map C
  rw [hf.2 g, IsUnit.mul_left_dvd hu]

/- English proof (translation)
Simplify using `[specFirst]`.
-/
theorem specFirst_C_mul {R : Type*} [CommSemiring R] {n k : ℕ} (c : R)
    (f : MvPolynomial (Fin (k + 1) × Fin n) R) (u : Fin n → R) :
    specFirst (C c * f) u = C c * specFirst f u := by
  simp [specFirst]

/- English proof (translation)
Introduce `K _ _ n e I f u hI hf hu v`. Take `⟨c, g, hc, hg, hprim⟩` from `h2 K v _ f hf.1`. Establish `hcf : IsChowForm I (e + 1) (g.map (algebraMap (𝓞 K) K))`. Rewrite using `[hg]`. Conclude with `isChowForm_C_mul hf hc`.

Take `⟨h1a, h1b⟩` from `h1 K n e I g u v hI hcf hu hprim`. Rewrite `h1a` using `[hg, specFirst_C_mul, gaussNorm_C_mul]`. Rewrite `h1b` using `[hg, gaussNorm_C_mul]`. Rewrite using `[h3]`. Use `set a := NumberField.HeightOneSpectrum.adicAbv K v c`.

Use `set N : ℝ := (Ideal.absNorm v.asIdeal : ℝ)`. Use `set D := vertDeg e I u v`. Establish `hN : 0 < N`. Establish `h` using `Ideal.absNorm_ne_zero_of_nonZeroDivisors (⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ : nonZeroDivisors (Ideal (𝓞 K)))`. Establish `h' : 0 < Ideal.absNorm v.asIdeal` using `Nat.pos_of_ne_zero h`.

Conclude with `Nat.cast_pos.mpr h'`. Establish `ha : a ≠ 0`. Introduce `h0`. Rewrite `h1b` using `[h0, zero_mul]`. Conclude with `zero_ne_one h1b`.

Establish `hfu : 0 < gaussNorm v (specFirst f fun j => (u j : K))`. Use `lt_of_le_of_ne (gaussNorm_nonneg v _) fun h0 => ?_` and prove the remaining obligations. Rewrite `h1a` using `[← h0, mul_zero, zero_mul]`. Conclude with `zero_ne_one h1a`. Establish `hff : gaussNorm v f = gaussNorm v (specFirst f fun j => (u j : K)) * N ^ D`.

Establish `e1 : a * gaussNorm v f = a * (gaussNorm v (specFirst f fun j => (u j : K)) * N ^ D)`. Rewrite using `[h1b, ← mul_assoc, h1a]`. Conclude with `mul_left_cancel₀ ha e1`. Rewrite using `[hff, Real.log_mul hfu.ne' (pow_ne_zero _ hN.ne'), Real.log_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Main.proof (h1 : GaussEq.Statement) (h2 : PrimitiveScale.Statement)
    (h3 : VertTermEq.Statement) : ChowFormSectionVertical.Statement := by
  intro K _ _ n e I f u hI hf hu v
  obtain ⟨c, g, hc, hg, hprim⟩ := h2 K v _ f hf.1
  have hcf : IsChowForm I (e + 1) (g.map (algebraMap (𝓞 K) K)) := by
    rw [hg]
    exact isChowForm_C_mul hf hc
  obtain ⟨h1a, h1b⟩ := h1 K n e I g u v hI hcf hu hprim
  rw [hg, specFirst_C_mul, gaussNorm_C_mul] at h1a
  rw [hg, gaussNorm_C_mul] at h1b
  rw [h3]
  set a := NumberField.HeightOneSpectrum.adicAbv K v c
  set N : ℝ := (Ideal.absNorm v.asIdeal : ℝ)
  set D := vertDeg e I u v
  have hN : 0 < N := by
    have h := Ideal.absNorm_ne_zero_of_nonZeroDivisors
      (⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ : nonZeroDivisors (Ideal (𝓞 K)))
    have h' : 0 < Ideal.absNorm v.asIdeal := Nat.pos_of_ne_zero h
    exact Nat.cast_pos.mpr h'
  have ha : a ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1b
    exact zero_ne_one h1b
  have hfu : 0 < gaussNorm v (specFirst f fun j => (u j : K)) := by
    refine lt_of_le_of_ne (gaussNorm_nonneg v _) fun h0 => ?_
    rw [← h0, mul_zero, zero_mul] at h1a
    exact zero_ne_one h1a
  have hff : gaussNorm v f = gaussNorm v (specFirst f fun j => (u j : K)) * N ^ D := by
    have e1 : a * gaussNorm v f = a * (gaussNorm v (specFirst f fun j => (u j : K)) * N ^ D) := by
      rw [h1b, ← mul_assoc, h1a]
    exact mul_left_cancel₀ ha e1
  rw [hff, Real.log_mul hfu.ne' (pow_ne_zero _ hN.ne'), Real.log_pow]
  ring

end

end GroundTheory.Heights₂.Heights.Vertical
