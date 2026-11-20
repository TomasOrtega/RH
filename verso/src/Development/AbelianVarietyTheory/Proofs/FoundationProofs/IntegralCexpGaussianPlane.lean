import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsPosHermFormV
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical

namespace GlobalTheory.UnitaryTheta

/- English proof (translation)
Introduce `l u v hl`. Establish `hl0 : l ≠ 0`. Introduce `h`. Simplify using `[h] at hl`. Establish `hpi : (π : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`.

Establish `hb : (-(π : ℂ) * l).re < 0`. Use `mul_pos Real.pi_pos hl` as an intermediate fact. Simplify using `using this`. Use `set f : ℝ → ℂ := fun x => cexp ((-(π : ℂ) * l) * x ^ 2 + (π * (u + conj v)) * x + 0) with hf`. Use `set g : ℝ → ℂ := fun y => cexp ((-(π : ℂ) * l) * y ^ 2 + (π * I * (conj v - u)) * y + 0) with hg`.

Establish `hfi : Integrable f` using `integrable_cexp_quadratic' hb _ _`. Establish `hgi : Integrable g` using `integrable_cexp_quadratic' hb _ _`. Establish `key : (fun z : ℂ => cexp (-(π : ℂ) * l * (z * conj z) + π * (u * conj z) + π * (z * conj v))) = (fun p : ℝ × ℝ => f p.1 * g p.2) ∘ Complex.measurableEquivRealProd`. Use function extensionality and compare the values at `z`. Simplify using `only [hf, hg, Function.comp, Complex.measurableEquivRealProd_apply, ← Complex.exp_add]`.

Use `congr 1`. Establish `hz : z = z.re + z.im * I` using `(Complex.re_add_im z).symm`. Establish `hc : conj z = z.re - z.im * I`. Apply the tactic sequence `apply Complex.ext <;> simp`. Rewrite using `[hc]`.

Generalize the expression as in `(z.re : ℂ) = a at hz ⊢`. Generalize the expression as in `(z.im : ℂ) = b at hz ⊢`. Substitute `hz` using the available equality. Take the linear combination `(π * l * b ^ 2) * Complex.I_sq`. Establish `hmp` using `Complex.volume_preserving_equiv_real_prod`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[key, hmp.integrable_comp_emb Complex.measurableEquivRealProd.measurableEmbedding]`. Conclude with `hfi.mul_prod hgi`. Rewrite using `[key]`. Establish `h1` using `hmp.integral_comp' (fun p : ℝ × ℝ => f p.1 * g p.2)`.

Simplify using `only [Function.comp_def]`. Rewrite using `[h1, Measure.volume_eq_prod, integral_prod_mul, hf, hg, integral_cexp_quadratic hb, integral_cexp_quadratic hb]`. Establish `h2 : (π : ℂ) / -(-(π : ℂ) * l) = l⁻¹` using `by field_simp`. Establish `h3 : (l⁻¹ : ℂ) ^ (1 / 2 : ℂ) * (l⁻¹ : ℂ) ^ (1 / 2 : ℂ) = l⁻¹`. Rewrite using `[← Complex.cpow_add _ _ (inv_ne_zero hl0)]`.

Evaluate the numerical expressions. Rewrite using `[h2, mul_mul_mul_comm, h3, ← Complex.exp_add]`. Use `congr 2`. Clear the denominators using the available nonvanishing facts. Take the linear combination `(π * (conj v - u) ^ 2) * Complex.I_sq`.
-/
theorem integral_cexp_gaussian_plane : ∀ l u v : ℂ, 0 < l.re → Integrable (fun z : ℂ => cexp (-(π : ℂ) * l * (z * conj z) + π * (u * conj z) + π * (z * conj v))) ∧ ∫ z : ℂ, cexp (-(π : ℂ) * l * (z * conj z) + π * (u * conj z) + π * (z * conj v)) = l⁻¹ * cexp (π * (u * conj v) / l) := by
  intro l u v hl
  have hl0 : l ≠ 0 := by
    intro h
    simp [h] at hl
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hb : (-(π : ℂ) * l).re < 0 := by
    have := mul_pos Real.pi_pos hl
    simpa using this
  set f : ℝ → ℂ := fun x => cexp ((-(π : ℂ) * l) * x ^ 2 + (π * (u + conj v)) * x + 0) with hf
  set g : ℝ → ℂ := fun y => cexp ((-(π : ℂ) * l) * y ^ 2 + (π * I * (conj v - u)) * y + 0) with hg
  have hfi : Integrable f := integrable_cexp_quadratic' hb _ _
  have hgi : Integrable g := integrable_cexp_quadratic' hb _ _
  have key : (fun z : ℂ => cexp (-(π : ℂ) * l * (z * conj z) + π * (u * conj z) + π * (z * conj v)))
      = (fun p : ℝ × ℝ => f p.1 * g p.2) ∘ Complex.measurableEquivRealProd := by
    funext z
    simp only [hf, hg, Function.comp, Complex.measurableEquivRealProd_apply, ← Complex.exp_add]
    congr 1
    have hz : z = z.re + z.im * I := (Complex.re_add_im z).symm
    have hc : conj z = z.re - z.im * I := by
      apply Complex.ext <;> simp
    rw [hc]
    generalize (z.re : ℂ) = a at hz ⊢
    generalize (z.im : ℂ) = b at hz ⊢
    subst hz
    linear_combination (π * l * b ^ 2) * Complex.I_sq
  have hmp := Complex.volume_preserving_equiv_real_prod
  refine ⟨?_, ?_⟩
  · rw [key, hmp.integrable_comp_emb Complex.measurableEquivRealProd.measurableEmbedding]
    exact hfi.mul_prod hgi
  · rw [key]
    have h1 := hmp.integral_comp' (fun p : ℝ × ℝ => f p.1 * g p.2)
    simp only [Function.comp_def]
    rw [h1, Measure.volume_eq_prod, integral_prod_mul, hf, hg, integral_cexp_quadratic hb,
      integral_cexp_quadratic hb]
    have h2 : (π : ℂ) / -(-(π : ℂ) * l) = l⁻¹ := by field_simp
    have h3 : (l⁻¹ : ℂ) ^ (1 / 2 : ℂ) * (l⁻¹ : ℂ) ^ (1 / 2 : ℂ) = l⁻¹ := by
      rw [← Complex.cpow_add _ _ (inv_ne_zero hl0)]
      norm_num
    rw [h2, mul_mul_mul_comm, h3, ← Complex.exp_add]
    congr 2
    field_simp
    linear_combination (π * (conj v - u) ^ 2) * Complex.I_sq

end GlobalTheory.UnitaryTheta
