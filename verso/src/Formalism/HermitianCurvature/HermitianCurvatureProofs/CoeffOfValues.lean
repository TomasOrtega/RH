import Mathlib

open MeasureTheory Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral

section vand

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

def vN (d : ℕ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ := Matrix.vandermonde fun m : Fin (d + 1) => ((m : ℕ) : ℂ)

/- English proof (translation)
Rewrite using `[isUnit_iff_ne_zero, vN, Matrix.det_vandermonde_ne_zero_iff]`. Introduce `a b h`. Establish `h' : ((a : ℕ) : ℂ) = ((b : ℕ) : ℂ)` using `h`. Conclude with `Fin.ext (by exact_mod_cast h')`.
-/
theorem vN_det (d : ℕ) : IsUnit (vN d).det := by
  rw [isUnit_iff_ne_zero, vN, Matrix.det_vandermonde_ne_zero_iff]
  intro a b h
  have h' : ((a : ℕ) : ℂ) = ((b : ℕ) : ℂ) := h
  exact Fin.ext (by exact_mod_cast h')

/- English proof (translation)
Establish `hinv : (vN d)⁻¹ * vN d = 1` using `Matrix.nonsing_inv_mul _ (vN_det d)`. Repeatedly rewrite using `[Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Establish `e : ∀ n' : Fin (d + 1), ∑ m, ((vN d)⁻¹ n m * (((m : ℕ) : ℝ) : ℂ) ^ (n' : ℕ)) • c n' = ((vN d)⁻¹ * vN d) n n' • c n'`. Introduce `n'`.

Rewrite using `[← Finset.sum_smul, Matrix.mul_apply]`. Use `congr 1`. Repeatedly rewrite using `[e, hinv, Matrix.one_apply, ite_smul, one_smul, zero_smul]`. Simplify using the standard rewrite rules.
-/
theorem coeff_of_values (d : ℕ) (c : Fin (d + 1) → E) (n : Fin (d + 1)) :
    ∑ m, (vN d)⁻¹ n m • ∑ n' : Fin (d + 1), ((((m : ℕ) : ℝ) : ℂ) ^ (n' : ℕ)) • c n' = c n := by
  have hinv : (vN d)⁻¹ * vN d = 1 := Matrix.nonsing_inv_mul _ (vN_det d)
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have e : ∀ n' : Fin (d + 1), ∑ m, ((vN d)⁻¹ n m * (((m : ℕ) : ℝ) : ℂ) ^ (n' : ℕ)) • c n' =
      ((vN d)⁻¹ * vN d) n n' • c n' := by
    intro n'
    rw [← Finset.sum_smul, Matrix.mul_apply]
    congr 1
  simp_rw [e, hinv, Matrix.one_apply, ite_smul, one_smul, zero_smul]
  simp

end vand

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/- English proof (translation)
Use `set W := (vN d)⁻¹ with hW`. Use `set C : Fin (d + 1) → X → E := fun n x => ∑ m, W n m • I ((m : ℕ) : ℝ) x with hC`. Establish `hCint : ∀ n, Integrable (C n) μ` using `fun n => integrable_finsetSum _ fun m _ => (hI _).smul (W n m)`. Establish `hCeq : ∀ n, ∫ x, C n x ∂μ = ∑ m, W n m • ∫ x, I ((m : ℕ) : ℝ) x ∂μ`. Introduce `n`.

Use `show ∫ x, ∑ m, W n m • I ((m : ℕ) : ℝ) x ∂μ = _`. Use `integral_finsetSum (μ := μ) Finset.univ (f := fun m x => W n m • I ((m : ℕ) : ℝ) x) (fun m _ => (hI _).smul (W n m))` as an intermediate fact. Rewrite using `[this]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `m _`.

Rewrite using `[integral_smul]`. Establish `hae : ∀ᵐ x ∂μ, (∀ y : ℝ, I y x = ∑ n : Fin (d + 1), ((y : ℂ) ^ (n : ℕ)) • C n x) ∧ C (Fin.last d) x = T x` using `by filter_upwards [hP] with x ⟨c, hc, hcx⟩`. Establish `hCc : ∀ n, C n x = c n`. Introduce `n`. Rewrite using `[hC]`.

Simplify using `only`. Repeatedly rewrite using `[hcx]`. Use `coeff_of_values d c n` as an intermediate fact. Simplify `this` using `[hW]`. Use `⟨fun y => ?_, by rw [hCc, hc]⟩` and prove the remaining obligations.

Rewrite using `[hcx y]`. Repeatedly rewrite using `[hCc]`. Use `⟨fun n => ∫ x, C n x ∂μ, ?_, fun y => ?_⟩` and prove the remaining obligations. Conclude with `integral_congr_ae (hae.mono fun x hx => hx.2)`. Rewrite using `[integral_congr_ae (hae.mono fun x hx => hx.1 y)]`.

Use `integral_finsetSum (μ := μ) Finset.univ (f := fun (n : Fin (d + 1)) x => ((y : ℂ) ^ (n : ℕ)) • C n x) (fun n _ => (hCint n).smul _)` as an intermediate fact. Rewrite using `[this]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `n _`. Rewrite using `[integral_smul]`.
-/
theorem poly_integral (μ : Measure X) (d : ℕ) (I : ℝ → X → E) (T : X → E) (hI : ∀ y, Integrable (I y) μ)
    (hP : ∀ᵐ x ∂μ, ∃ c : Fin (d + 1) → E, c (Fin.last d) = T x ∧ ∀ y : ℝ, I y x = ∑ n : Fin (d + 1), ((y : ℂ) ^ (n : ℕ)) • c n) :
    ∃ c : Fin (d + 1) → E, c (Fin.last d) = ∫ x, T x ∂μ ∧
      ∀ y : ℝ, ∫ x, I y x ∂μ = ∑ n : Fin (d + 1), ((y : ℂ) ^ (n : ℕ)) • c n := by
  set W := (vN d)⁻¹ with hW

  set C : Fin (d + 1) → X → E := fun n x => ∑ m, W n m • I ((m : ℕ) : ℝ) x with hC
  have hCint : ∀ n, Integrable (C n) μ := fun n =>
    integrable_finsetSum _ fun m _ => (hI _).smul (W n m)
  have hCeq : ∀ n, ∫ x, C n x ∂μ = ∑ m, W n m • ∫ x, I ((m : ℕ) : ℝ) x ∂μ := by
    intro n
    show ∫ x, ∑ m, W n m • I ((m : ℕ) : ℝ) x ∂μ = _
    have := integral_finsetSum (μ := μ) Finset.univ (f := fun m x => W n m • I ((m : ℕ) : ℝ) x)
      (fun m _ => (hI _).smul (W n m))
    rw [this]
    apply Finset.sum_congr rfl
    intro m _
    rw [integral_smul]

  have hae : ∀ᵐ x ∂μ, (∀ y : ℝ, I y x = ∑ n : Fin (d + 1), ((y : ℂ) ^ (n : ℕ)) • C n x) ∧ C (Fin.last d) x = T x := by
    filter_upwards [hP] with x ⟨c, hc, hcx⟩
    have hCc : ∀ n, C n x = c n := by
      intro n
      rw [hC]
      simp only
      simp_rw [hcx]
      have := coeff_of_values d c n
      simpa [hW] using this
    refine ⟨fun y => ?_, by rw [hCc, hc]⟩
    rw [hcx y]
    simp_rw [hCc]
  refine ⟨fun n => ∫ x, C n x ∂μ, ?_, fun y => ?_⟩
  · exact integral_congr_ae (hae.mono fun x hx => hx.2)
  · rw [integral_congr_ae (hae.mono fun x hx => hx.1 y)]
    have := integral_finsetSum (μ := μ) Finset.univ (f := fun (n : Fin (d + 1)) x => ((y : ℂ) ^ (n : ℕ)) • C n x)
      (fun n _ => (hCint n).smul _)
    rw [this]
    apply Finset.sum_congr rfl
    intro n _
    rw [integral_smul]

end Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral
