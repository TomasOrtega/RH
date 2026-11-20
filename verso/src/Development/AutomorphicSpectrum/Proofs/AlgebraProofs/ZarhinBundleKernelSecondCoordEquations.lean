import Mathlib

open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Flat

/- English proof (translation)
Introduce `E _ _ u n M hn hu hM ⟨x, hx⟩`. Establish `hlt : ∀ φ : E →+* ℂ, ‖φ (x : E)‖ < 1`. Introduce `φ`. Establish `h1 : (φ (u : E)) ^ n = 1`. Use `congrArg (fun y : 𝓞 E => φ (y : E)) hu` as an intermediate fact.

Simplify using `using this`. Establish `h2 : ‖φ (u : E)‖ = 1`. Use `congrArg norm h1` as an intermediate fact. Rewrite `this` using `[norm_pow, norm_one]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this`.

Establish `h3 : φ (u : E) - 1 = (M : ℂ) * φ (x : E)`. Use `congrArg (fun y : 𝓞 E => φ (y : E)) hx` as an intermediate fact. Simplify using `using this`. Establish `h4 : (M : ℝ) * ‖φ (x : E)‖ ≤ 2`. Establish `h5` using `norm_sub_le (φ (u : E)) 1`.

Rewrite `h5` using `[h3, norm_mul, h2, norm_one, Complex.norm_natCast]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h6 : (3 : ℝ) ≤ M` using `by exact_mod_cast hM`. Use polynomial arithmetic with `[norm_nonneg (φ (x : E))]`. Assume the negation of the conclusion as `hne`.

Establish `hx0 : (x : E) ≠ 0`. Introduce `h0`. Establish `: x = 0` using `by exact_mod_cast h0`. Rewrite `hx` using `[this, mul_zero, sub_eq_zero]`. Conclude with `hne hx`.

Take `⟨k, hk, hpow⟩` from `NumberField.Embeddings.pow_eq_one_of_norm_le_one E ℂ hx0 (RingOfIntegers.isIntegral_coe x) (fun φ => (hlt φ).le)`. Take `⟨φ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Establish `h7` using `congrArg (fun y : E => ‖φ y‖) hpow`. Simplify using `only [map_pow, norm_pow, map_one, norm_one] at h7`. Establish `h8` using `(pow_eq_one_iff_of_nonneg (norm_nonneg _) hk.ne').1 h7`.

Conclude with `(hlt φ).ne h8`.
-/
theorem root_of_unity_eq_one_of_dvd_sub_one :
    ∀ (E : Type) [Field E] [NumberField E] (u : 𝓞 E) (n M : ℕ),
      0 < n → u ^ n = 1 → 3 ≤ M → (M : 𝓞 E) ∣ u - 1 → u = 1 := by
  intro E _ _ u n M hn hu hM ⟨x, hx⟩
  have hlt : ∀ φ : E →+* ℂ, ‖φ (x : E)‖ < 1 := by
    intro φ
    have h1 : (φ (u : E)) ^ n = 1 := by
      have := congrArg (fun y : 𝓞 E => φ (y : E)) hu
      simpa using this
    have h2 : ‖φ (u : E)‖ = 1 := by
      have := congrArg norm h1
      rw [norm_pow, norm_one] at this
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this
    have h3 : φ (u : E) - 1 = (M : ℂ) * φ (x : E) := by
      have := congrArg (fun y : 𝓞 E => φ (y : E)) hx
      simpa using this
    have h4 : (M : ℝ) * ‖φ (x : E)‖ ≤ 2 := by
      have h5 := norm_sub_le (φ (u : E)) 1
      rw [h3, norm_mul, h2, norm_one, Complex.norm_natCast] at h5
      linarith
    have h6 : (3 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith [norm_nonneg (φ (x : E))]
  by_contra hne
  have hx0 : (x : E) ≠ 0 := by
    intro h0
    have : x = 0 := by exact_mod_cast h0
    rw [this, mul_zero, sub_eq_zero] at hx
    exact hne hx
  obtain ⟨k, hk, hpow⟩ := NumberField.Embeddings.pow_eq_one_of_norm_le_one E ℂ hx0
    (RingOfIntegers.isIntegral_coe x) (fun φ => (hlt φ).le)
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h7 := congrArg (fun y : E => ‖φ y‖) hpow
  simp only [map_pow, norm_pow, map_one, norm_one] at h7
  have h8 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) hk.ne').1 h7
  exact (hlt φ).ne h8

end GlobalTheory.CompanionTheory.Ar.Flat
