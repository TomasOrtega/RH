import Mathlib

/- English proof (translation)
Introduce `E _ _ _ d x hd hx`. Take `⟨φ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Establish `hsq : (NumberField.IsCMField.complexConj E x) ^ 2 = x ^ 2`. Rewrite using `[← map_pow, hx, map_neg, map_natCast]`. Break down `sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h` into its components or cases.

It suffices to derive a contradiction. Establish `h1` using `NumberField.IsCMField.complexEmbedding_complexConj E φ x`. Rewrite `h1` using `[h]`. Take `⟨r, hr⟩` from `Complex.conj_eq_iff_real.mp h1.symm`. Establish `h2 : (φ x) ^ 2 = -(d : ℂ)` using `by rw [← map_pow, hx, map_neg, map_natCast]`.

Rewrite `h2` using `[hr]`. Establish `h3 : r ^ 2 = -(d : ℝ)` using `by exact_mod_cast h2`. Establish `h4 : (0 : ℝ) < d` using `by exact_mod_cast hd`. Use polynomial arithmetic with `[sq_nonneg r]`. Conclude with `h`.
-/
theorem UpperTheory.Reformulated.B.ConjugateSqrtNeg.conj_sqrt_neg :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E]
    [inst_2 : NumberField.IsCMField E] (d : ℕ) (x : E),
    (0 : ℕ) < d → x ^ (2 : ℕ) = -(↑d : E) → (NumberField.IsCMField.complexConj E : E → E) x = -x := by
  intro E _ _ _ d x hd hx
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hsq : (NumberField.IsCMField.complexConj E x) ^ 2 = x ^ 2 := by
    rw [← map_pow, hx, map_neg, map_natCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exfalso
    have h1 := NumberField.IsCMField.complexEmbedding_complexConj E φ x
    rw [h] at h1
    obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.mp h1.symm
    have h2 : (φ x) ^ 2 = -(d : ℂ) := by rw [← map_pow, hx, map_neg, map_natCast]
    rw [hr] at h2
    have h3 : r ^ 2 = -(d : ℝ) := by exact_mod_cast h2
    have h4 : (0 : ℝ) < d := by exact_mod_cast hd
    nlinarith [sq_nonneg r]
  · exact h
