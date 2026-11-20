import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSquareOfValuedSubOneLt
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

/- English proof (translation)
Establish `key : ∀ c : K, c ≠ 0 → ∃ n : ℤ, w c ^ 2 = WithZero.exp (2 * n)`. Introduce `c hc`. Establish `h0 : w c ≠ 0` using `by simpa using hc`. Use `⟨WithZero.log (w c), ?_⟩` and prove the remaining obligations. Rewrite using `[two_mul, WithZero.exp_add, WithZero.exp_log h0, sq]`.

Introduce `a b hab`. Establish `ha2 : w (a ^ 2) = w a ^ 2` using `map_pow _ _ _`. Establish `hb2 : w (δ * b ^ 2) = w b ^ 2` using `by rw [map_mul, hδ, one_mul, map_pow]`. Break down `lt_trichotomy (w a) (w b) with h | h | h` into its components or cases. Establish `hb : b ≠ 0`.

Introduce and unpack `rfl`. Simplify using `at h`. Establish `hlt : w (a ^ 2) < w (δ * b ^ 2)`. Rewrite using `[ha2, hb2]`. Conclude with `pow_lt_pow_left₀ h zero_le two_ne_zero`.

Rewrite using `[w.map_sub_eq_of_lt_right hlt, hb2]`. Conclude with `key b hb`. Establish `ha : a ≠ 0`. Introduce and unpack `rfl`. Break down `hab with h' | h'` into its components or cases.

Conclude with `h' rfl`. Rewrite `h` using `[map_zero]`. Conclude with `h' (by simpa using h.symm)`. Establish `ha0 : w a ≠ 0` using `by simpa using ha`. Establish `hb : b ≠ 0`.

Introduce and unpack `rfl`. Rewrite `h` using `[map_zero]`. Conclude with `ha0 h`. Establish `hle : w (a ^ 2 - δ * b ^ 2) ≤ w a ^ 2`. Use `(w.map_sub _ _).trans (max_le ha2.le ?_)` and prove the remaining obligations.

Rewrite using `[hb2, h]`. Break down `hle.lt_or_eq with hlt | heq` into its components or cases. It suffices to derive a contradiction. Apply `hn` to reduce the goal to its premises. Establish `e : δ * (b / a) ^ 2 - 1 = -((a ^ 2 - δ * b ^ 2) / a ^ 2)` using `by field_simp; ring`.

Establish `hs : IsSquare (δ * (b / a) ^ 2)`. Apply `hsq` to reduce the goal to its premises. Rewrite using `[e, Valuation.map_neg, map_div₀, ha2, div_lt_one₀ (pow_pos (zero_lt_iff.2 ha0) 2)]`. Conclude with `hlt`. Take `⟨r, hr⟩` from `hs`.

Use `⟨r * a / b, ?_⟩` and prove the remaining obligations. Establish `: δ = (δ * (b / a) ^ 2) * (a / b) ^ 2` using `by field_simp`. Rewrite using `[this, hr]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[heq]`.

Conclude with `key a ha`. Establish `ha : a ≠ 0`. Introduce and unpack `rfl`. Simplify using `at h`. Establish `hlt : w (δ * b ^ 2) < w (a ^ 2)`.

Rewrite using `[ha2, hb2]`. Conclude with `pow_lt_pow_left₀ h zero_le two_ne_zero`. Rewrite using `[w.map_sub_eq_of_lt_left hlt, ha2]`. Conclude with `key a ha`.
-/
theorem evenNorms_of_unit_nonsquare {K : Type} [Field K] (w : Valuation K ℤᵐ⁰)
    (hsq : ∀ x : K, w (x - 1) < 1 → IsSquare x) (δ : K) (hδ : w δ = 1) (hn : ¬ IsSquare δ) :
    EvenNorms w δ := by
  have key : ∀ c : K, c ≠ 0 → ∃ n : ℤ, w c ^ 2 = WithZero.exp (2 * n) := by
    intro c hc
    have h0 : w c ≠ 0 := by simpa using hc
    refine ⟨WithZero.log (w c), ?_⟩
    rw [two_mul, WithZero.exp_add, WithZero.exp_log h0, sq]
  intro a b hab
  have ha2 : w (a ^ 2) = w a ^ 2 := map_pow _ _ _
  have hb2 : w (δ * b ^ 2) = w b ^ 2 := by rw [map_mul, hδ, one_mul, map_pow]
  rcases lt_trichotomy (w a) (w b) with h | h | h
  · have hb : b ≠ 0 := by
      rintro rfl
      simp at h
    have hlt : w (a ^ 2) < w (δ * b ^ 2) := by
      rw [ha2, hb2]; exact pow_lt_pow_left₀ h zero_le two_ne_zero
    rw [w.map_sub_eq_of_lt_right hlt, hb2]
    exact key b hb
  · have ha : a ≠ 0 := by
      rintro rfl
      rcases hab with h' | h'
      · exact h' rfl
      · rw [map_zero] at h
        exact h' (by simpa using h.symm)
    have ha0 : w a ≠ 0 := by simpa using ha
    have hb : b ≠ 0 := by
      rintro rfl
      rw [map_zero] at h
      exact ha0 h
    have hle : w (a ^ 2 - δ * b ^ 2) ≤ w a ^ 2 := by
      refine (w.map_sub _ _).trans (max_le ha2.le ?_)
      rw [hb2, h]
    rcases hle.lt_or_eq with hlt | heq
    · exfalso
      apply hn
      have e : δ * (b / a) ^ 2 - 1 = -((a ^ 2 - δ * b ^ 2) / a ^ 2) := by
        field_simp; ring
      have hs : IsSquare (δ * (b / a) ^ 2) := by
        apply hsq
        rw [e, Valuation.map_neg, map_div₀, ha2, div_lt_one₀ (pow_pos (zero_lt_iff.2 ha0) 2)]
        exact hlt
      obtain ⟨r, hr⟩ := hs
      refine ⟨r * a / b, ?_⟩
      have : δ = (δ * (b / a) ^ 2) * (a / b) ^ 2 := by field_simp
      rw [this, hr]; ring
    · rw [heq]; exact key a ha
  · have ha : a ≠ 0 := by
      rintro rfl
      simp at h
    have hlt : w (δ * b ^ 2) < w (a ^ 2) := by
      rw [ha2, hb2]; exact pow_lt_pow_left₀ h zero_le two_ne_zero
    rw [w.map_sub_eq_of_lt_left hlt, ha2]
    exact key a ha

/- English proof (translation)
Introduce `F _ _ v h2 δ hδ hn`. Use `evenNorms_of_unit_nonsquare _ (fun x hx => ?_) δ hδ hn` and prove the remaining obligations. Apply `GlobalTheory.LocalQuad.isSquare_of_valued_sub_one_lt F v x` to reduce the goal to its premises. Establish `: (4 : v.adicCompletion F) = 2 * 2` using `by norm_num`. Rewrite using `[this, map_mul, h2, one_mul]`.

Conclude with `hx`.
-/
theorem evenNorms_of_odd_place : ∀ (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)), Valued.v (2 : v.adicCompletion F) = 1 →
    ∀ δ : v.adicCompletion F, Valued.v δ = 1 → ¬ IsSquare δ → EvenNorms Valued.v δ := by
  intro F _ _ v h2 δ hδ hn
  refine evenNorms_of_unit_nonsquare _ (fun x hx => ?_) δ hδ hn
  apply GlobalTheory.LocalQuad.isSquare_of_valued_sub_one_lt F v x
  have : (4 : v.adicCompletion F) = 2 * 2 := by norm_num
  rw [this, map_mul, h2, one_mul]
  exact hx

end GlobalTheory.QNorm
