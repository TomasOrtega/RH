import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.InFrameStabilizer

open GlobalTheory.SgAlg Matrix

namespace GlobalTheory.SgAlg

/- English proof (translation)
Take `⟨hinv, ⟨x₀, hx₀⟩, hred, -, hunit⟩` from `h`. Distinguish the cases in `hN : ∀ y : E, y ≠ 0 → y * σ y ≠ 0`. Use `left`. Use `⟨⟨σ x₀, x₀, hx₀⟩, mul_comm, ?_⟩` and prove the remaining obligations. Introduce `y hy`.

Establish `hfix : σ (y * σ y) = y * σ y`. Rewrite using `[map_mul, hinv, mul_comm]`. Take `⟨u, hu⟩` from `hunit _ hfix (hN y hy)`. Use `⟨σ y * (↑u⁻¹ : E), ?_⟩` and prove the remaining obligations. Rewrite using `[← mul_assoc, ← hu]`.

Conclude with `u.mul_inv`. Use `right push Not at hN`. Take `⟨y, hy, hyy⟩` from `hN`. Establish `hsfix : σ (y + σ y) = y + σ y`. Rewrite using `[map_add, hinv, add_comm]`.

Establish `hs : y + σ y ≠ 0`. Introduce `h0`. Establish `h1 : σ y = -y` using `eq_neg_of_add_eq_zero_right h0`. Rewrite `hyy` using `[h1]`. Establish `h2 : y ^ 2 = 0`.

Establish `: y * y = 0` using `by simpa using hyy`. Rewrite using `[pow_two, this]`. Conclude with `hy (pow_eq_zero_iff (two_ne_zero) |>.mp h2)`. Take `⟨s, hs'⟩` from `hunit _ hsfix hs`. Establish `hsum : (↑s⁻¹ : E) * (y + σ y) = 1` using `by rw [← hs', Units.inv_mul]`.

Establish `hσs : σ (↑s⁻¹ : E) * (y + σ y) = 1`. Establish `: σ ((↑s⁻¹ : E) * (y + σ y)) = 1`. Rewrite using `[hsum, map_one]`. Rewrite `this` using `[map_mul, hsfix]`. Then use the resulting hypothesis. Establish `hσs' : σ (↑s⁻¹ : E) = ↑s⁻¹`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_comm (y + σ y), hsum, mul_one]`. Use `_ = ↑s⁻¹ := by rw [← mul_assoc, hσs, one_mul]`. Use `set e : E := y * ↑s⁻¹ with he`. Establish `hσe : σ e = σ y * ↑s⁻¹` using `by rw [he, map_mul, hσs']`.

Establish `hadd : e + σ e = 1`. Rewrite using `[hσe, he, ← add_mul, mul_comm]`. Conclude with `hsum`. Establish `horth : e * σ e = 0`. Rewrite using `[hσe, he]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hidem : e * e = e`. Establish `: e * (e + σ e) = e` using `by rw [hadd, mul_one]`. Rewrite `this` using `[mul_add, horth, add_zero]`. Then use the resulting hypothesis. Use `⟨e, hidem, hadd, ?_⟩` and prove the remaining obligations.

Introduce `x hx`. Establish `hufix : σ (e * x + σ (e * x)) = e * x + σ (e * x)`. Rewrite using `[map_add, hinv, add_comm]`. Establish `heu : e * (e * x + σ (e * x)) = e * x`. Rewrite using `[map_mul, mul_add, ← mul_assoc, hidem, ← mul_assoc, horth, zero_mul, add_zero]`.

Establish `hu0 : e * x + σ (e * x) ≠ 0`. Introduce `h0`. Rewrite `heu` using `[h0, mul_zero]`. Conclude with `hx heu.symm`. Take `⟨u, hu⟩` from `hunit _ hufix hu0`.

Use `⟨↑u⁻¹, ?_⟩` and prove the remaining obligations. Rewrite using `[← heu, ← hu, mul_assoc, u.mul_inv, mul_one]`.
-/
theorem isField_or_exists_idempotent_of_isQA {E : Type} [CommRing E] (σ : E →+* E) (h : IsQA σ) :
    IsField E ∨ ∃ e : E, e * e = e ∧ e + σ e = 1 ∧ ∀ x : E, e * x ≠ 0 → ∃ y, e * x * y = e := by
  obtain ⟨hinv, ⟨x₀, hx₀⟩, hred, -, hunit⟩ := h
  by_cases hN : ∀ y : E, y ≠ 0 → y * σ y ≠ 0
  · left
    refine ⟨⟨σ x₀, x₀, hx₀⟩, mul_comm, ?_⟩
    intro y hy
    have hfix : σ (y * σ y) = y * σ y := by
      rw [map_mul, hinv, mul_comm]
    obtain ⟨u, hu⟩ := hunit _ hfix (hN y hy)
    refine ⟨σ y * (↑u⁻¹ : E), ?_⟩
    rw [← mul_assoc, ← hu]
    exact u.mul_inv
  · right
    push Not at hN
    obtain ⟨y, hy, hyy⟩ := hN
    have hsfix : σ (y + σ y) = y + σ y := by
      rw [map_add, hinv, add_comm]
    have hs : y + σ y ≠ 0 := by
      intro h0
      have h1 : σ y = -y := eq_neg_of_add_eq_zero_right h0
      rw [h1] at hyy
      have h2 : y ^ 2 = 0 := by
        have : y * y = 0 := by simpa using hyy
        rw [pow_two, this]
      exact hy (pow_eq_zero_iff (two_ne_zero) |>.mp h2)
    obtain ⟨s, hs'⟩ := hunit _ hsfix hs
    have hsum : (↑s⁻¹ : E) * (y + σ y) = 1 := by rw [← hs', Units.inv_mul]
    have hσs : σ (↑s⁻¹ : E) * (y + σ y) = 1 := by
      have : σ ((↑s⁻¹ : E) * (y + σ y)) = 1 := by
        rw [hsum, map_one]
      rwa [map_mul, hsfix] at this
    have hσs' : σ (↑s⁻¹ : E) = ↑s⁻¹ := by
      calc σ (↑s⁻¹ : E) = σ (↑s⁻¹ : E) * ((y + σ y) * ↑s⁻¹) := by
            rw [mul_comm (y + σ y), hsum, mul_one]
        _ = ↑s⁻¹ := by rw [← mul_assoc, hσs, one_mul]
    set e : E := y * ↑s⁻¹ with he
    have hσe : σ e = σ y * ↑s⁻¹ := by rw [he, map_mul, hσs']
    have hadd : e + σ e = 1 := by
      rw [hσe, he, ← add_mul, mul_comm]; exact hsum
    have horth : e * σ e = 0 := by
      rw [hσe, he]
      calc y * ↑s⁻¹ * (σ y * ↑s⁻¹) = (y * σ y) * (↑s⁻¹ * ↑s⁻¹) := by ring
        _ = 0 := by rw [hyy, zero_mul]
    have hidem : e * e = e := by
      have : e * (e + σ e) = e := by rw [hadd, mul_one]
      rwa [mul_add, horth, add_zero] at this
    refine ⟨e, hidem, hadd, ?_⟩
    intro x hx
    have hufix : σ (e * x + σ (e * x)) = e * x + σ (e * x) := by
      rw [map_add, hinv, add_comm]
    have heu : e * (e * x + σ (e * x)) = e * x := by
      rw [map_mul, mul_add, ← mul_assoc, hidem, ← mul_assoc, horth, zero_mul, add_zero]
    have hu0 : e * x + σ (e * x) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at heu
      exact hx heu.symm
    obtain ⟨u, hu⟩ := hunit _ hufix hu0
    refine ⟨↑u⁻¹, ?_⟩
    rw [← heu, ← hu, mul_assoc, u.mul_inv, mul_one]

end GlobalTheory.SgAlg
