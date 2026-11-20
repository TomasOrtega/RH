import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementE
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KurComplete

noncomputable section
open NumberField

namespace Formalism.L2.Th1.GD

open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)

section SlopeTestRemainingChoices

variable {p : ℕ} [hp : Fact p.Prime]

/- English proof (translation)
Establish `h : ‖(((p : ℚ_[p]) : ℚ_[p]) : ℂ_[p])‖ = ‖(p : ℚ_[p])‖` using `PadicComplex.norm_extends' p _`. Establish `h2 : (((p : ℚ_[p]) : ℚ_[p]) : ℂ_[p]) = (p : ℂ_[p])`. Simplify using the standard rewrite rules. Rewrite `h` using `[h2]`. Rewrite using `[h]`.

Conclude with `Padic.norm_p`.
-/
lemma norm_p_eq : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
  have h : ‖(((p : ℚ_[p]) : ℚ_[p]) : ℂ_[p])‖ = ‖(p : ℚ_[p])‖ := PadicComplex.norm_extends' p _
  have h2 : (((p : ℚ_[p]) : ℚ_[p]) : ℂ_[p]) = (p : ℂ_[p]) := by
    simp
  rw [h2] at h
  rw [h]
  exact Padic.norm_p

/- English proof (translation)
Rewrite using `[norm_p_eq]`. Establish `: (0 : ℝ) < p` using `by exact_mod_cast hp.out.pos`. Check the signs of the components of the expression.
-/
lemma norm_p_pos : 0 < ‖(p : ℂ_[p])‖ := by
  rw [norm_p_eq]
  have : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  positivity

/- English proof (translation)
Rewrite using `[norm_p_eq]`. Establish `: (1 : ℝ) < p` using `by exact_mod_cast hp.out.one_lt`. Conclude with `inv_lt_one_of_one_lt₀ this`.
-/
lemma norm_p_lt_one : ‖(p : ℂ_[p])‖ < 1 := by
  rw [norm_p_eq]
  have : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  exact inv_lt_one_of_one_lt₀ this

/- English proof (translation)
Take `⟨P, hP, hPx⟩` from `hx`. Establish `hx' : IsIntegral (NormedField.valuation (K` using `ℂ_[p])).integer x := by`. Use `⟨P.map (Int.castRingHom _), hP.map _, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval₂_map, ← hPx]`. Use `congr 1`.

Establish `h` using `(Valuation.integer.integers (NormedField.valuation (K := ℂ_[p]))).mem_of_integral hx'`. Rewrite `h` using `[Valuation.mem_integer_iff, NormedField.valuation_apply]`. Conclude with `h` after adjusting the coercions.
-/
lemma norm_le_one_of_isIntegralElem {x : ℂ_[p]} (hx : (Int.castRingHom ℂ_[p]).IsIntegralElem x) :
    ‖x‖ ≤ 1 := by
  obtain ⟨P, hP, hPx⟩ := hx
  have hx' : IsIntegral (NormedField.valuation (K := ℂ_[p])).integer x := by
    refine ⟨P.map (Int.castRingHom _), hP.map _, ?_⟩
    rw [Polynomial.eval₂_map, ← hPx]
    congr 1
  have h := (Valuation.integer.integers (NormedField.valuation (K := ℂ_[p]))).mem_of_integral hx'
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

/- English proof (translation)
Take `⟨P, hP, hPx⟩` from `RingOfIntegers.isIntegral_coe y`. Use `norm_le_one_of_isIntegralElem ⟨P, hP, ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg ψ hPx`. Rewrite `h` using `[Polynomial.hom_eval₂, map_zero]`. Rewrite using `[← h]`.

Use `congr 1`. Conclude with `Subsingleton.elim _ _`.
-/
lemma norm_map_le_one {E : Type} [Field E] [NumberField E] (ψ : E →+* ℂ_[p]) (y : 𝓞 E) :
    ‖ψ (y : E)‖ ≤ 1 := by
  obtain ⟨P, hP, hPx⟩ := RingOfIntegers.isIntegral_coe y
  refine norm_le_one_of_isIntegralElem ⟨P, hP, ?_⟩
  have h := congrArg ψ hPx
  rw [Polynomial.hom_eval₂, map_zero] at h
  rw [← h]
  congr 1
  exact Subsingleton.elim _ _

/- English proof (translation)
Distinguish the cases in `h0 : a = 0`. Rewrite using `[h0, norm_zero]`. Conclude with `(zpow_pos norm_p_pos _).le`. Take `⟨k, hk⟩` from `Formalism.L2.Th1.D.kurUnram p a ha h0`. Rewrite `h`, the goal using `[hk]`.

Establish `h1 : m < k` using `(zpow_lt_zpow_iff_right_of_lt_one₀ norm_p_pos norm_p_lt_one).1 h`. Conclude with `(zpow_le_zpow_iff_right_of_lt_one₀ norm_p_pos norm_p_lt_one).2 (by omega)`.
-/
lemma kur_step {a : ℂ_[p]} (ha : a ∈ MaximalUnramifiedExtension p) (m : ℤ) (h : ‖a‖ < ‖(p : ℂ_[p])‖ ^ m) :
    ‖a‖ ≤ ‖(p : ℂ_[p])‖ ^ (m + 1) := by
  by_cases h0 : a = 0
  · rw [h0, norm_zero]
    exact (zpow_pos norm_p_pos _).le
  · obtain ⟨k, hk⟩ := Formalism.L2.Th1.D.kurUnram p a ha h0
    rw [hk] at h ⊢
    have h1 : m < k := (zpow_lt_zpow_iff_right_of_lt_one₀ norm_p_pos norm_p_lt_one).1 h
    exact (zpow_le_zpow_iff_right_of_lt_one₀ norm_p_pos norm_p_lt_one).2 (by omega)

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `p _ _ E _ _ s δ φ hδ hsδ hss hK`. Use `set q : ℝ := ‖(p : ℂ_[p])‖ with hq`. Establish `hq0 : 0 < q` using `norm_p_pos`. Establish `hq1 : q < 1` using `norm_p_lt_one`. Use `set d : ℝ := ‖φ δ‖ with hd`.

Establish `hd0 : 0 ≤ d` using `norm_nonneg _`. Establish `hdq : d ^ 2 = q`. Rewrite using `[hd, ← norm_pow, ← map_pow, hδ, map_neg, map_natCast, norm_neg]`. Establish `hdpos : 0 < d`. Break down `hd0.lt_or_eq with h | h` into its components or cases.

Conclude with `h`. Rewrite `hdq` using `[← h]`. Evaluate the numerical expressions using `at hdq`. Conclude with `absurd hdq hq0.ne`. Establish `hd1 : d < 1`.

Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_lt]`. Establish `: 1 ≤ d ^ 2` using `one_le_pow₀ h`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hqd : q ≤ d`.

Rewrite using `[← hdq]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hδ0 : δ ≠ 0`. Introduce `h`. Rewrite `hdpos` using `[hd, h, map_zero, norm_zero]`.

Conclude with `lt_irrefl _ hdpos`. Establish `hdr : d = q ^ (1 / 2 : ℝ)`. Rewrite using `[← Real.sqrt_eq_rpow, ← hdq, Real.sqrt_sq hd0]`. Establish `key : ∀ b : ℂ_[p], b ∈ MaximalUnramifiedExtension p → ‖b‖ * d ≤ 1 → ‖b‖ ≤ 1`. Introduce `b hb h`.

Establish `h1 : ‖b‖ < q ^ (-1 : ℤ)`. Rewrite using `[zpow_neg_one, ← hdq, ← one_div, lt_div_iff₀ (by positivity)]`. Combine the equalities or inequalities in the displayed calculation. Use `kur_step hb (-1) h1` as an intermediate fact. Simplify using `using this`.

Establish `hint : ∀ y : 𝓞 E, ‖φ (y : E)‖ ≤ 1` using `fun y => norm_map_le_one φ y`. Establish `hints : ∀ y : 𝓞 E, ‖φ (s (y : E))‖ ≤ 1` using `fun y => norm_map_le_one (φ.comp (s : E →+* E)) y`. Use `⟨hdr, ?_, ?_⟩` and prove the remaining obligations. Introduce `y`. Rewrite using `[← hdr]`.

Use `set w : E := (y : E) - s (y : E) with hw`. Establish `hsw : s (w / δ) = w / δ`. Rewrite using `[map_div₀, hsδ, hw, map_sub, hss, div_neg, ← neg_div, neg_sub]`. Establish `hw1 : ‖φ w‖ ≤ 1`. Rewrite using `[hw, map_sub, sub_eq_add_neg]`.

Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hint y) ?_)` and prove the remaining obligations. Rewrite using `[norm_neg]`. Conclude with `hints y`. Establish `hmul : ‖φ (w / δ)‖ * d = ‖φ w‖`. Rewrite using `[hd, ← norm_mul, ← map_mul, div_mul_cancel₀ _ hδ0]`.

Establish `h1` using `key _ (hK _ hsw) (by rw [hmul]; exact hw1)`. Rewrite using `[← map_sub, ← hw, ← hmul]`. Conclude with `mul_le_of_le_one_left hd0 h1`. Introduce `y hy set a : E := ((y : E) + s (y : E)) / 2 with ha set b : E := ((y : E) - s (y : E)) / (2 * δ) with hb`. Establish `hsa : s a = a`.

Rewrite using `[ha, map_div₀, map_add, hss, map_ofNat, add_comm]`. Establish `hsb : s b = b`. Rewrite using `[hb, map_div₀, map_mul, hsδ, map_sub, hss, map_ofNat, mul_neg, div_neg, ← neg_div, neg_sub]`. Establish `hy' : (y : E) = a + b * δ`. Rewrite using `[ha, hb]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hnb : ‖φ (b * δ)‖ = ‖φ b‖ * d` using `by rw [map_mul, norm_mul]`. Distinguish the cases in `hne : ‖φ a‖ = ‖φ (b * δ)‖`. Distinguish the cases in `hb0 : φ b = 0`.

Establish `ha0 : φ a = 0`. Rewrite `hne` using `[hnb, hb0, norm_zero, zero_mul]`. Conclude with `norm_eq_zero.1 hne`. Rewrite using `[hy', map_add, map_mul, ha0, hb0, zero_mul, add_zero, norm_zero]`. Conclude with `hd0`.

It suffices to derive a contradiction. Establish `ha0 : φ a ≠ 0`. Introduce `h`. Rewrite `hne` using `[hnb, h, norm_zero]`. Establish `: 0 < ‖φ b‖ * d` using `mul_pos (norm_pos_iff.2 hb0) hdpos`.

Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨k, hk⟩` from `Formalism.L2.Th1.D.kurUnram p _ (hK _ hsa) ha0`. Take `⟨m, hm⟩` from `Formalism.L2.Th1.D.kurUnram p _ (hK _ hsb) hb0`. Establish `h2 : (‖φ a‖) ^ 2 = (‖φ b‖) ^ 2 * q`. Rewrite using `[hne, hnb, mul_pow, hdq]`.

Rewrite `h2` using `[hk, hm, ← hq]`. Establish `h3 : q ^ (2 * k) = q ^ (2 * m + 1)`. Rewrite using `[zpow_add₀ hq0.ne', zpow_one, mul_comm 2 k, mul_comm 2 m, zpow_mul, zpow_mul]`. Conclude with `h2` after adjusting the coercions. Establish `h4` using `zpow_right_injective₀ hq0 hq1.ne h3`.

Use linear arithmetic over natural numbers and integers. Establish `hmax : ‖φ (y : E)‖ = max ‖φ a‖ ‖φ (b * δ)‖`. Rewrite using `[hy', map_add]`. Conclude with `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne`. Rewrite `hy`, the goal using `[hmax]`.

Establish `hA : ‖φ a‖ < 1` using `(le_max_left _ _).trans_lt hy`. Establish `hB : ‖φ (b * δ)‖ < 1` using `(le_max_right _ _).trans_lt hy`. Use `max_le ?_ ?_` and prove the remaining obligations. Use `kur_step (hK _ hsa) 0 (by simpa using hA)` as an intermediate fact. Rewrite `this` using `[zero_add, zpow_one]`.

Conclude with `this.trans hqd`. Rewrite `hB`, the goal using `[hnb]`. Conclude with `mul_le_of_le_one_left hd0 (key _ (hK _ hsb) hB.le)`.
-/
theorem InertiaRam_proof : InertiaRam := by
  intro p _ _ E _ _ s δ φ hδ hsδ hss hK
  set q : ℝ := ‖(p : ℂ_[p])‖ with hq
  have hq0 : 0 < q := norm_p_pos
  have hq1 : q < 1 := norm_p_lt_one
  set d : ℝ := ‖φ δ‖ with hd
  have hd0 : 0 ≤ d := norm_nonneg _
  have hdq : d ^ 2 = q := by
    rw [hd, ← norm_pow, ← map_pow, hδ, map_neg, map_natCast, norm_neg]
  have hdpos : 0 < d := by
    rcases hd0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hdq
      norm_num at hdq
      exact absurd hdq hq0.ne
  have hd1 : d < 1 := by
    by_contra h
    rw [not_lt] at h
    have : 1 ≤ d ^ 2 := one_le_pow₀ h
    linarith
  have hqd : q ≤ d := by
    rw [← hdq]
    nlinarith
  have hδ0 : δ ≠ 0 := by
    intro h
    rw [hd, h, map_zero, norm_zero] at hdpos
    exact lt_irrefl _ hdpos
  have hdr : d = q ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow, ← hdq, Real.sqrt_sq hd0]

  have key : ∀ b : ℂ_[p], b ∈ MaximalUnramifiedExtension p → ‖b‖ * d ≤ 1 → ‖b‖ ≤ 1 := by
    intro b hb h
    have h1 : ‖b‖ < q ^ (-1 : ℤ) := by
      rw [zpow_neg_one, ← hdq, ← one_div, lt_div_iff₀ (by positivity)]
      calc ‖b‖ * d ^ 2 = (‖b‖ * d) * d := by ring
        _ ≤ 1 * d := mul_le_mul_of_nonneg_right h hd0
        _ < 1 := by rw [one_mul]; exact hd1
    have := kur_step hb (-1) h1
    simpa using this
  have hint : ∀ y : 𝓞 E, ‖φ (y : E)‖ ≤ 1 := fun y => norm_map_le_one φ y
  have hints : ∀ y : 𝓞 E, ‖φ (s (y : E))‖ ≤ 1 := fun y => norm_map_le_one (φ.comp (s : E →+* E)) y
  refine ⟨hdr, ?_, ?_⟩
  · intro y
    rw [← hdr]
    set w : E := (y : E) - s (y : E) with hw
    have hsw : s (w / δ) = w / δ := by
      rw [map_div₀, hsδ, hw, map_sub, hss, div_neg, ← neg_div, neg_sub]
    have hw1 : ‖φ w‖ ≤ 1 := by
      rw [hw, map_sub, sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hint y) ?_)
      rw [norm_neg]
      exact hints y
    have hmul : ‖φ (w / δ)‖ * d = ‖φ w‖ := by
      rw [hd, ← norm_mul, ← map_mul, div_mul_cancel₀ _ hδ0]
    have h1 := key _ (hK _ hsw) (by rw [hmul]; exact hw1)
    rw [← map_sub, ← hw, ← hmul]
    exact mul_le_of_le_one_left hd0 h1
  · intro y hy
    set a : E := ((y : E) + s (y : E)) / 2 with ha
    set b : E := ((y : E) - s (y : E)) / (2 * δ) with hb
    have hsa : s a = a := by
      rw [ha, map_div₀, map_add, hss, map_ofNat, add_comm]
    have hsb : s b = b := by
      rw [hb, map_div₀, map_mul, hsδ, map_sub, hss, map_ofNat, mul_neg, div_neg, ← neg_div, neg_sub]
    have hy' : (y : E) = a + b * δ := by
      rw [ha, hb]
      field_simp
      ring
    have hnb : ‖φ (b * δ)‖ = ‖φ b‖ * d := by rw [map_mul, norm_mul]
    by_cases hne : ‖φ a‖ = ‖φ (b * δ)‖
    ·
      by_cases hb0 : φ b = 0
      · have ha0 : φ a = 0 := by
          rw [hnb, hb0, norm_zero, zero_mul] at hne
          exact norm_eq_zero.1 hne
        rw [hy', map_add, map_mul, ha0, hb0, zero_mul, add_zero, norm_zero]
        exact hd0
      · exfalso
        have ha0 : φ a ≠ 0 := by
          intro h
          rw [hnb, h, norm_zero] at hne
          have : 0 < ‖φ b‖ * d := mul_pos (norm_pos_iff.2 hb0) hdpos
          linarith
        obtain ⟨k, hk⟩ := Formalism.L2.Th1.D.kurUnram p _ (hK _ hsa) ha0
        obtain ⟨m, hm⟩ := Formalism.L2.Th1.D.kurUnram p _ (hK _ hsb) hb0
        have h2 : (‖φ a‖) ^ 2 = (‖φ b‖) ^ 2 * q := by
          rw [hne, hnb, mul_pow, hdq]
        rw [hk, hm, ← hq] at h2
        have h3 : q ^ (2 * k) = q ^ (2 * m + 1) := by
          rw [zpow_add₀ hq0.ne', zpow_one, mul_comm 2 k, mul_comm 2 m, zpow_mul, zpow_mul]
          exact_mod_cast h2
        have h4 := zpow_right_injective₀ hq0 hq1.ne h3
        omega
    · have hmax : ‖φ (y : E)‖ = max ‖φ a‖ ‖φ (b * δ)‖ := by
        rw [hy', map_add]
        exact IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
      rw [hmax] at hy ⊢
      have hA : ‖φ a‖ < 1 := (le_max_left _ _).trans_lt hy
      have hB : ‖φ (b * δ)‖ < 1 := (le_max_right _ _).trans_lt hy
      refine max_le ?_ ?_
      · have := kur_step (hK _ hsa) 0 (by simpa using hA)
        rw [zero_add, zpow_one] at this
        exact this.trans hqd
      · rw [hnb] at hB ⊢
        exact mul_le_of_le_one_left hd0 (key _ (hK _ hsb) hB.le)

end Formalism.L2.Th1.GD
