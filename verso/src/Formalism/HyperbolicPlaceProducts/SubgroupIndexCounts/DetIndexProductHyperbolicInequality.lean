import Formalism.HyperbolicPlaceProducts.DetIndexProductHyperbolicInequality

open Module

noncomputable section

namespace Formalism.SLP.GlobalBoundRefinements.P

open Formalism.SLP.GlobalBoundRefinements

/- English proof (translation)
Introduce `V _ _ h hsym y A y' A' hw hyA hyA'`. Establish `hAy : h A y = 0` using `by rw [hsym y A, hyA, map_zero]`. Establish `hAy' : h A' y' = 0` using `by rw [hsym y' A', hyA', map_zero]`. Establish `e1 : h (y - A) (y - A) = h y y + h A A`. Simplify using `only [map_sub, LinearMap.sub_apply, hyA, hAy]`.

Expand and normalize the polynomial expressions, which then agree. Establish `e2 : h (y' + A') (y' + A') = h y' y' + h A' A'`. Simplify using `only [map_add, LinearMap.add_apply, hyA', hAy']`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← e1, ← e2, hw]`.
-/
theorem polarization_of_orthogonal_splittings : Formalism.SLP.GlobalBoundRefinements.Polarise := by
  intro V _ _ h hsym y A y' A' hw hyA hyA'
  have hAy : h A y = 0 := by rw [hsym y A, hyA, map_zero]
  have hAy' : h A' y' = 0 := by rw [hsym y' A', hyA', map_zero]
  have e1 : h (y - A) (y - A) = h y y + h A A := by
    simp only [map_sub, LinearMap.sub_apply, hyA, hAy]
    ring
  have e2 : h (y' + A') (y' + A') = h y' y' + h A' A' := by
    simp only [map_add, LinearMap.add_apply, hyA', hAy']
    ring
  rw [← e1, ← e2, hw]

/- English proof (translation)
Introduce `R M _ _ _ _ e v hv`. Establish `hinj : Function.Injective (fun f : M ≃ₗ[R] M => fun i => f (v i))`. Introduce `f g hfg`. Apply `LinearEquiv.toLinearMap_injective` to reduce the goal to its premises. Conclude with `LinearMap.ext_on_range hv (fun i => congrFun hfg i)`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem card_linearEquiv_le : Formalism.SLP.GlobalBoundRefinements.AutCount := by
  intro R M _ _ _ _ e v hv
  have hinj : Function.Injective (fun f : M ≃ₗ[R] M => fun i => f (v i)) := by
    intro f g hfg
    apply LinearEquiv.toLinearMap_injective
    exact LinearMap.ext_on_range hv (fun i => congrFun hfg i)
  calc Nat.card (M ≃ₗ[R] M) ≤ Nat.card (Fin e → M) := Nat.card_le_card_of_injective _ hinj
    _ = Nat.card M ^ e := by rw [Nat.card_fun, Nat.card_fin]

set_option maxHeartbeats 800000 in
/- English proof (translation)
Introduce `a b c d T T' hT hT' hform`. Establish `h10` using `hform 1 0`. Establish `h01` using `hform 0 1`. Simplify using `only [mul_one, mul_zero, add_zero, zero_add, norm_one, norm_zero, one_pow] at h10 h01`. Evaluate the numerical expressions using `at h10 h01`.

Establish `e1 : ‖a‖ ^ 2 - 1 = T' * ‖c‖ ^ 2 / T`. Clear the denominators using the available nonvanishing facts. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e2 : ‖d‖ ^ 2 - 1 = T * ‖b‖ ^ 2 / T'`. Clear the denominators using the available nonvanishing facts.

Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨e1, e2, fun ha => ?_⟩` and prove the remaining obligations. Establish `hc2 : ‖c‖ ^ 2 = 0`. Rewrite `h10` using `[ha]`. Use polynomial arithmetic with `[sq_nonneg ‖c‖]`.

Establish `hc : c = 0` using `by simpa using hc2`. Establish `haa : a * (starRingEnd ℂ a) = 1`. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq, ha]`. Evaluate the numerical expressions. Establish `hx` using `hform (starRingEnd ℂ a * b) 1`.

Establish `h2b : a * (starRingEnd ℂ a * b) + b * 1 = 2 * b`. Rewrite using `[← mul_assoc, haa]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hx` using `[h2b, hc]`. Simplify using `only [zero_mul, zero_add, mul_one, norm_mul, Complex.norm_conj, ha, one_mul, norm_one, one_pow] at hx`.

Evaluate the numerical expressions using `at hx`. Establish `hb2 : ‖b‖ ^ 2 = 0` using `by nlinarith [sq_nonneg ‖b‖]`. Establish `hb : b = 0` using `by simpa using hb2`. Use `⟨hc, hb, ?_⟩` and prove the remaining obligations. Rewrite `e2` using `[hb, norm_zero]`.

Establish `hd2 : ‖d‖ ^ 2 = 1` using `by linarith [e2, show T * (0:ℝ) ^ 2 / T' = 0 by simp]`. Use polynomial arithmetic with `[norm_nonneg d]`.
-/
theorem coefficients_of_form_preserving : Formalism.SLP.GlobalBoundRefinements.FormCoeff := by
  intro a b c d T T' hT hT' hform
  have h10 := hform 1 0
  have h01 := hform 0 1
  simp only [mul_one, mul_zero, add_zero, zero_add, norm_one, norm_zero, one_pow] at h10 h01
  norm_num at h10 h01
  have e1 : ‖a‖ ^ 2 - 1 = T' * ‖c‖ ^ 2 / T := by
    field_simp
    linarith
  have e2 : ‖d‖ ^ 2 - 1 = T * ‖b‖ ^ 2 / T' := by
    field_simp
    linarith
  refine ⟨e1, e2, fun ha => ?_⟩
  have hc2 : ‖c‖ ^ 2 = 0 := by
    rw [ha] at h10
    nlinarith [sq_nonneg ‖c‖]
  have hc : c = 0 := by simpa using hc2
  have haa : a * (starRingEnd ℂ a) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ha]
    norm_num
  have hx := hform (starRingEnd ℂ a * b) 1
  have h2b : a * (starRingEnd ℂ a * b) + b * 1 = 2 * b := by
    rw [← mul_assoc, haa]
    ring
  rw [h2b, hc] at hx
  simp only [zero_mul, zero_add, mul_one, norm_mul, Complex.norm_conj, ha, one_mul, norm_one,
    one_pow] at hx
  norm_num at hx
  have hb2 : ‖b‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖b‖]
  have hb : b = 0 := by simpa using hb2
  refine ⟨hc, hb, ?_⟩
  rw [hb, norm_zero] at e2
  have hd2 : ‖d‖ ^ 2 = 1 := by linarith [e2, show T * (0:ℝ) ^ 2 / T' = 0 by simp]
  nlinarith [norm_nonneg d]

/- English proof (translation)
Introduce `ι _ T al n ch sh Nr hT hal hsh hch hbd hNr h1`. Establish `hsq : ∀ v, T v * al v ^ 2 ≤ (n v * (1 + ch v) / sh v) ^ 2`. Introduce `v`. Establish `h0 : 0 ≤ Real.sqrt (T v) * al v` using `mul_nonneg (Real.sqrt_nonneg _) (hal v)`. Establish `h2` using `pow_le_pow_left₀ h0 (hbd v) 2`.

Rewrite `h2` using `[mul_pow, Real.sq_sqrt (hT v).le]`. Then use the resulting hypothesis. Establish `hprod : (∏ v, T v) * ∏ v, al v ^ 2 ≤ (∏ v, n v ^ 2) * ∏ v, ((1 + ch v) / sh v) ^ 2`. Rewrite using `[← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]`. Apply `Finset.prod_le_prod` to reduce the goal to its premises. Introduce `v _`.

Conclude with `mul_nonneg (hT v).le (sq_nonneg _)`. Introduce `v _`. Combine the equalities or inequalities in the displayed calculation. Establish `hTpos : 0 ≤ ∏ v, T v` using `Finset.prod_nonneg fun v _ => (hT v).le`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[div_le_iff₀ hNr]`. Combine the equalities or inequalities in the displayed calculation. Use `_ ≤ _ := hprod`.
-/
theorem prod_places_hyperbolic_inequality : Formalism.SLP.GlobalBoundRefinements.ProdPlacesHyperbolicInequality := by
  intro ι _ T al n ch sh Nr hT hal hsh hch hbd hNr h1
  have hsq : ∀ v, T v * al v ^ 2 ≤ (n v * (1 + ch v) / sh v) ^ 2 := by
    intro v
    have h0 : 0 ≤ Real.sqrt (T v) * al v := mul_nonneg (Real.sqrt_nonneg _) (hal v)
    have h2 := pow_le_pow_left₀ h0 (hbd v) 2
    rwa [mul_pow, Real.sq_sqrt (hT v).le] at h2
  have hprod : (∏ v, T v) * ∏ v, al v ^ 2 ≤ (∏ v, n v ^ 2) * ∏ v, ((1 + ch v) / sh v) ^ 2 := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod
    · intro v _
      exact mul_nonneg (hT v).le (sq_nonneg _)
    · intro v _
      calc T v * al v ^ 2 ≤ (n v * (1 + ch v) / sh v) ^ 2 := hsq v
        _ = n v ^ 2 * ((1 + ch v) / sh v) ^ 2 := by ring
  have hTpos : 0 ≤ ∏ v, T v := Finset.prod_nonneg fun v _ => (hT v).le
  calc (∏ v, T v) / Nr ≤ (∏ v, T v) * ∏ v, al v ^ 2 := by
        rw [div_le_iff₀ hNr]
        calc (∏ v, T v) = (∏ v, T v) * 1 := (mul_one _).symm
          _ ≤ (∏ v, T v) * ((∏ v, al v ^ 2) * Nr) := mul_le_mul_of_nonneg_left h1 hTpos
          _ = (∏ v, T v) * (∏ v, al v ^ 2) * Nr := by ring
    _ ≤ _ := hprod

/- English proof (translation)
Introduce `detM dLa₁ dLa₂ dPs₁ dPs₂ P₁ P₂ dQ₁ dQ₂ i₁ i₂ G0₁ G0₂ g NT K₁ K₂ Nr₁ Nr₂ e f hP₁ hP₂ hQ₁ hQ₂ hg hi₁ hi₂ hL₁ hL₂ hNT hK₁ hK₂ hN₁ hN₂ hD₁ hD₂ hPs₁ hPs₂ hG₁ hG₂ hB₁ hB₂ hgQ`. Substitute `hPs₁ hPs₂` using the available equality. Establish `hG₁0 : 0 ≤ G0₁ / Nr₁` using `le_trans (by positivity) hG₁`. Establish `hG₂0 : 0 ≤ G0₂ / Nr₂` using `le_trans (by positivity) hG₂`. Establish `hG₁' : 0 ≤ G0₁`.

Establish `h` using `mul_nonneg hG₁0 hN₁.le`. Rewrite `h` using `[div_mul_cancel₀ _ hN₁.ne']`. Then use the resulting hypothesis. Establish `hG₂' : 0 ≤ G0₂`. Establish `h` using `mul_nonneg hG₂0 hN₂.le`. Rewrite `h` using `[div_mul_cancel₀ _ hN₂.ne']`. Then use the resulting hypothesis.

Establish `hD0 : 0 ≤ detM`. Rewrite using `[hD₁]`. Check the signs of the components of the expression. Establish `hDD : detM * detM = dLa₁ * dLa₂ / ((P₁ * P₂) * (dQ₁ * dQ₂))`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[div_mul_div_comm]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hX2 : (detM * i₁ * i₂) ^ 2 = (dLa₁ * i₁ ^ 2) * (dLa₂ * i₂ ^ 2) / ((P₁ * P₂) * (dQ₁ * dQ₂))`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hDD]`. Clear the denominators using the available nonvanishing facts. Establish `hnum : (dLa₁ * i₁ ^ 2) * (dLa₂ * i₂ ^ 2) ≤ (G0₁ / Nr₁) * (G0₂ / Nr₂)` using `mul_le_mul hG₁ hG₂ (by positivity) hG₁0`. Establish `hgQ' : g ^ (2 * f * e) / 4 ^ (e * f) ≤ dQ₁ * dQ₂`. Rewrite using `[div_le_iff₀ (by positivity)]`.

Combine the linear relations using `[hgQ, show (4:ℝ) ^ (e * f) * dQ₁ * dQ₂ = dQ₁ * dQ₂ * 4 ^ (e * f) by ring]`. Establish `hden : (NT / (Nr₂ * K₂ ^ 2)) * (NT / (Nr₁ * K₁ ^ 2)) * (g ^ (2 * f * e) / 4 ^ (e * f)) ≤ (P₁ * P₂) * (dQ₁ * dQ₂)` using `mul_le_mul (mul_le_mul hB₁ hB₂ (by positivity) hP₁.le) hgQ' (by positivity) (by positivity)`. Establish `hX2le : (detM * i₁ * i₂) ^ 2 ≤ (G0₁ / Nr₁) * (G0₂ / Nr₂) / ((NT / (Nr₂ * K₂ ^ 2)) * (NT / (Nr₁ * K₁ ^ 2)) * (g ^ (2 * f * e) / 4 ^ (e * f)))`. Rewrite using `[hX2]`. Conclude with `div_le_div₀ (mul_nonneg hG₁0 hG₂0) hnum (by positivity) hden`.

Establish `hpw : ((2 / g) ^ (e * f)) ^ 2 = 4 ^ (e * f) / g ^ (2 * f * e)`. Rewrite using `[← pow_mul, div_pow, show (4:ℝ) = 2 ^ 2 by norm_num, ← pow_mul, show e * f * 2 = 2 * (e * f) by ring, show 2 * f * e = 2 * (e * f) by ring]`. Establish `hY2 : ((2 / g) ^ (e * f) * Real.sqrt (G0₁ * G0₂) * K₁ * K₂ / NT) ^ 2 = (G0₁ / Nr₁) * (G0₂ / Nr₂) / ((NT / (Nr₂ * K₂ ^ 2)) * (NT / (Nr₁ * K₁ ^ 2)) * (g ^ (2 * f * e) / 4 ^ (e * f)))`. Rewrite using `[div_pow, mul_pow, mul_pow, mul_pow, hpw, Real.sq_sqrt (mul_nonneg hG₁' hG₂')]`. Clear the denominators using the available nonvanishing facts.

Establish `hY0 : 0 ≤ (2 / g) ^ (e * f) * Real.sqrt (G0₁ * G0₂) * K₁ * K₂ / NT` using `by positivity`. Rewrite `hX2le` using `[← hY2]`. Conclude with `(pow_le_pow_iff_left₀ (by positivity) hY0 two_ne_zero).mp hX2le`.
-/
theorem det_index_product_hyperbolic_inequality : Formalism.SLP.GlobalBoundRefinements.DetIndexProductHyperbolicInequality := by
  intro detM dLa₁ dLa₂ dPs₁ dPs₂ P₁ P₂ dQ₁ dQ₂ i₁ i₂ G0₁ G0₂ g NT K₁ K₂ Nr₁ Nr₂ e f
    hP₁ hP₂ hQ₁ hQ₂ hg hi₁ hi₂ hL₁ hL₂ hNT hK₁ hK₂ hN₁ hN₂ hD₁ hD₂ hPs₁ hPs₂ hG₁ hG₂ hB₁ hB₂ hgQ
  subst hPs₁ hPs₂
  have hG₁0 : 0 ≤ G0₁ / Nr₁ := le_trans (by positivity) hG₁
  have hG₂0 : 0 ≤ G0₂ / Nr₂ := le_trans (by positivity) hG₂
  have hG₁' : 0 ≤ G0₁ := by
    have h := mul_nonneg hG₁0 hN₁.le
    rwa [div_mul_cancel₀ _ hN₁.ne'] at h
  have hG₂' : 0 ≤ G0₂ := by
    have h := mul_nonneg hG₂0 hN₂.le
    rwa [div_mul_cancel₀ _ hN₂.ne'] at h
  have hD0 : 0 ≤ detM := by
    rw [hD₁]
    positivity
  have hDD : detM * detM = dLa₁ * dLa₂ / ((P₁ * P₂) * (dQ₁ * dQ₂)) := by
    calc detM * detM = (dLa₁ / (P₁ * dQ₁)) * (dLa₂ / (P₂ * dQ₂)) := by rw [← hD₁, ← hD₂]
      _ = dLa₁ * dLa₂ / ((P₁ * P₂) * (dQ₁ * dQ₂)) := by
        rw [div_mul_div_comm]
        congr 1
        ring
  have hX2 : (detM * i₁ * i₂) ^ 2 = (dLa₁ * i₁ ^ 2) * (dLa₂ * i₂ ^ 2) / ((P₁ * P₂) * (dQ₁ * dQ₂)) := by
    calc (detM * i₁ * i₂) ^ 2 = (detM * detM) * i₁ ^ 2 * i₂ ^ 2 := by ring
      _ = _ := by
        rw [hDD]
        field_simp
  have hnum : (dLa₁ * i₁ ^ 2) * (dLa₂ * i₂ ^ 2) ≤ (G0₁ / Nr₁) * (G0₂ / Nr₂) :=
    mul_le_mul hG₁ hG₂ (by positivity) hG₁0
  have hgQ' : g ^ (2 * f * e) / 4 ^ (e * f) ≤ dQ₁ * dQ₂ := by
    rw [div_le_iff₀ (by positivity)]
    linarith [hgQ, show (4:ℝ) ^ (e * f) * dQ₁ * dQ₂ = dQ₁ * dQ₂ * 4 ^ (e * f) by ring]
  have hden : (NT / (Nr₂ * K₂ ^ 2)) * (NT / (Nr₁ * K₁ ^ 2)) * (g ^ (2 * f * e) / 4 ^ (e * f)) ≤
      (P₁ * P₂) * (dQ₁ * dQ₂) :=
    mul_le_mul (mul_le_mul hB₁ hB₂ (by positivity) hP₁.le) hgQ' (by positivity) (by positivity)
  have hX2le : (detM * i₁ * i₂) ^ 2 ≤ (G0₁ / Nr₁) * (G0₂ / Nr₂) /
      ((NT / (Nr₂ * K₂ ^ 2)) * (NT / (Nr₁ * K₁ ^ 2)) * (g ^ (2 * f * e) / 4 ^ (e * f))) := by
    rw [hX2]
    exact div_le_div₀ (mul_nonneg hG₁0 hG₂0) hnum (by positivity) hden
  have hpw : ((2 / g) ^ (e * f)) ^ 2 = 4 ^ (e * f) / g ^ (2 * f * e) := by
    rw [← pow_mul, div_pow, show (4:ℝ) = 2 ^ 2 by norm_num, ← pow_mul,
      show e * f * 2 = 2 * (e * f) by ring, show 2 * f * e = 2 * (e * f) by ring]
  have hY2 : ((2 / g) ^ (e * f) * Real.sqrt (G0₁ * G0₂) * K₁ * K₂ / NT) ^ 2 =
      (G0₁ / Nr₁) * (G0₂ / Nr₂) /
        ((NT / (Nr₂ * K₂ ^ 2)) * (NT / (Nr₁ * K₁ ^ 2)) * (g ^ (2 * f * e) / 4 ^ (e * f))) := by
    rw [div_pow, mul_pow, mul_pow, mul_pow, hpw, Real.sq_sqrt (mul_nonneg hG₁' hG₂')]
    field_simp
  have hY0 : 0 ≤ (2 / g) ^ (e * f) * Real.sqrt (G0₁ * G0₂) * K₁ * K₂ / NT := by positivity
  rw [← hY2] at hX2le
  exact (pow_le_pow_iff_left₀ (by positivity) hY0 two_ne_zero).mp hX2le

end Formalism.SLP.GlobalBoundRefinements.P
