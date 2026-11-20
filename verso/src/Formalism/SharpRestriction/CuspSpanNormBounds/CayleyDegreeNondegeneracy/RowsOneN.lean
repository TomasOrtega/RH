import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsNum

namespace Formalism.MainNotions.BridgeLemma₂

/- English proof (translation)
Establish `h0 : 0 ≤ h` using `by linarith`. Establish `hσ0 : 0 ≤ σ` using `by linarith`. Combine the equalities or inequalities in the displayed calculation. Apply the tactic sequence `rw [← Real.rpow_natCast σ 4, ← Real.rpow_mul hσ0] <;> norm_num`.
-/
theorem rpow_le_rpow_mul_rpow {P σ h c : ℝ} (hP : 1 ≤ P) (hσ : 1 ≤ σ) (h1 : 1 ≤ h) (hh : h ≤ P * σ ^ 4) (hc : 0 ≤ c) :
    h ^ c ≤ P ^ c * σ ^ (4 * c) := by
  have h0 : 0 ≤ h := by linarith
  have hσ0 : 0 ≤ σ := by linarith
  calc h ^ c ≤ (P * σ ^ 4) ^ c := Real.rpow_le_rpow h0 hh hc
    _ = P ^ c * (σ ^ 4) ^ c := Real.mul_rpow (by linarith) (by positivity)
    _ = P ^ c * σ ^ (4 * c) := by
      rw [← Real.rpow_natCast σ 4, ← Real.rpow_mul hσ0] <;> norm_num

/- English proof (translation)
Use polynomial arithmetic with `[mul_self_nonneg (a - b)]`.
-/
private theorem le_of_sq_le_sq_of_nonneg' {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  nlinarith [mul_self_nonneg (a - b)]

/- English proof (translation)
Establish `hx2 : 1 ≤ x ^ 2` using `by nlinarith`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hx2 (sq_nonneg x)]`.
-/
private theorem sq_le_pow_four_of_one_le {x : ℝ} (hx : 1 ≤ x) : x ^ 2 ≤ x ^ 4 := by
  have hx2 : 1 ≤ x ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hx2 (sq_nonneg x)]

/- English proof (translation)
Establish `h0 : 0 < σ` using `by linarith`. Establish `hsq : ∀ x : ℝ, (σ ^ x) ^ 2 = σ ^ (2 * x)` using `fun x => by`. Apply the tactic sequence `rw [← Real.rpow_natCast, ← Real.rpow_mul h0.le, mul_comm] <;> norm_num`. Simplify using `only [hsq, ← Real.rpow_add h0]`. Apply `Real.rpow_le_rpow_of_exponent_le hσ` to reduce the goal to its premises.

Combine the linear relations using `[le_abs_self a4]`.
-/
private theorem rpow_product_le_rpow_neg_sq_with_a4 {σ cS c4 cV a2 a4 dq e : ℝ} (hσ : 1 ≤ σ) (hcS : 0 ≤ cS)
    (he : 4 * c4 + 4 * cS + 4 * cV + a2 / 2 + |a4| - dq / 2 ≤ -e) :
    σ ^ (4 * cS) * (σ ^ (4 * c4)) ^ 2 * (σ ^ (4 * cV)) ^ 2 * (σ ^ a2 * (σ ^ a4) ^ 2 * σ ^ (-dq)) ≤
      (σ ^ (-e)) ^ 2 := by
  have h0 : 0 < σ := by linarith
  have hsq : ∀ x : ℝ, (σ ^ x) ^ 2 = σ ^ (2 * x) := fun x => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h0.le, mul_comm] <;> norm_num
  simp only [hsq, ← Real.rpow_add h0]
  apply Real.rpow_le_rpow_of_exponent_le hσ
  linarith [le_abs_self a4]

/- English proof (translation)
Establish `h0 : 0 < σ` using `by linarith`. Establish `hsq : ∀ x : ℝ, (σ ^ x) ^ 2 = σ ^ (2 * x)` using `fun x => by`. Apply the tactic sequence `rw [← Real.rpow_natCast, ← Real.rpow_mul h0.le, mul_comm] <;> norm_num`. Simplify using `only [hsq, ← Real.rpow_add h0]`. Apply `Real.rpow_le_rpow_of_exponent_le hσ` to reduce the goal to its premises.

Combine the linear relations using `[abs_nonneg a4]`.
-/
private theorem rpow_product_le_rpow_neg_sq {σ cS c4 cV a2 a4 dq e : ℝ} (hσ : 1 ≤ σ) (hcS : 0 ≤ cS)
    (he : 4 * c4 + 4 * cS + 4 * cV + a2 / 2 + |a4| - dq / 2 ≤ -e) :
    σ ^ (4 * cS) * (σ ^ (4 * c4)) ^ 2 * (σ ^ (4 * cV)) ^ 2 * (σ ^ a2 * σ ^ (-dq)) ≤
      (σ ^ (-e)) ^ 2 := by
  have h0 : 0 < σ := by linarith
  have hsq : ∀ x : ℝ, (σ ^ x) ^ 2 = σ ^ (2 * x) := fun x => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h0.le, mul_comm] <;> norm_num
  simp only [hsq, ← Real.rpow_add h0]
  apply Real.rpow_le_rpow_of_exponent_le hσ
  linarith [abs_nonneg a4]

set_option maxHeartbeats 800000 in

/- English proof (translation)
Establish `hσ₁0 : 0 < σ₁` using `by linarith`. Establish `hσ₂0 : 0 < σ₂` using `by linarith`. Establish `hS0₁ : 0 < hS₁` using `by linarith`. Establish `hS0₂ : 0 < hS₂` using `by linarith`. Establish `h40₁ : 0 < h4₁` using `by linarith`.

Establish `h40₂ : 0 < h4₂` using `by linarith`. Establish `hV0₁ : 0 < hV₁` using `by linarith`. Establish `hV0₂ : 0 < hV₂` using `by linarith`. Establish `hP0 : 0 < P` using `by linarith`. Establish `hL0₁ : 0 ≤ L₁` using `by rw [hL₁]; positivity`.

Establish `hL0₂ : 0 ≤ L₂` using `by rw [hL₂]; positivity`. Establish `hs0 : 0 ≤ Real.sqrt (L₁ / n₁) * Real.sqrt (L₂ / n₂)` using `by positivity`. Establish `hR0 : 0 ≤ (K4 * ((P ^ c4) ^ 2 * (P ^ cS) ^ 2 * (P ^ cV) ^ 2) * Γ * Ex * τ * Real.sqrt Q) * (σ₁ ^ (-e) * σ₂ ^ (-e))` using `by positivity`. Distinguish the cases in `hN : N ≤ 0`. Establish `h1 : 0 ≤ (-N) * (Real.sqrt (L₁ / n₁) * Real.sqrt (L₂ / n₂))` using `mul_nonneg (by linarith) hs0`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `push_neg at hN`. Apply `le_of_sq_le_sq_of_nonneg' hR0` to reduce the goal to its premises. Establish `hlhs : (N * (Real.sqrt (L₁ / n₁) * Real.sqrt (L₂ / n₂))) ^ 2 = N ^ 2 * (L₁ / n₁ * (L₂ / n₂))`. Rewrite using `[mul_pow, mul_pow, Real.sq_sqrt (div_nonneg hL0₁ hn₁.le), Real.sq_sqrt (div_nonneg hL0₂ hn₂.le)]`.

Establish `hrhs : ((K4 * ((P ^ c4) ^ 2 * (P ^ cS) ^ 2 * (P ^ cV) ^ 2) * Γ * Ex * τ * Real.sqrt Q) * (σ₁ ^ (-e) * σ₂ ^ (-e))) ^ 2 = K4 ^ 2 * Γ ^ 2 * Ex ^ 2 * τ ^ 2 * Q * ((P ^ c4) ^ 2 * (P ^ cS) ^ 2 * (P ^ cV) ^ 2) ^ 2 * ((σ₁ ^ (-e)) ^ 2 * (σ₂ ^ (-e)) ^ 2)`. Establish `hq` using `Real.sq_sqrt hQ`. Take the linear combination `(K4 ^ 2 * Γ ^ 2 * Ex ^ 2 * τ ^ 2 * ((P ^ c4) ^ 2 * (P ^ cS) ^ 2 * (P ^ cV) ^ 2) ^ 2 * ((σ₁ ^ (-e)) ^ 2 * (σ₂ ^ (-e)) ^ 2)) * hq`. Rewrite using `[hlhs, hrhs]`. Establish `e1 : n₁ * (L₁ / n₁) = L₁`.

Rewrite using `[mul_div_assoc', mul_comm, mul_div_assoc, div_self hn₁.ne', mul_one]`. Establish `e2 : n₂ * (L₂ / n₂) = L₂`. Rewrite using `[mul_div_assoc', mul_comm, mul_div_assoc, div_self hn₂.ne', mul_one]`. Establish `hN2 : N ^ 2 ≤ (hS₁ ^ cS * n₁ * (K4 * (h4₁ * h4₂) ^ c4)) * (hS₂ ^ cS * n₂ * (K4 * (h4₂ * h4₁) ^ c4))`. Rewrite using `[sq]; exact mul_le_mul hN₁ hN₂ hN.le (by positivity)`.

Establish `b1` using `rpow_le_rpow_mul_rpow hP hσ₁ hS1₁ hSP₁ hcS`. Establish `b2` using `rpow_le_rpow_mul_rpow hP hσ₂ hS1₂ hSP₂ hcS`. Establish `b3` using `rpow_le_rpow_mul_rpow hP hσ₁ h41₁ h4P₁ hc4`. Establish `b4` using `rpow_le_rpow_mul_rpow hP hσ₂ h41₂ h4P₂ hc4`. Establish `b5` using `rpow_le_rpow_mul_rpow hP hσ₁ hV1₁ hVP₁ hcV`.

Establish `b6` using `rpow_le_rpow_mul_rpow hP hσ₂ hV1₂ hVP₂ hcV`. Establish `hPp : (P ^ cS) ^ 2 * (P ^ c4) ^ 4 * (P ^ cV) ^ 4 ≤ ((P ^ c4) ^ 2 * (P ^ cS) ^ 2 * (P ^ cV) ^ 2) ^ 2`. Establish `hx : 1 ≤ P ^ cS` using `Real.one_le_rpow hP hcS`. Establish `h2 : (P ^ cS) ^ 2 ≤ (P ^ cS) ^ 4` using `sq_le_pow_four_of_one_le hx`. Combine the equalities or inequalities in the displayed calculation.

Establish `hσ1b` using `rpow_product_le_rpow_neg_sq_with_a4 hσ₁ hcS he`. Establish `hσ2b` using `rpow_product_le_rpow_neg_sq hσ₂ hcS he`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_comm h4₂ h4₁, Real.mul_rpow h40₁.le h40₂.le]`. Expand and normalize the polynomial expressions, which then agree.

Use `_ = K4 ^ 2 * (hS₁ ^ cS * hS₂ ^ cS) * (h4₁ ^ c4 * h4₂ ^ c4) ^ 2 * L₁ * L₂ := by rw [e1, e2]`. Use `_ = (K4 ^ 2 * Γ ^ 2 * Ex ^ 2 * τ ^ 2 * Q) * ((hS₁ ^ cS * hS₂ ^ cS) * (h4₁ ^ c4 * h4₂ ^ c4) ^ 2 * (hV₁ ^ cV) ^ 2 * (hV₂ ^ cV) ^ 2 * (σ₁ ^ a2 * (σ₁ ^ a4) ^ 2 * σ₁ ^ (-dq)) * (σ₂ ^ a2 * σ₂ ^ (-dq))) := by`. Rewrite using `[hL₁, hL₂]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ (K4 ^ 2 * Γ ^ 2 * Ex ^ 2 * τ ^ 2 * Q) * (((P ^ cS * σ₁ ^ (4 * cS)) * (P ^ cS * σ₂ ^ (4 * cS))) * ((P ^ c4 * σ₁ ^ (4 * c4)) * (P ^ c4 * σ₂ ^ (4 * c4))) ^ 2 * (P ^ cV * σ₁ ^ (4 * cV)) ^ 2 * (P ^ cV * σ₂ ^ (4 * cV)) ^ 2 * (σ₁ ^ a2 * (σ₁ ^ a4) ^ 2 * σ₁ ^ (-dq)) * (σ₂ ^ a2 * σ₂ ^ …`.

Use `_ = (K4 ^ 2 * Γ ^ 2 * Ex ^ 2 * τ ^ 2 * Q) * (((P ^ cS) ^ 2 * (P ^ c4) ^ 4 * (P ^ cV) ^ 4) * (σ₁ ^ (4 * cS) * (σ₁ ^ (4 * c4)) ^ 2 * (σ₁ ^ (4 * cV)) ^ 2 * (σ₁ ^ a2 * (σ₁ ^ a4) ^ 2 * σ₁ ^ (-dq))) * (σ₂ ^ (4 * cS) * (σ₂ ^ (4 * c4)) ^ 2 * (σ₂ ^ (4 * cV)) ^ 2 * (σ₂ ^ a2 * σ₂ ^ (-dq)))) …`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ (K4 ^ 2 * Γ ^ 2 * Ex ^ 2 * τ ^ 2 * Q) * (((P ^ c4) ^ 2 * (P ^ cS) ^ 2 * (P ^ cV) ^ 2) ^ 2 * (σ₁ ^ (-e)) ^ 2 * (σ₂ ^ (-e)) ^ 2) := by`. Apply `mul_le_mul_of_nonneg_left _ (by positivity)` to reduce the goal to its premises. Conclude with `mul_le_mul (mul_le_mul hPp hσ1b (by positivity) (by positivity)) hσ2b (by positivity) (by positivity)`.

Use `_ = K4 ^ 2 * Γ ^ 2 * Ex ^ 2 * τ ^ 2 * Q * ((P ^ c4) ^ 2 * (P ^ cS) ^ 2 * (P ^ cV) ^ 2) ^ 2 * ((σ₁ ^ (-e)) ^ 2 * (σ₂ ^ (-e)) ^ 2) := by ring`.
-/
theorem mul_sqrt_div_mul_sqrt_div_le {P σ₁ σ₂ hS₁ hS₂ h4₁ h4₂ hV₁ hV₂ cS c4 cV Γ Ex a2 a4 dq τ Q n₁ n₂ K4 N L₁ L₂ e : ℝ}
    (hP : 1 ≤ P) (hσ₁ : 1 ≤ σ₁) (hσ₂ : 1 ≤ σ₂)
    (hS1₁ : 1 ≤ hS₁) (hS1₂ : 1 ≤ hS₂) (h41₁ : 1 ≤ h4₁) (h41₂ : 1 ≤ h4₂) (hV1₁ : 1 ≤ hV₁) (hV1₂ : 1 ≤ hV₂)
    (hSP₁ : hS₁ ≤ P * σ₁ ^ 4) (hSP₂ : hS₂ ≤ P * σ₂ ^ 4) (h4P₁ : h4₁ ≤ P * σ₁ ^ 4) (h4P₂ : h4₂ ≤ P * σ₂ ^ 4)
    (hVP₁ : hV₁ ≤ P * σ₁ ^ 4) (hVP₂ : hV₂ ≤ P * σ₂ ^ 4) (hcS : 0 ≤ cS) (hc4 : 0 ≤ c4) (hcV : 0 ≤ cV)
    (hΓ : 0 ≤ Γ) (hEx : 0 ≤ Ex) (hτ : 0 ≤ τ) (hQ : 0 ≤ Q) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hK4 : 0 ≤ K4)
    (hN₁ : N ≤ hS₁ ^ cS * n₁ * (K4 * (h4₁ * h4₂) ^ c4)) (hN₂ : N ≤ hS₂ ^ cS * n₂ * (K4 * (h4₂ * h4₁) ^ c4))
    (hL₁ : L₁ = (hV₁ ^ cV) ^ 2 * (Γ * σ₁ ^ a2) * (Ex * σ₁ ^ a4) ^ 2 * τ * Q * σ₁ ^ (-dq))
    (hL₂ : L₂ = (hV₂ ^ cV) ^ 2 * (Γ * σ₂ ^ a2) * σ₂ ^ (-dq) * τ)
    (he : 4 * c4 + 4 * cS + 4 * cV + a2 / 2 + |a4| - dq / 2 ≤ -e) :
    N * (Real.sqrt (L₁ / n₁) * Real.sqrt (L₂ / n₂)) ≤
      (K4 * ((P ^ c4) ^ 2 * (P ^ cS) ^ 2 * (P ^ cV) ^ 2) * Γ * Ex * τ * Real.sqrt Q) * (σ₁ ^ (-e) * σ₂ ^ (-e)) := by
  have hσ₁0 : 0 < σ₁ := by linarith
  have hσ₂0 : 0 < σ₂ := by linarith
  have hS0₁ : 0 < hS₁ := by linarith
  have hS0₂ : 0 < hS₂ := by linarith
  have h40₁ : 0 < h4₁ := by linarith
  have h40₂ : 0 < h4₂ := by linarith
  have hV0₁ : 0 < hV₁ := by linarith
  have hV0₂ : 0 < hV₂ := by linarith
  have hP0 : 0 < P := by linarith
  have hL0₁ : 0 ≤ L₁ := by rw [hL₁]; positivity
  have hL0₂ : 0 ≤ L₂ := by rw [hL₂]; positivity
  have hs0 : 0 ≤ Real.sqrt (L₁ / n₁) * Real.sqrt (L₂ / n₂) := by positivity
  have hR0 : 0 ≤ (K4 * ((P ^ c4) ^ 2 * (P ^ cS) ^ 2 * (P ^ cV) ^ 2) * Γ * Ex * τ * Real.sqrt Q) *
      (σ₁ ^ (-e) * σ₂ ^ (-e)) := by positivity
  by_cases hN : N ≤ 0
  · have h1 : 0 ≤ (-N) * (Real.sqrt (L₁ / n₁) * Real.sqrt (L₂ / n₂)) := mul_nonneg (by linarith) hs0
    linarith
  push_neg at hN
  apply le_of_sq_le_sq_of_nonneg' hR0
  have hlhs : (N * (Real.sqrt (L₁ / n₁) * Real.sqrt (L₂ / n₂))) ^ 2 = N ^ 2 * (L₁ / n₁ * (L₂ / n₂)) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (div_nonneg hL0₁ hn₁.le), Real.sq_sqrt (div_nonneg hL0₂ hn₂.le)]
  have hrhs : ((K4 * ((P ^ c4) ^ 2 * (P ^ cS) ^ 2 * (P ^ cV) ^ 2) * Γ * Ex * τ * Real.sqrt Q) *
      (σ₁ ^ (-e) * σ₂ ^ (-e))) ^ 2 = K4 ^ 2 * Γ ^ 2 * Ex ^ 2 * τ ^ 2 * Q *
      ((P ^ c4) ^ 2 * (P ^ cS) ^ 2 * (P ^ cV) ^ 2) ^ 2 * ((σ₁ ^ (-e)) ^ 2 * (σ₂ ^ (-e)) ^ 2) := by
    have hq := Real.sq_sqrt hQ
    linear_combination (K4 ^ 2 * Γ ^ 2 * Ex ^ 2 * τ ^ 2 * ((P ^ c4) ^ 2 * (P ^ cS) ^ 2 * (P ^ cV) ^ 2) ^ 2 *
      ((σ₁ ^ (-e)) ^ 2 * (σ₂ ^ (-e)) ^ 2)) * hq
  rw [hlhs, hrhs]
  have e1 : n₁ * (L₁ / n₁) = L₁ := by
    rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self hn₁.ne', mul_one]
  have e2 : n₂ * (L₂ / n₂) = L₂ := by
    rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self hn₂.ne', mul_one]
  have hN2 : N ^ 2 ≤ (hS₁ ^ cS * n₁ * (K4 * (h4₁ * h4₂) ^ c4)) * (hS₂ ^ cS * n₂ * (K4 * (h4₂ * h4₁) ^ c4)) := by
    rw [sq]; exact mul_le_mul hN₁ hN₂ hN.le (by positivity)
  have b1 := rpow_le_rpow_mul_rpow hP hσ₁ hS1₁ hSP₁ hcS
  have b2 := rpow_le_rpow_mul_rpow hP hσ₂ hS1₂ hSP₂ hcS
  have b3 := rpow_le_rpow_mul_rpow hP hσ₁ h41₁ h4P₁ hc4
  have b4 := rpow_le_rpow_mul_rpow hP hσ₂ h41₂ h4P₂ hc4
  have b5 := rpow_le_rpow_mul_rpow hP hσ₁ hV1₁ hVP₁ hcV
  have b6 := rpow_le_rpow_mul_rpow hP hσ₂ hV1₂ hVP₂ hcV
  have hPp : (P ^ cS) ^ 2 * (P ^ c4) ^ 4 * (P ^ cV) ^ 4 ≤ ((P ^ c4) ^ 2 * (P ^ cS) ^ 2 * (P ^ cV) ^ 2) ^ 2 := by
    have hx : 1 ≤ P ^ cS := Real.one_le_rpow hP hcS
    have h2 : (P ^ cS) ^ 2 ≤ (P ^ cS) ^ 4 := sq_le_pow_four_of_one_le hx
    calc (P ^ cS) ^ 2 * (P ^ c4) ^ 4 * (P ^ cV) ^ 4 ≤ (P ^ cS) ^ 4 * (P ^ c4) ^ 4 * (P ^ cV) ^ 4 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 (by positivity)) (by positivity)
      _ = ((P ^ c4) ^ 2 * (P ^ cS) ^ 2 * (P ^ cV) ^ 2) ^ 2 := by ring
  have hσ1b := rpow_product_le_rpow_neg_sq_with_a4 hσ₁ hcS he
  have hσ2b := rpow_product_le_rpow_neg_sq hσ₂ hcS he
  calc N ^ 2 * (L₁ / n₁ * (L₂ / n₂))
      ≤ ((hS₁ ^ cS * n₁ * (K4 * (h4₁ * h4₂) ^ c4)) * (hS₂ ^ cS * n₂ * (K4 * (h4₂ * h4₁) ^ c4))) *
          (L₁ / n₁ * (L₂ / n₂)) := mul_le_mul_of_nonneg_right hN2 (by positivity)
    _ = K4 ^ 2 * (hS₁ ^ cS * hS₂ ^ cS) * (h4₁ ^ c4 * h4₂ ^ c4) ^ 2 * (n₁ * (L₁ / n₁)) *
          (n₂ * (L₂ / n₂)) := by
        rw [mul_comm h4₂ h4₁, Real.mul_rpow h40₁.le h40₂.le]; ring
    _ = K4 ^ 2 * (hS₁ ^ cS * hS₂ ^ cS) * (h4₁ ^ c4 * h4₂ ^ c4) ^ 2 * L₁ * L₂ := by rw [e1, e2]
    _ = (K4 ^ 2 * Γ ^ 2 * Ex ^ 2 * τ ^ 2 * Q) * ((hS₁ ^ cS * hS₂ ^ cS) * (h4₁ ^ c4 * h4₂ ^ c4) ^ 2 *
          (hV₁ ^ cV) ^ 2 * (hV₂ ^ cV) ^ 2 * (σ₁ ^ a2 * (σ₁ ^ a4) ^ 2 * σ₁ ^ (-dq)) *
          (σ₂ ^ a2 * σ₂ ^ (-dq))) := by
        rw [hL₁, hL₂]; ring
    _ ≤ (K4 ^ 2 * Γ ^ 2 * Ex ^ 2 * τ ^ 2 * Q) * (((P ^ cS * σ₁ ^ (4 * cS)) * (P ^ cS * σ₂ ^ (4 * cS))) *
          ((P ^ c4 * σ₁ ^ (4 * c4)) * (P ^ c4 * σ₂ ^ (4 * c4))) ^ 2 *
          (P ^ cV * σ₁ ^ (4 * cV)) ^ 2 * (P ^ cV * σ₂ ^ (4 * cV)) ^ 2 *
          (σ₁ ^ a2 * (σ₁ ^ a4) ^ 2 * σ₁ ^ (-dq)) * (σ₂ ^ a2 * σ₂ ^ (-dq))) := by
        gcongr
    _ = (K4 ^ 2 * Γ ^ 2 * Ex ^ 2 * τ ^ 2 * Q) * (((P ^ cS) ^ 2 * (P ^ c4) ^ 4 * (P ^ cV) ^ 4) *
          (σ₁ ^ (4 * cS) * (σ₁ ^ (4 * c4)) ^ 2 * (σ₁ ^ (4 * cV)) ^ 2 * (σ₁ ^ a2 * (σ₁ ^ a4) ^ 2 * σ₁ ^ (-dq))) *
          (σ₂ ^ (4 * cS) * (σ₂ ^ (4 * c4)) ^ 2 * (σ₂ ^ (4 * cV)) ^ 2 * (σ₂ ^ a2 * σ₂ ^ (-dq)))) := by
        ring
    _ ≤ (K4 ^ 2 * Γ ^ 2 * Ex ^ 2 * τ ^ 2 * Q) * (((P ^ c4) ^ 2 * (P ^ cS) ^ 2 * (P ^ cV) ^ 2) ^ 2 *
          (σ₁ ^ (-e)) ^ 2 * (σ₂ ^ (-e)) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul (mul_le_mul hPp hσ1b (by positivity) (by positivity)) hσ2b (by positivity)
          (by positivity)
    _ = K4 ^ 2 * Γ ^ 2 * Ex ^ 2 * τ ^ 2 * Q * ((P ^ c4) ^ 2 * (P ^ cS) ^ 2 * (P ^ cV) ^ 2) ^ 2 *
          ((σ₁ ^ (-e)) ^ 2 * (σ₂ ^ (-e)) ^ 2) := by ring

end Formalism.MainNotions.BridgeLemma₂
