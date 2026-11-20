import Mathlib
import Formalism.MirabolicMackeyTheory.ErrSumGoodExact
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.LocalConditionsComposeGeneral
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PrimeLogOverP
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PrimeLogOverPSqTail

open Module NumberField IsDedekindDomain

namespace Formalism.EigenvalueLevelCeiling

open Formalism.DivisionValues

/- English proof (translation)
Assemble the required witnesses or components as `⟨_root_.sum_log_p_over_p Y hY, chebyshev_theta_log_four Y (by linarith), _root_.prime_log_over_sq_tail X2 hX2⟩`.
-/
theorem primeBoundsExact (Y X2 : ℝ) (hY : 1 < Y) (hX2 : 0 < X2) :
    (∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime ∧ (p : ℝ) ≤ Y) →
      ∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ≤ Real.log Y) ∧
    (∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime ∧ (p : ℝ) ≤ Y) → ∑ p ∈ Q, Real.log (p : ℝ) ≤ Real.log 4 * Y) ∧
    (∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime ∧ X2 < (p : ℝ)) →
      ∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ^ 2 ≤ 2.04 / X2) :=
  ⟨_root_.sum_log_p_over_p Y hY, chebyshev_theta_log_four Y (by linarith),
    _root_.prime_log_over_sq_tail X2 hX2⟩

/- English proof (translation)
Introduce `PI hPI Y X2 A1 A2 kw T Cth Cadd th add hY hX2 hA1 hA2 hkw hT hth hadd hD`. Take `⟨hB1, hB2, hB3⟩` from `primeBoundsExact Y X2 hY hX2`. Take `⟨hD1, hD2⟩` from `hD`. Establish `hQ : ∀ p ∈ PI.filter (fun p : ℕ => (p : ℝ) ≤ Y), p.Prime ∧ (p : ℝ) ≤ Y`. Introduce `p hp`.

Rewrite `hp` using `[Finset.mem_filter]`. Conclude with `⟨hPI p hp.1, hp.2⟩`. Establish `hQ' : ∀ p ∈ PI.filter (fun p : ℕ => (p : ℝ) ≤ Y), p.Prime` using `fun p hp => (hQ p hp).1`. Establish `hR : ∀ p ∈ (PI.filter (fun p : ℕ => (p : ℝ) ≤ Y)).filter (fun p : ℕ => X2 < (p : ℝ)), p.Prime ∧ X2 < (p : ℝ)`. Introduce `p hp`.

Rewrite `hp` using `[Finset.mem_filter]`. Conclude with `⟨(hQ p hp.1).1, hp.2⟩`. Establish `e1` using `hB1 _ hQ`. Establish `e2` using `hB2 _ hQ`. Establish `e3` using `hB3 _ hR`.

Establish `e4` using `hD1 _ hQ'`. Establish `e5` using `hD2 _ hQ'`. Rewrite `e1`, `e2`, `e4`, `e5` using `[Finset.sum_filter]`. Rewrite `e3` using `[Finset.sum_filter, Finset.sum_filter]`. Establish `hsum : ∑ p ∈ PI, Real.log (p : ℝ) * errGood Y X2 A1 A2 kw T th add p = 2 * A1 * (∑ p ∈ PI, if (p : ℝ) ≤ Y then Real.log (p : ℝ) / (p : ℝ) else 0) + 2 * kw * (∑ p ∈ PI, if (p : ℝ) ≤ Y then th p * Real.log (p : ℝ) else 0) + 2 * (T * ∑ p ∈ PI, if (p : ℝ) ≤ Y then add p * Real.log (p …`.

Simplify using `only [Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl (fun p _ => ?_)` and prove the remaining obligations. Unfold `errGood`. Apply the tactic sequence `split_ifs <;> ring`. Rewrite using `[hsum]`.

Establish `h1` using `mul_le_mul_of_nonneg_left e1 hA1`. Establish `h2` using `mul_le_mul_of_nonneg_left e4 hkw`. Establish `h4` using `mul_le_mul_of_nonneg_left e3 hA2`. Establish `h4' : A2 * (2.04 / X2) = 2.04 * A2 / X2` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem error_sum_good_places_exact : ErrSumGoodExact := by
  intro PI hPI Y X2 A1 A2 kw T Cth Cadd th add hY hX2 hA1 hA2 hkw hT hth hadd hD
  obtain ⟨hB1, hB2, hB3⟩ := primeBoundsExact Y X2 hY hX2
  obtain ⟨hD1, hD2⟩ := hD
  have hQ : ∀ p ∈ PI.filter (fun p : ℕ => (p : ℝ) ≤ Y), p.Prime ∧ (p : ℝ) ≤ Y := by
    intro p hp
    rw [Finset.mem_filter] at hp
    exact ⟨hPI p hp.1, hp.2⟩
  have hQ' : ∀ p ∈ PI.filter (fun p : ℕ => (p : ℝ) ≤ Y), p.Prime := fun p hp => (hQ p hp).1
  have hR : ∀ p ∈ (PI.filter (fun p : ℕ => (p : ℝ) ≤ Y)).filter (fun p : ℕ => X2 < (p : ℝ)),
      p.Prime ∧ X2 < (p : ℝ) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    exact ⟨(hQ p hp.1).1, hp.2⟩
  have e1 := hB1 _ hQ
  have e2 := hB2 _ hQ
  have e3 := hB3 _ hR
  have e4 := hD1 _ hQ'
  have e5 := hD2 _ hQ'
  rw [Finset.sum_filter] at e1 e2 e4 e5
  rw [Finset.sum_filter, Finset.sum_filter] at e3
  have hsum : ∑ p ∈ PI, Real.log (p : ℝ) * errGood Y X2 A1 A2 kw T th add p =
      2 * A1 * (∑ p ∈ PI, if (p : ℝ) ≤ Y then Real.log (p : ℝ) / (p : ℝ) else 0) +
      2 * kw * (∑ p ∈ PI, if (p : ℝ) ≤ Y then th p * Real.log (p : ℝ) else 0) +
      2 * (T * ∑ p ∈ PI, if (p : ℝ) ≤ Y then add p * Real.log (p : ℝ) else 0) +
      2 * A2 * (∑ p ∈ PI, if (p : ℝ) ≤ Y then
        (if X2 < (p : ℝ) then Real.log (p : ℝ) / (p : ℝ) ^ 2 else 0) else 0) +
      2 * (∑ p ∈ PI, if (p : ℝ) ≤ Y then Real.log (p : ℝ) else 0) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    unfold errGood
    split_ifs <;> ring
  rw [hsum]
  have h1 := mul_le_mul_of_nonneg_left e1 hA1
  have h2 := mul_le_mul_of_nonneg_left e4 hkw
  have h4 := mul_le_mul_of_nonneg_left e3 hA2
  have h4' : A2 * (2.04 / X2) = 2.04 * A2 / X2 := by ring
  linarith

/- English proof (translation)
Introduce `K _ _ _ S Bad eb heb Y X2 A1 A2 kw T Cth Cadd th add hY hX2 hA1 hA2 hkw hT hth hadd hD errl herr`. Establish `hG : ∀ p : ℕ, 0 ≤ errGood Y X2 A1 A2 kw T th add p`. Introduce `p`. Establish `hp : (0 : ℝ) ≤ p` using `Nat.cast_nonneg p`. Unfold `errGood`.

Apply the tactic sequence `split_ifs <;>`. Combine the linear relations using `[div_nonneg hA1 hp, mul_nonneg hkw (hth p), mul_nonneg hT (hadd p), div_nonneg hA2 (pow_nonneg hp 2)]`. Establish `hX : ∀ p : ℕ, 0 ≤ (if p ∈ Bad then eb p else errGood Y X2 A1 A2 kw T th add p)`. Introduce `p`. Use `split_ifs`.

Conclude with `heb p`. Conclude with `hG p`. Establish `step1 : ∑ w ∈ S, lw w * ((ramw w : ℝ) * errl w) ≤ ∑ w ∈ S, lw w * ((ramw w : ℝ) * (if plc w ∈ Bad then eb (plc w) else errGood Y X2 A1 A2 kw T th add (plc w)))`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `w hw`.

Establish `hl : 0 ≤ lw w`. Unfold `lw`. Conclude with `div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)`. Establish `hr : (0 : ℝ) ≤ (ramw w : ℝ)` using `by exact_mod_cast (le_trans zero_le_one (hR K w).2.1)`. Conclude with `mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (herr w hw) hr) hl`.

Establish `step2` using `hP K S (fun p => if p ∈ Bad then eb p else errGood Y X2 A1 A2 kw T th add p) hX`. Establish `hprime : ∀ p ∈ S.image plc, p.Prime`. Introduce `p hp`. Take `⟨w, -, rfl⟩` from `Finset.mem_image.mp hp`. Conclude with `(hR K w).1`.

Establish `hbadpart : ∑ p ∈ S.image plc, (if p ∈ Bad then Real.log (p : ℝ) * eb p else 0) ≤ ∑ p ∈ Bad, Real.log (p : ℝ) * eb p`. Establish `hsub : (S.image plc).filter (fun p => p ∈ Bad) ⊆ Bad`. Introduce `p hp`. Conclude with `(Finset.mem_filter.mp hp).2`. Establish `h` using `Finset.sum_le_sum_of_subset_of_nonneg (f := fun p : ℕ => Real.log (p : ℝ) * eb p) hsub (fun p _ _ => mul_nonneg (Real.log_natCast_nonneg p) (heb p))`.

Rewrite `h` using `[Finset.sum_filter]`. Then use the resulting hypothesis. Establish `hgoodpart : ∑ p ∈ S.image plc, (if p ∉ Bad then Real.log (p : ℝ) * errGood Y X2 A1 A2 kw T th add p else 0) ≤ 2 * (A1 * Real.log Y + kw * Cth + Cadd + 2.04 * A2 / X2 + Real.log 4 * Y)`. Establish `h` using `hE ((S.image plc).filter (fun p => p ∉ Bad)) (fun p hp => hprime p (Finset.mem_filter.mp hp).1) Y X2 A1 A2 kw T Cth Cadd th add hY hX2 hA1 hA2 hkw hT hth hadd hD`. Rewrite `h` using `[Finset.sum_filter]`. Then use the resulting hypothesis. Establish `hsplit : ∑ p ∈ S.image plc, Real.log (p : ℝ) * (if p ∈ Bad then eb p else errGood Y X2 A1 A2 kw T th add p) = ∑ p ∈ S.image plc, (if p ∈ Bad then Real.log (p : ℝ) * eb p else 0) + ∑ p ∈ S.image plc, (if p ∉ Bad then Real.log (p : ℝ) * errGood Y X2 A1 A2 kw T th add p else 0)`.

Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl (fun p _ => ?_)` and prove the remaining obligations. Apply the tactic sequence `by_cases h : p ∈ Bad <;> simp [h]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem onSumExact_of (hP : PlaceSum) (hR : RamBasic) (hE : ErrSumGoodExact) : OnSumExact := by
  intro K _ _ _ S Bad eb heb Y X2 A1 A2 kw T Cth Cadd th add hY hX2 hA1 hA2 hkw hT hth hadd hD errl herr
  have hG : ∀ p : ℕ, 0 ≤ errGood Y X2 A1 A2 kw T th add p := by
    intro p
    have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    unfold errGood
    split_ifs <;>
      linarith [div_nonneg hA1 hp, mul_nonneg hkw (hth p), mul_nonneg hT (hadd p),
        div_nonneg hA2 (pow_nonneg hp 2)]
  have hX : ∀ p : ℕ, 0 ≤ (if p ∈ Bad then eb p else errGood Y X2 A1 A2 kw T th add p) := by
    intro p
    split_ifs
    · exact heb p
    · exact hG p
  have step1 : ∑ w ∈ S, lw w * ((ramw w : ℝ) * errl w) ≤
      ∑ w ∈ S, lw w * ((ramw w : ℝ) *
        (if plc w ∈ Bad then eb (plc w) else errGood Y X2 A1 A2 kw T th add (plc w))) := by
    apply Finset.sum_le_sum
    intro w hw
    have hl : 0 ≤ lw w := by
      unfold lw
      exact div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)
    have hr : (0 : ℝ) ≤ (ramw w : ℝ) :=
      by exact_mod_cast (le_trans zero_le_one (hR K w).2.1)
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (herr w hw) hr) hl
  have step2 := hP K S (fun p => if p ∈ Bad then eb p else errGood Y X2 A1 A2 kw T th add p) hX
  have hprime : ∀ p ∈ S.image plc, p.Prime := by
    intro p hp
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hp
    exact (hR K w).1
  have hbadpart : ∑ p ∈ S.image plc, (if p ∈ Bad then Real.log (p : ℝ) * eb p else 0) ≤
      ∑ p ∈ Bad, Real.log (p : ℝ) * eb p := by
    have hsub : (S.image plc).filter (fun p => p ∈ Bad) ⊆ Bad := by
      intro p hp
      exact (Finset.mem_filter.mp hp).2
    have h := Finset.sum_le_sum_of_subset_of_nonneg (f := fun p : ℕ => Real.log (p : ℝ) * eb p) hsub
      (fun p _ _ => mul_nonneg (Real.log_natCast_nonneg p) (heb p))
    rwa [Finset.sum_filter] at h
  have hgoodpart : ∑ p ∈ S.image plc,
      (if p ∉ Bad then Real.log (p : ℝ) * errGood Y X2 A1 A2 kw T th add p else 0) ≤
      2 * (A1 * Real.log Y + kw * Cth + Cadd + 2.04 * A2 / X2 + Real.log 4 * Y) := by
    have h := hE ((S.image plc).filter (fun p => p ∉ Bad))
      (fun p hp => hprime p (Finset.mem_filter.mp hp).1) Y X2 A1 A2 kw T Cth Cadd th add
      hY hX2 hA1 hA2 hkw hT hth hadd hD
    rwa [Finset.sum_filter] at h
  have hsplit : ∑ p ∈ S.image plc, Real.log (p : ℝ) *
        (if p ∈ Bad then eb p else errGood Y X2 A1 A2 kw T th add p) =
      ∑ p ∈ S.image plc, (if p ∈ Bad then Real.log (p : ℝ) * eb p else 0) +
      ∑ p ∈ S.image plc,
        (if p ∉ Bad then Real.log (p : ℝ) * errGood Y X2 A1 A2 kw T th add p else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    by_cases h : p ∈ Bad <;> simp [h]
  linarith

/- English proof (translation)
The claim follows from `onSumExact_of place_sum ramified_basic_bound error_sum_good_places_exact`.
-/
theorem local_sum_exact : OnSumExact := onSumExact_of place_sum ramified_basic_bound error_sum_good_places_exact

/- English proof (translation)
Introduce `C L f m b k ws Se Y X2 hC hf hm hb hk hws0 hws hSe hkS hY hlY hYb hX2`. Establish `hl4 : Real.log 4 < 1.3863`. Establish `h` using `Real.log_two_lt_d9`. Establish `h4 : Real.log 4 = 2 * Real.log 2`. Rewrite using `[show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]`.

Evaluate the numerical expressions. Rewrite using `[h4]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hC0 : 0 ≤ C` using `by linarith`. Establish `hf0 : 0 ≤ f` using `by linarith`.

Establish `hm0 : 0 ≤ m` using `by linarith`. Establish `hk0 : 0 < k` using `by linarith`. Establish `hX0 : 0 < X2` using `by linarith`. Establish `hY0 : 0 < Y` using `by linarith`. Establish `hlk : 0 ≤ Real.log k` using `Real.log_nonneg hk`.

Establish `hmb : 0 ≤ m * b` using `mul_nonneg hm0 hb.le`. Establish `hfb : 0 ≤ f * b` using `mul_nonneg hf0 hb.le`. Establish `e1 : C * (Real.log k * m * ws) * Real.log Y ≤ C * (Real.log k * m * ws) * (2 * L)` using `mul_le_mul_of_nonneg_left hlY (mul_nonneg hC0 (mul_nonneg (mul_nonneg hlk hm0) hws0))`. Establish `e2 : C * (f * k * Se) * Real.log Y ≤ C * (f * k * Se) * (2 * L)` using `mul_le_mul_of_nonneg_left hlY (mul_nonneg hC0 (mul_nonneg (mul_nonneg hf0 hk0.le) hSe))`. Establish `e2b : C * f * (k * Se * L) ≤ C * f * (m * b)` using `mul_le_mul_of_nonneg_left hkS (mul_nonneg hC0 hf0)`.

Establish `e3 : C * k * ws * (C / k) = C ^ 2 * ws`. Rewrite using `[show C * k * ws * (C / k) = C ^ 2 * ws * (k / k) by ring, div_self hk0.ne', mul_one]`. Establish `e3b : C ^ 2 * ws ≤ C ^ 2 * (2 * (f * b))` using `mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg C)`. Establish `hfbm : f * b ≤ f * b * m` using `le_mul_of_one_le_right hfb hm`. Establish `e3c : C ^ 2 * (f * b) ≤ C ^ 2 * (f * b * m)` using `mul_le_mul_of_nonneg_left hfbm (sq_nonneg C)`.

Establish `hmbf : m * b ≤ f * (m * b)` using `le_mul_of_one_le_left hmb hf`. Establish `e4 : C * (m * b) ≤ C * (f * (m * b))` using `mul_le_mul_of_nonneg_left hmbf hC0`. Establish `hCws : 0 ≤ C * ws` using `mul_nonneg hC0 hws0`. Establish `hkX : k / X2 ≤ 1` using `(div_le_one hX0).mpr hX2`. Establish `e5 : C * k * ws / X2 ≤ C * ws`.

Combine the equalities or inequalities in the displayed calculation. Establish `e5' : 2.04 * (C * k * ws) / X2 ≤ 2.04 * (C * ws)`. Rewrite using `[mul_div_assoc]`. Conclude with `mul_le_mul_of_nonneg_left e5 (by norm_num)`. Establish `e5b : C * ws ≤ C * (2 * (f * b))` using `mul_le_mul_of_nonneg_left (by linarith) hC0`.

Establish `e5c : C * (f * b) ≤ C * (f * b * m)` using `mul_le_mul_of_nonneg_left hfbm hC0`. Establish `e6 : Real.log 4 * Y ≤ 1.3863 * Y` using `mul_le_mul_of_nonneg_right hl4.le hY0.le`. Establish `hCf : 1 ≤ C * f` using `one_le_mul_of_one_le_of_one_le hC hf`. Establish `e6b : m * b ≤ C * f * (m * b)` using `le_mul_of_one_le_left hmb hCf`. Establish `e7 : 0 ≤ C * f * (m * b)` using `mul_nonneg (mul_nonneg hC0 hf0) hmb`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem lead_exact : LeadExact := by
  intro C L f m b k ws Se Y X2 hC hf hm hb hk hws0 hws hSe hkS hY hlY hYb hX2
  have hl4 : Real.log 4 < 1.3863 := by
    have h := Real.log_two_lt_d9
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [h4]
    linarith
  have hC0 : 0 ≤ C := by linarith
  have hf0 : 0 ≤ f := by linarith
  have hm0 : 0 ≤ m := by linarith
  have hk0 : 0 < k := by linarith
  have hX0 : 0 < X2 := by linarith
  have hY0 : 0 < Y := by linarith
  have hlk : 0 ≤ Real.log k := Real.log_nonneg hk
  have hmb : 0 ≤ m * b := mul_nonneg hm0 hb.le
  have hfb : 0 ≤ f * b := mul_nonneg hf0 hb.le
  have e1 : C * (Real.log k * m * ws) * Real.log Y ≤ C * (Real.log k * m * ws) * (2 * L) :=
    mul_le_mul_of_nonneg_left hlY (mul_nonneg hC0 (mul_nonneg (mul_nonneg hlk hm0) hws0))
  have e2 : C * (f * k * Se) * Real.log Y ≤ C * (f * k * Se) * (2 * L) :=
    mul_le_mul_of_nonneg_left hlY (mul_nonneg hC0 (mul_nonneg (mul_nonneg hf0 hk0.le) hSe))
  have e2b : C * f * (k * Se * L) ≤ C * f * (m * b) :=
    mul_le_mul_of_nonneg_left hkS (mul_nonneg hC0 hf0)
  have e3 : C * k * ws * (C / k) = C ^ 2 * ws := by
    rw [show C * k * ws * (C / k) = C ^ 2 * ws * (k / k) by ring, div_self hk0.ne', mul_one]
  have e3b : C ^ 2 * ws ≤ C ^ 2 * (2 * (f * b)) :=
    mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg C)
  have hfbm : f * b ≤ f * b * m := le_mul_of_one_le_right hfb hm
  have e3c : C ^ 2 * (f * b) ≤ C ^ 2 * (f * b * m) := mul_le_mul_of_nonneg_left hfbm (sq_nonneg C)
  have hmbf : m * b ≤ f * (m * b) := le_mul_of_one_le_left hmb hf
  have e4 : C * (m * b) ≤ C * (f * (m * b)) := mul_le_mul_of_nonneg_left hmbf hC0
  have hCws : 0 ≤ C * ws := mul_nonneg hC0 hws0
  have hkX : k / X2 ≤ 1 := (div_le_one hX0).mpr hX2
  have e5 : C * k * ws / X2 ≤ C * ws := by
    calc C * k * ws / X2 = C * ws * (k / X2) := by ring
      _ ≤ C * ws * 1 := mul_le_mul_of_nonneg_left hkX hCws
      _ = C * ws := mul_one _
  have e5' : 2.04 * (C * k * ws) / X2 ≤ 2.04 * (C * ws) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left e5 (by norm_num)
  have e5b : C * ws ≤ C * (2 * (f * b)) := mul_le_mul_of_nonneg_left (by linarith) hC0
  have e5c : C * (f * b) ≤ C * (f * b * m) := mul_le_mul_of_nonneg_left hfbm hC0
  have e6 : Real.log 4 * Y ≤ 1.3863 * Y := mul_le_mul_of_nonneg_right hl4.le hY0.le
  have hCf : 1 ≤ C * f := one_le_mul_of_one_le_of_one_le hC hf
  have e6b : m * b ≤ C * f * (m * b) := le_mul_of_one_le_left hmb hCf
  have e7 : 0 ≤ C * f * (m * b) := mul_nonneg (mul_nonneg hC0 hf0) hmb
  linarith

/- English proof (translation)
Introduce `C Cb L xe f m b k ws Se Y X2 bad hC hCb hL hxe hf hm hb hk hlk hws0 hws hSe hkS hY hlY hYb hX2 hbad`. Establish `hlead` using `lead_exact C L f m b k ws Se Y X2 hC hf hm hb hk hws0 hws hSe hkS hY hlY hYb hX2`. Establish `hC0 : 0 ≤ C` using `by linarith`. Establish `hL0 : 0 ≤ L` using `by linarith`. Establish `hm0 : 0 ≤ m` using `by linarith`.

Establish `hf0 : 0 ≤ f` using `by linarith`. Establish `hZ : 0 ≤ f * m * b` using `mul_nonneg (mul_nonneg hf0 hm0) hb.le`. Establish `hxe1 : 1 ≤ xe` using `by linarith`. Establish `hxL : 1 ≤ xe * L` using `one_le_mul_of_one_le_of_one_le hxe1 hL`. Establish `a1 : Real.log k * (C * L * (m * ws)) ≤ L * (C * L * (m * ws))` using `mul_le_mul_of_nonneg_right hlk (mul_nonneg (mul_nonneg hC0 hL0) (mul_nonneg hm0 hws0))`.

Establish `a2 : C * L * L * (m * ws) ≤ C * L * L * (m * (2 * f * b))` using `mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hws hm0) (mul_nonneg (mul_nonneg hC0 hL0) hL0)`. Establish `a3 : C * (f * m * b) * (L * L) ≤ C * (f * m * b) * (xe * L)` using `mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hxe hL0) (mul_nonneg hC0 hZ)`. Establish `hq : 0 ≤ 4 * C ^ 2 + 17 * C` using `add_nonneg (by positivity) (by linarith)`. Establish `a5 : (4 * C ^ 2 + 17 * C) * (f * m * b) ≤ (4 * C ^ 2 + 17 * C) * (f * m * b) * (xe * L)` using `le_mul_of_one_le_right (mul_nonneg hq hZ) hxL`. Establish `a6 : Cb * (f * m * b * L) ≤ Cb * (f * m * b * L) * xe` using `le_mul_of_one_le_right (mul_nonneg hCb (mul_nonneg hZ hL0)) hxe1`.

Establish `a7 : 12 * (f * m * b) ≤ 12 * (f * m * b) * (xe * L)` using `le_mul_of_one_le_right (by linarith) hxL`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem absorb_local_conditions_exact : AbsorbOnExact := by
  intro C Cb L xe f m b k ws Se Y X2 bad hC hCb hL hxe hf hm hb hk hlk hws0 hws hSe hkS hY hlY hYb hX2 hbad
  have hlead := lead_exact C L f m b k ws Se Y X2 hC hf hm hb hk hws0 hws hSe hkS hY hlY hYb hX2
  have hC0 : 0 ≤ C := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hm0 : 0 ≤ m := by linarith
  have hf0 : 0 ≤ f := by linarith
  have hZ : 0 ≤ f * m * b := mul_nonneg (mul_nonneg hf0 hm0) hb.le
  have hxe1 : 1 ≤ xe := by linarith
  have hxL : 1 ≤ xe * L := one_le_mul_of_one_le_of_one_le hxe1 hL
  have a1 : Real.log k * (C * L * (m * ws)) ≤ L * (C * L * (m * ws)) :=
    mul_le_mul_of_nonneg_right hlk (mul_nonneg (mul_nonneg hC0 hL0) (mul_nonneg hm0 hws0))
  have a2 : C * L * L * (m * ws) ≤ C * L * L * (m * (2 * f * b)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hws hm0) (mul_nonneg (mul_nonneg hC0 hL0) hL0)
  have a3 : C * (f * m * b) * (L * L) ≤ C * (f * m * b) * (xe * L) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hxe hL0) (mul_nonneg hC0 hZ)
  have hq : 0 ≤ 4 * C ^ 2 + 17 * C := add_nonneg (by positivity) (by linarith)
  have a5 : (4 * C ^ 2 + 17 * C) * (f * m * b) ≤ (4 * C ^ 2 + 17 * C) * (f * m * b) * (xe * L) :=
    le_mul_of_one_le_right (mul_nonneg hq hZ) hxL
  have a6 : Cb * (f * m * b * L) ≤ Cb * (f * m * b * L) * xe :=
    le_mul_of_one_le_right (mul_nonneg hCb (mul_nonneg hZ hL0)) hxe1
  have a7 : 12 * (f * m * b) ≤ 12 * (f * m * b) * (xe * L) :=
    le_mul_of_one_le_right (by linarith) hxL
  linarith

end Formalism.EigenvalueLevelCeiling
