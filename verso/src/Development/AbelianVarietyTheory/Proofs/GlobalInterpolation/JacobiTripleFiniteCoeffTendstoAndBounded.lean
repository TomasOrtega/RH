import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MultipliableTpFactor

open Complex
open scoped Real

noncomputable section

namespace GlobalTheory.JacobiTriple

/- English proof (translation)
Introduce `t ht`. Take `⟨hlim, hP0, hne⟩` from `qPoch_tendsto t ht`. Use `⟨fun j => ?_, ?_⟩` and prove the remaining obligations. Establish `ha : Filter.Tendsto (fun n : ℕ => ((n : ℤ) + j).toNat) Filter.atTop Filter.atTop`. Use `Filter.tendsto_atTop_mono (f := fun n : ℕ => n - j.natAbs) (fun n => by omega) ?_` and prove the remaining obligations.

Conclude with `Filter.tendsto_sub_atTop_nat _`. Establish `hb : Filter.Tendsto (fun n : ℕ => 2 * n - ((n : ℤ) + j).toNat) Filter.atTop Filter.atTop`. Use `Filter.tendsto_atTop_mono (f := fun n : ℕ => n - j.natAbs) (fun n => by omega) ?_` and prove the remaining obligations. Conclude with `Filter.tendsto_sub_atTop_nat _`. Establish `h2 : Filter.Tendsto (fun n : ℕ => 2 * n) Filter.atTop Filter.atTop` using `Filter.tendsto_atTop_mono (fun n => by show n ≤ 2 * n; omega) Filter.tendsto_id`.

Establish `hmain : Filter.Tendsto (fun n : ℕ => qPoch t (2 * n) / (qPoch t ((n : ℤ) + j).toNat * qPoch t (2 * n - ((n : ℤ) + j).toNat))) Filter.atTop (nhds (qPochInf t / (qPochInf t * qPochInf t)))` using `(hlim.comp h2).div ((hlim.comp ha).mul (hlim.comp hb)) (mul_ne_zero hP0 hP0)`. Establish `hval : qPochInf t / (qPochInf t * qPochInf t) = (qPochInf t)⁻¹`. Clear the denominators using the available nonvanishing facts. Rewrite `hmain` using `[hval]`. Use `hmain.congr' ?_` and prove the remaining obligations.

Use `filter_upwards [Filter.eventually_ge_atTop j.natAbs] with n hn`. Simplify using `[finCoeff, qBinom, hn]`. Take `⟨B1, hB1⟩` from `isBounded_iff_forall_norm_le.mp (Metric.isBounded_range_of_tendsto _ hlim)`. Take `⟨B2, hB2⟩` from `isBounded_iff_forall_norm_le.mp (Metric.isBounded_range_of_tendsto _ (hlim.inv₀ hP0))`. Use `set B := max B1 B2`.

Establish `b1 : ∀ m, ‖qPoch t m‖ ≤ B` using `fun m => (hB1 _ ⟨m, rfl⟩).trans (le_max_left _ _)`. Establish `b2 : ∀ m, ‖(qPoch t m)⁻¹‖ ≤ B` using `fun m => (hB2 _ ⟨m, rfl⟩).trans (le_max_right _ _)`. Establish `hB0 : 0 ≤ B` using `(norm_nonneg _).trans (b1 0)`. Use `⟨max (B ^ 3) 0, fun n j => ?_⟩` and prove the remaining obligations. Unfold `finCoeff`.

Use `split_ifs`. Unfold `qBinom`. Rewrite using `[div_eq_mul_inv, mul_inv, norm_mul, norm_mul]`. Use `le_max_of_le_left ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Conclude with `b1 _`. Conclude with `b2 _`. Conclude with `b2 _`. Use `_ = B ^ 3 := by ring`. Simplify using the standard rewrite rules.
-/
theorem finCoeff_tendsto_and_bounded :
    ∀ t : ℂ, ‖t‖ < 1 → (∀ j : ℤ, Filter.Tendsto (fun n : ℕ => GlobalTheory.JacobiTriple.finCoeff t n j)
      Filter.atTop (nhds (GlobalTheory.JacobiTriple.qPochInf t)⁻¹)) ∧
      ∃ C : ℝ, ∀ (n : ℕ) (j : ℤ), ‖GlobalTheory.JacobiTriple.finCoeff t n j‖ ≤ C := by
  intro t ht
  obtain ⟨hlim, hP0, hne⟩ := qPoch_tendsto t ht
  refine ⟨fun j => ?_, ?_⟩
  · have ha : Filter.Tendsto (fun n : ℕ => ((n : ℤ) + j).toNat) Filter.atTop Filter.atTop := by
      refine Filter.tendsto_atTop_mono (f := fun n : ℕ => n - j.natAbs) (fun n => by omega) ?_
      exact Filter.tendsto_sub_atTop_nat _
    have hb : Filter.Tendsto (fun n : ℕ => 2 * n - ((n : ℤ) + j).toNat) Filter.atTop
        Filter.atTop := by
      refine Filter.tendsto_atTop_mono (f := fun n : ℕ => n - j.natAbs) (fun n => by omega) ?_
      exact Filter.tendsto_sub_atTop_nat _
    have h2 : Filter.Tendsto (fun n : ℕ => 2 * n) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_mono (fun n => by show n ≤ 2 * n; omega) Filter.tendsto_id
    have hmain : Filter.Tendsto (fun n : ℕ => qPoch t (2 * n) /
        (qPoch t ((n : ℤ) + j).toNat * qPoch t (2 * n - ((n : ℤ) + j).toNat))) Filter.atTop
        (nhds (qPochInf t / (qPochInf t * qPochInf t))) :=
      (hlim.comp h2).div ((hlim.comp ha).mul (hlim.comp hb)) (mul_ne_zero hP0 hP0)
    have hval : qPochInf t / (qPochInf t * qPochInf t) = (qPochInf t)⁻¹ := by
      field_simp
    rw [hval] at hmain
    refine hmain.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop j.natAbs] with n hn
    simp [finCoeff, qBinom, hn]
  · obtain ⟨B1, hB1⟩ := isBounded_iff_forall_norm_le.mp (Metric.isBounded_range_of_tendsto _ hlim)
    obtain ⟨B2, hB2⟩ := isBounded_iff_forall_norm_le.mp
      (Metric.isBounded_range_of_tendsto _ (hlim.inv₀ hP0))
    set B := max B1 B2
    have b1 : ∀ m, ‖qPoch t m‖ ≤ B := fun m => (hB1 _ ⟨m, rfl⟩).trans (le_max_left _ _)
    have b2 : ∀ m, ‖(qPoch t m)⁻¹‖ ≤ B := fun m => (hB2 _ ⟨m, rfl⟩).trans (le_max_right _ _)
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (b1 0)
    refine ⟨max (B ^ 3) 0, fun n j => ?_⟩
    unfold finCoeff
    split_ifs
    · unfold qBinom
      rw [div_eq_mul_inv, mul_inv, norm_mul, norm_mul]
      refine le_max_of_le_left ?_
      calc ‖qPoch t (2 * n)‖ * (‖(qPoch t ((n : ℤ) + j).toNat)⁻¹‖ *
            ‖(qPoch t (2 * n - ((n : ℤ) + j).toNat))⁻¹‖) ≤ B * (B * B) := by
            gcongr
            · exact b1 _
            · exact b2 _
            · exact b2 _
        _ = B ^ 3 := by ring
    · simp

end GlobalTheory.JacobiTriple
