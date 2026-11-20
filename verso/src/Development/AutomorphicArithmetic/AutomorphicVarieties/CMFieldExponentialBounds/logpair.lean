import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.StmtFields

open NumberField Formalism.HC UpperTheory.Top UpperTheory.V

/- English proof (translation)
Introduce `eps heps`. Establish `hs : 0 < eps / 20` using `by positivity`. Establish `h1` using `(isLittleO_log_rpow_rpow_atTop 2 hs).bound (by norm_num : (0:ℝ) < 1 / 2)`. Establish `h2` using `(tendsto_rpow_atTop hs).eventually_ge_atTop 2`. Take `⟨Y0, hY0⟩` from `Filter.eventually_atTop.1 ((h1.and h2).and (Filter.eventually_gt_atTop 0))`.

Use `⟨Y0, fun Y hY q d hw => ?_⟩` and prove the remaining obligations. Take `⟨⟨hl, hg⟩, hpos⟩` from `hY0 Y hY`. Establish `hq : (0:ℝ) < q` using `by exact_mod_cast hw.q_prime.pos`. Establish `hd : (0:ℝ) < d` using `by exact_mod_cast hw.d_prime.pos`. Rewrite using `[Real.log_mul hq.ne' hd.ne']`.

Establish `hA : 0 < Y ^ (eps / 5)` using `Real.rpow_pos_of_pos hpos _`. Establish `hB : 0 < Y ^ (eps / 20)` using `Real.rpow_pos_of_pos hpos _`. Rewrite `hl` using `[Real.rpow_two, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), abs_of_pos hB]`. Establish `hsplit : Y ^ (eps / 4) = Y ^ (eps / 5) * Y ^ (eps / 20)`. Rewrite using `[← Real.rpow_add hpos]`.

Put the polynomial expressions in normal form. Rewrite using `[hsplit]`. Establish `hq'` using `hw.q_up`. Establish `hd'` using `hw.d_up`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hl hA.le, mul_le_mul_of_nonneg_left hg hA.le]`.
-/
theorem UpperTheory.V.log_mul_le_rpow_of_winPair :
    ∀ eps : ℝ, 0 < eps → ∃ Y0 : ℝ, ∀ Y ≥ Y0, ∀ q d : ℕ, WinPair eps Y q d → Real.log ((q : ℝ) * d) ≤ Y ^ (eps / 4) := by
  intro eps heps
  have hs : 0 < eps / 20 := by positivity
  have h1 := (isLittleO_log_rpow_rpow_atTop 2 hs).bound (by norm_num : (0:ℝ) < 1 / 2)
  have h2 := (tendsto_rpow_atTop hs).eventually_ge_atTop 2
  obtain ⟨Y0, hY0⟩ := Filter.eventually_atTop.1 ((h1.and h2).and (Filter.eventually_gt_atTop 0))
  refine ⟨Y0, fun Y hY q d hw => ?_⟩
  obtain ⟨⟨hl, hg⟩, hpos⟩ := hY0 Y hY
  have hq : (0:ℝ) < q := by exact_mod_cast hw.q_prime.pos
  have hd : (0:ℝ) < d := by exact_mod_cast hw.d_prime.pos
  rw [Real.log_mul hq.ne' hd.ne']
  have hA : 0 < Y ^ (eps / 5) := Real.rpow_pos_of_pos hpos _
  have hB : 0 < Y ^ (eps / 20) := Real.rpow_pos_of_pos hpos _
  rw [Real.rpow_two, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
    abs_of_pos hB] at hl
  have hsplit : Y ^ (eps / 4) = Y ^ (eps / 5) * Y ^ (eps / 20) := by
    rw [← Real.rpow_add hpos]
    ring_nf
  rw [hsplit]
  have hq' := hw.q_up
  have hd' := hw.d_up
  nlinarith [mul_le_mul_of_nonneg_left hl hA.le, mul_le_mul_of_nonneg_left hg hA.le]
