import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SizeAbsorption.PrimeWeightedRemainderBound
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PrimeLogOverP
import Development.AutomorphicArithmetic.OrbitLabellings.SumLogMulMaxZeroLeOfOddAddOrderOf

noncomputable section

namespace UpperTheory.G2

open Formalism.BasicNotions Formalism.MainNotions.G PI.SzEatI.W

/- English proof (translation)
Introduce `K ce eps Ct CGam Cc CT2 PK`. Take `⟨x0, hx0⟩` from `hA K eps`. Take `⟨C, hC, x1, hx1⟩` from `UpperTheory.sum_log_mul_max_zero_le_of_odd_addOrderOf ce eps Ct CGam Cc CT2 PK`. Establish `hc1 : 0 ≤ c1 ce` using `by unfold c1; positivity`. Use `⟨c1 ce + 1 + C, by positivity, max x0 x1, ?_⟩` and prove the remaining obligations.

Introduce `D L P hU hx hSz j hj S hS`. Take `⟨hbb, hR0, hYR, hY1, hlog⟩` from `hx0 D L hU.1 (le_trans (le_max_left _ _) hx) hSz`. Establish `hX` using `hx1 D L P hU (le_trans (le_max_right _ _) hx) hSz j hj (S.filter fun p => IsCs D p) (by`. Introduce `p hp`. Take `⟨hpS, hcs⟩` from `Finset.mem_filter.1 hp`.

Conclude with `⟨(hS p hpS).1, hcs.1, hcs.2.1, (hS p hpS).2.2.2⟩)`. Establish `hXs : ∑ p ∈ S, Real.log p * EatX L ce j p ≤ C * (D.R.f : ℝ) * L.sc.b * Real.log (L.sc.X'' D.R.n)`. Use `le_trans ?_ hX` and prove the remaining obligations. Rewrite using `[Finset.sum_filter]`. Use `Finset.sum_le_sum fun p _ => ?_` and prove the remaining obligations.

Unfold `EatX`. Use `split_ifs`. Conclude with `mul_le_mul_of_nonneg_left (le_max_right _ _) (Real.log_natCast_nonneg p)`. Simplify using the standard rewrite rules. Use `set Y := L.sc.X'' D.R.n with hYdef`.

Use `set f : ℝ := (D.R.f : ℝ) with hfdef`. Establish `hf : 0 ≤ f` using `Nat.cast_nonneg _`. Establish `hb : 0 ≤ L.sc.b` using `(Real.exp_pos _).le`. Establish `hpt : ∀ p ∈ S, Real.log p * (EatI L K ce j p - max 0 ((∑ z ∈ kindA D p, FOrb D j p z) / (nP D p : ℝ))) ≤ c1 ce * f * L.sc.b * (Real.log p / p) + f * Rt L K + Real.log p * EatX L ce j p`. Introduce `p hp`.

Take `⟨hpr, -, -, hpY⟩` from `hS p hp`. Establish `h` using `prime_weighted_remainder_bound K ce D L hSz hbb j hj p hpr hpY`. Unfold `rest at h`. Rewrite `h` using `[mul_sub]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hM : ∑ p ∈ S, Real.log (p : ℝ) / (p : ℝ) ≤ Real.log Y` using `sum_log_p_over_p Y hY1 S (fun p hp => ⟨(hS p hp).1, (hS p hp).2.2.2⟩)`. Establish `hcard : (S.card : ℝ) ≤ Y` using `card_le_of_le S Y (by linarith) (fun p hp => ⟨(hS p hp).1.one_lt.le, (hS p hp).2.2.2⟩)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]`. Use `_ ≤ c1 ce * f * L.sc.b * Real.log Y + Y * (f * Rt L K) + C * f * L.sc.b * Real.log Y := by`.

Establish `h0 : 0 ≤ c1 ce * f * L.sc.b` using `mul_nonneg (mul_nonneg hc1 hf) hb`. Conclude with `add_le_add (add_le_add (mul_le_mul_of_nonneg_left hM h0) (mul_le_mul_of_nonneg_right hcard (mul_nonneg hf hR0))) hXs`. Use `_ = c1 ce * f * L.sc.b * Real.log Y + f * (Y * Rt L K) + C * f * L.sc.b * Real.log Y := by ring`. Use `_ ≤ c1 ce * f * L.sc.b * Real.log Y + f * (L.sc.b * Real.log Y) + C * f * L.sc.b * Real.log Y := by`. Use `add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ hf)) le_rfl` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Use `_ = (c1 ce + 1 + C) * f * L.sc.b * Real.log Y := by ring`.
-/
theorem szEatI_of_stepA (hA : StepA) : PI.SzEatI.SzEatI := by
  classical
  intro K ce eps Ct CGam Cc CT2 PK
  obtain ⟨x0, hx0⟩ := hA K eps
  obtain ⟨C, hC, x1, hx1⟩ := UpperTheory.sum_log_mul_max_zero_le_of_odd_addOrderOf ce eps Ct CGam Cc CT2 PK
  have hc1 : 0 ≤ c1 ce := by unfold c1; positivity
  refine ⟨c1 ce + 1 + C, by positivity, max x0 x1, ?_⟩
  intro D L P hU hx hSz j hj S hS
  obtain ⟨hbb, hR0, hYR, hY1, hlog⟩ := hx0 D L hU.1 (le_trans (le_max_left _ _) hx) hSz
  have hX := hx1 D L P hU (le_trans (le_max_right _ _) hx) hSz j hj (S.filter fun p => IsCs D p) (by
    intro p hp
    obtain ⟨hpS, hcs⟩ := Finset.mem_filter.1 hp
    exact ⟨(hS p hpS).1, hcs.1, hcs.2.1, (hS p hpS).2.2.2⟩)
  have hXs : ∑ p ∈ S, Real.log p * EatX L ce j p ≤
      C * (D.R.f : ℝ) * L.sc.b * Real.log (L.sc.X'' D.R.n) := by
    refine le_trans ?_ hX
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum fun p _ => ?_
    unfold EatX
    split_ifs
    · exact mul_le_mul_of_nonneg_left (le_max_right _ _) (Real.log_natCast_nonneg p)
    · simp
  set Y := L.sc.X'' D.R.n with hYdef
  set f : ℝ := (D.R.f : ℝ) with hfdef
  have hf : 0 ≤ f := Nat.cast_nonneg _
  have hb : 0 ≤ L.sc.b := (Real.exp_pos _).le
  have hpt : ∀ p ∈ S, Real.log p * (EatI L K ce j p -
      max 0 ((∑ z ∈ kindA D p, FOrb D j p z) / (nP D p : ℝ))) ≤
      c1 ce * f * L.sc.b * (Real.log p / p) + f * Rt L K + Real.log p * EatX L ce j p := by
    intro p hp
    obtain ⟨hpr, -, -, hpY⟩ := hS p hp
    have h := prime_weighted_remainder_bound K ce D L hSz hbb j hj p hpr hpY
    unfold rest at h
    rw [mul_sub] at h
    linarith
  have hM : ∑ p ∈ S, Real.log (p : ℝ) / (p : ℝ) ≤ Real.log Y :=
    sum_log_p_over_p Y hY1 S (fun p hp => ⟨(hS p hp).1, (hS p hp).2.2.2⟩)
  have hcard : (S.card : ℝ) ≤ Y :=
    card_le_of_le S Y (by linarith) (fun p hp => ⟨(hS p hp).1.one_lt.le, (hS p hp).2.2.2⟩)
  calc ∑ p ∈ S, Real.log p * (EatI L K ce j p -
        max 0 ((∑ z ∈ kindA D p, FOrb D j p z) / (nP D p : ℝ)))
      ≤ ∑ p ∈ S, (c1 ce * f * L.sc.b * (Real.log p / p) + f * Rt L K + Real.log p * EatX L ce j p) :=
        Finset.sum_le_sum hpt
    _ = c1 ce * f * L.sc.b * (∑ p ∈ S, Real.log (p : ℝ) / (p : ℝ)) + (S.card : ℝ) * (f * Rt L K) +
          ∑ p ∈ S, Real.log p * EatX L ce j p := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    _ ≤ c1 ce * f * L.sc.b * Real.log Y + Y * (f * Rt L K) + C * f * L.sc.b * Real.log Y := by
        have h0 : 0 ≤ c1 ce * f * L.sc.b := mul_nonneg (mul_nonneg hc1 hf) hb
        exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hM h0)
          (mul_le_mul_of_nonneg_right hcard (mul_nonneg hf hR0))) hXs
    _ = c1 ce * f * L.sc.b * Real.log Y + f * (Y * Rt L K) + C * f * L.sc.b * Real.log Y := by ring
    _ ≤ c1 ce * f * L.sc.b * Real.log Y + f * (L.sc.b * Real.log Y) + C * f * L.sc.b * Real.log Y := by
        refine add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ hf)) le_rfl
        calc Y * Rt L K ≤ L.sc.b := hYR
          _ = L.sc.b * 1 := by ring
          _ ≤ L.sc.b * Real.log Y := mul_le_mul_of_nonneg_left hlog hb
    _ = (c1 ce + 1 + C) * f * L.sc.b * Real.log Y := by ring

end UpperTheory.G2
