import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.PMinorAff

noncomputable section

open scoped BigOperators
open Classical

namespace PI.EntAtD.W

open PI.EntAtD

/- English proof (translation)
Establish `hp1 : (1 : ℝ) ≤ p` using `by exact_mod_cast (Fact.out : p.Prime).one_lt.le`. Establish `hp0 : (0 : ℝ) < p` using `by linarith`. Establish `hq0 : (0 : ℝ) ≤ (p : ℝ) ^ ((1 : ℝ) / 2)` using `Real.rpow_nonneg hp0.le _`. Establish `hq1 : (1 : ℝ) ≤ (p : ℝ) ^ ((1 : ℝ) / 2)` using `Real.one_le_rpow hp1 (by norm_num)`. Establish `hA : ‖((A : ℤ) : ℂ_[p])‖ ≤ 1` using `IsUltrametricDist.norm_intCast_le_one ℂ_[p] A`.

Establish `h2 : ∏ t : H, ‖(-(S * ut t)) ^ n t‖ ≤ (p : ℝ) ^ ((∑ t : H, (c t : ℝ)) / 2)`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.prod_le_prod (fun t _ => norm_nonneg _)` to reduce the goal to its premises. Introduce `t _`. Rewrite using `[norm_pow, norm_neg, norm_mul]`.

Combine the equalities or inequalities in the displayed calculation. Apply `pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _))` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Use `_ ≤ _ := pow_le_pow_right₀ hq1 (hn t)`. Use `_ = _ := by`.

Rewrite using `[Finset.sum_div, Real.rpow_sum_of_pos hp0]`. Use `Finset.prod_congr rfl (fun t _ => ?_)` and prove the remaining obligations. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul hp0.le]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[norm_mul, norm_mul, norm_prod]`. Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul (mul_le_mul hX h2 (Finset.prod_nonneg fun _ _ => norm_nonneg _) zero_le_one) hA (norm_nonneg _)` to reduce the goal to its premises. Conclude with `mul_nonneg zero_le_one (Real.rpow_nonneg hp0.le _)`. Use `_ = _ := by ring`.
-/
theorem coreTerm_le {H : Type} [Fintype H] (p : ℕ) [Fact p.Prime] (S : ℂ_[p]) (ut : H → ℂ_[p])
    (hS : ‖S‖ ≤ (p : ℝ) ^ ((1 : ℝ) / 2)) (hut : ∀ t, ‖ut t‖ ≤ 1) (X : ℂ_[p]) (hX : ‖X‖ ≤ 1) (A : ℤ)
    (n c : H → ℕ) (hn : ∀ t, n t ≤ c t) :
    ‖X * (∏ t : H, (-(S * ut t)) ^ n t) * ((A : ℤ) : ℂ_[p])‖ ≤
      (p : ℝ) ^ ((∑ t : H, (c t : ℝ)) / 2) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hp0 : (0 : ℝ) < p := by linarith
  have hq0 : (0 : ℝ) ≤ (p : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hp0.le _
  have hq1 : (1 : ℝ) ≤ (p : ℝ) ^ ((1 : ℝ) / 2) := Real.one_le_rpow hp1 (by norm_num)
  have hA : ‖((A : ℤ) : ℂ_[p])‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one ℂ_[p] A
  have h2 : ∏ t : H, ‖(-(S * ut t)) ^ n t‖ ≤ (p : ℝ) ^ ((∑ t : H, (c t : ℝ)) / 2) := by
    calc ∏ t : H, ‖(-(S * ut t)) ^ n t‖ ≤ ∏ t : H, ((p : ℝ) ^ ((1 : ℝ) / 2)) ^ c t := by
          apply Finset.prod_le_prod (fun t _ => norm_nonneg _)
          intro t _
          rw [norm_pow, norm_neg, norm_mul]
          calc (‖S‖ * ‖ut t‖) ^ n t ≤ ((p : ℝ) ^ ((1 : ℝ) / 2)) ^ n t := by
                apply pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
                calc ‖S‖ * ‖ut t‖ ≤ (p : ℝ) ^ ((1 : ℝ) / 2) * 1 :=
                      mul_le_mul hS (hut t) (norm_nonneg _) hq0
                  _ = _ := mul_one _
            _ ≤ _ := pow_le_pow_right₀ hq1 (hn t)
      _ = _ := by
          rw [Finset.sum_div, Real.rpow_sum_of_pos hp0]
          refine Finset.prod_congr rfl (fun t _ => ?_)
          rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
          congr 1
          ring
  rw [norm_mul, norm_mul, norm_prod]
  calc ‖X‖ * (∏ t : H, ‖(-(S * ut t)) ^ n t‖) * ‖((A : ℤ) : ℂ_[p])‖
      ≤ 1 * (p : ℝ) ^ ((∑ t : H, (c t : ℝ)) / 2) * 1 := by
        apply mul_le_mul (mul_le_mul hX h2 (Finset.prod_nonneg fun _ _ => norm_nonneg _) zero_le_one)
          hA (norm_nonneg _)
        exact mul_nonneg zero_le_one (Real.rpow_nonneg hp0.le _)
    _ = _ := by ring

/- English proof (translation)
Introduce `H _ _ N0 N1 p _ nu Th hTh I m`. Take `⟨S, hS, ut, hut, sg, hsg, rfl⟩` from `hTh`. Rewrite using `[hE H N0 N1 p S ut sg (Gxz N0 N1 nu I) m, neg_neg]`. Establish `hp0 : (0 : ℝ) < p` using `by exact_mod_cast (Fact.out : p.Prime).pos`. Establish `hB0 : (0 : ℝ) ≤ (p : ℝ) ^ ((∑ t : H, (cPr (nu (false, t)) (nu (true, t)) : ℝ)) / 2)` using `Real.rpow_nonneg hp0.le _`.

Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hB0 (fun κ2 _ => ?_)` and prove the remaining obligations. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hB0 (fun n _ => ?_)` and prove the remaining obligations. Distinguish the cases in `hn : ∃ t, cPr (nu (false, t)) (nu (true, t)) < n t`. Take `⟨t, ht⟩` from `hn`. Rewrite using `[hV H N0 N1 nu I m κ2 n t ht]`.

Simplify using `using hB0`. Simplify using `only [not_exists, not_lt] at hn`. Conclude with `coreTerm_le p S ut hS hut _ (hsg κ2) _ n (fun t => cPr (nu (false, t)) (nu (true, t))) hn`.
-/
theorem core_of (hE : PExpand) (hV : PVanish) : CoreBound := by
  intro H _ _ N0 N1 p _ nu Th hTh I m
  obtain ⟨S, hS, ut, hut, sg, hsg, rfl⟩ := hTh
  rw [hE H N0 N1 p S ut sg (Gxz N0 N1 nu I) m, neg_neg]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hB0 : (0 : ℝ) ≤ (p : ℝ) ^ ((∑ t : H, (cPr (nu (false, t)) (nu (true, t)) : ℝ)) / 2) :=
    Real.rpow_nonneg hp0.le _
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hB0 (fun κ2 _ => ?_)
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hB0 (fun n _ => ?_)
  by_cases hn : ∃ t, cPr (nu (false, t)) (nu (true, t)) < n t
  · obtain ⟨t, ht⟩ := hn
    rw [hV H N0 N1 nu I m κ2 n t ht]
    simpa using hB0
  · simp only [not_exists, not_lt] at hn
    exact coreTerm_le p S ut hS hut _ (hsg κ2) _ n (fun t => cPr (nu (false, t)) (nu (true, t))) hn

end PI.EntAtD.W
