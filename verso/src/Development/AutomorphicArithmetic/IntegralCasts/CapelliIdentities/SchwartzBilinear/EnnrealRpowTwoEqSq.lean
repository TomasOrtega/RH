import Mathlib

namespace UpperTheory.Reformulated.B.P6.r96a

open scoped MeasureTheory ENNReal LE HPow NPow Monoid Semiring CommSemiring HMul Distrib OfNat

/- English proof (translation)
Chain the equalities or inequalities of the calculation.
-/
theorem ennreal_sqrt_mul_sqrt (x : ENNReal) : x ^ (1/2 : ℝ) * x ^ (1/2 : ℝ) = x := by
  calc x ^ (1/2 : ℝ) * x ^ (1/2 : ℝ) = (x ^ (1/2 : ℝ)) ^ (2:ℕ) := (sq _).symm
    _ = (x ^ (1/2 : ℝ)) ^ ((2:ℕ):ℝ) := (ENNReal.rpow_natCast _ _).symm
    _ = x := by rw [← ENNReal.rpow_mul]; norm_num

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem ennreal_sqrt_sq (x : ENNReal) : (x ^ (1/2 : ℝ)) ^ 2 = x := by
  rw [sq]; exact ennreal_sqrt_mul_sqrt x

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Evaluate the numerical expressions.
-/
theorem ennreal_rpow_two_eq_sq (x : ENNReal) : x ^ (2:ℝ) = x ^ 2 := by
  rw [← ENNReal.rpow_natCast]; norm_num

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem GlobalTheory.CompanionTheory.Conc.WeightedCauchySchwarzLintegral.sq_lintegral_mul_le.{u_1} :
    ∀ {X : Type u_1} [inst_h0 : MeasurableSpace X] (ν : MeasureTheory.Measure X) {a b : X → ENNReal}, Measurable a → Measurable b → HPow.hPow (β := ℕ) (∫⁻ (w : X), a w * b w ∂ν) (OfNat.ofNat (nat_lit 2)) ≤ (∫⁻ (w : X), a w ∂ν) * ∫⁻ (w : X), a w * HPow.hPow (β := ℕ) (b w) (OfNat.ofNat (nat_lit 2)) ∂ν := by
  intro X _ ν a b ha hb
  have hf : AEMeasurable (fun w => a w ^ (1/2:ℝ)) ν := (ha.pow_const _).aemeasurable
  have hg : AEMeasurable (fun w => a w ^ (1/2:ℝ) * b w) ν := ((ha.pow_const _).mul hb).aemeasurable
  have key := ENNReal.lintegral_mul_le_Lp_mul_Lq ν (p := 2) (q := 2)
    Real.HolderConjugate.two_two hf hg
  have key2 : ∫⁻ w, a w * b w ∂ν ≤
      (∫⁻ w, a w ∂ν) ^ (1/(2:ℝ)) * (∫⁻ w, a w * b w ^ 2 ∂ν) ^ (1/(2:ℝ)) := by
    have h1 : ∫⁻ w, a w * b w ∂ν
        = ∫⁻ w, ((fun w => a w ^ (1/2:ℝ)) * (fun w => a w ^ (1/2:ℝ) * b w)) w ∂ν := by
      apply MeasureTheory.lintegral_congr
      intro w
      simp only [Pi.mul_apply]
      rw [← mul_assoc, ennreal_sqrt_mul_sqrt]
    have h2 : ∫⁻ w, a w ∂ν = ∫⁻ w, (a w ^ (1/2:ℝ)) ^ (2:ℝ) ∂ν := by
      apply MeasureTheory.lintegral_congr
      intro w
      rw [ennreal_rpow_two_eq_sq, ennreal_sqrt_sq]
    have h3 : ∫⁻ w, a w * b w ^ 2 ∂ν = ∫⁻ w, (a w ^ (1/2:ℝ) * b w) ^ (2:ℝ) ∂ν := by
      apply MeasureTheory.lintegral_congr
      intro w
      rw [ennreal_rpow_two_eq_sq, mul_pow, ennreal_sqrt_sq]
    rw [h1, h2, h3]
    exact key
  calc (∫⁻ w, a w * b w ∂ν) ^ 2
      ≤ ((∫⁻ w, a w ∂ν) ^ (1/(2:ℝ)) * (∫⁻ w, a w * b w ^ 2 ∂ν) ^ (1/(2:ℝ))) ^ 2 := by
        gcongr
    _ = (∫⁻ w, a w ∂ν) * ∫⁻ w, a w * b w ^ 2 ∂ν := by
        rw [mul_pow, ennreal_sqrt_sq, ennreal_sqrt_sq]

end UpperTheory.Reformulated.B.P6.r96a
