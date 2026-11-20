import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsElem
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Elementary
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open Finset

noncomputable section

/- English proof (translation)
Introduce `f r a c B₀ hf hr ha hB Q hT s e he p hp hpB`. Use `set Y : ℝ := ((f * (r * a) + 1 : ℕ) : ℝ) * |(fibreDegree f r a c : ℝ)| with hY`. Use `set X : ℝ := (restX r a : ℝ) with hX`. Establish `hp2 : (2 : ℝ) ≤ p` using `by exact_mod_cast hp.two_le`. Establish `hp0 : (0 : ℝ) < p` using `by linarith`.

Establish `hX0 : 0 ≤ X` using `by rw [hX]; unfold restX; positivity`. Establish `hN : 2 ≤ r + a` using `by omega`. Establish `hXp : X ≤ 3 / 8 * (p : ℝ)`. Use `XOverPrime.intersectionNumber_baseChange f r a B₀ p hf hN hB hpB` as an intermediate fact. Rewrite `this` using `[div_le_iff₀ hp0]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hY0 : 0 ≤ Y` using `by positivity`. Establish `hterm : ∀ τ : Fin f, ∀ k ∈ Finset.Icc 2 (r + a), |∑' n : ℕ, ((p : ℝ) ^ ((n + 1) * k))⁻¹ * ((e p (n + 1) τ k * restTerm f (r + a) Q k τ (smallPowerSum f r a c (k - 1) (s p (n + 1) τ)) : ℚ) : ℝ)| ≤ (Y * X ^ (k - 1) / (k.factorial : ℝ)) * (2 * ((p : ℝ) ^ k)⁻¹)`. Introduce `τ k hk`. Rewrite `hk` using `[Finset.mem_Icc]`.

Use `(h₁ (p : ℝ) k _ _ hp2 (by omega) ?_).2` and prove the remaining obligations. Introduce `n`. Establish `hb` using `hT k hk.1 hk.2 τ (s p (n + 1) τ)`. Establish `habs : |e p (n + 1) τ k * restTerm f (r + a) Q k τ (smallPowerSum f r a c (k - 1) (s p (n + 1) τ))| = |restTerm f (r + a) Q k τ (smallPowerSum f r a c (k - 1) (s p (n + 1) τ))|`. Rewrite using `[abs_mul]`.

Apply the tactic sequence `rcases he p (n + 1) τ k with h | h <;> simp [h]`. Rewrite using `[← Rat.cast_abs, habs]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hY, hX]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hsumk` using `h₂ (p : ℝ) X (r + a) hp0 hX0 hXp`. Establish `hlog : 0 ≤ Real.log p` using `Real.log_nonneg (by linarith)`. Unfold `restPrimeModel`. Rewrite using `[abs_mul, abs_of_nonneg hlog]`.

Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul_of_nonneg_left _ hlog` to reduce the goal to its premises. Use `(Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun τ _ => ?_)` and prove the remaining obligations. Use `(Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)` and prove the remaining obligations. Conclude with `hterm τ k hk`.

Use `_ = Real.log p * ((f : ℝ) * (Y * ∑ k ∈ Finset.Icc 2 (r + a), 2 * ((p : ℝ) ^ k)⁻¹ * X ^ (k - 1) / (k.factorial : ℝ))) := by`. Rewrite using `[Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Use `congr 1`. Use `congr 1`. Rewrite using `[Finset.mul_sum]`.

Conclude with `Finset.sum_congr rfl fun k _ => by ring`. Use `_ ≤ Real.log p * ((f : ℝ) * (Y * (1.5 * X / (p : ℝ) ^ 2))) := by gcongr`. Use `_ = 1.5 * (f : ℝ) * X * (Real.log p / (p : ℝ) ^ 2) * Y := by ring`. Use `_ = 1.5 * f * (restX r a : ℝ) * (Real.log p / (p : ℝ) ^ 2) * ((f * (r * a) + 1 : ℕ) : ℝ) * |(fibreDegree f r a c : ℝ)| := by`. Rewrite using `[hY, hX]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem RestPrimeBoundOfFactor.proof (h₁ : RestInnerTsumBound.Statement)
    (h₂ : RestKSumBound.Statement) : RestPrimeBoundOfFactor.Statement := by
  intro f r a c B₀ hf hr ha hB Q hT s e he p hp hpB
  set Y : ℝ := ((f * (r * a) + 1 : ℕ) : ℝ) * |(fibreDegree f r a c : ℝ)| with hY
  set X : ℝ := (restX r a : ℝ) with hX
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hX0 : 0 ≤ X := by rw [hX]; unfold restX; positivity
  have hN : 2 ≤ r + a := by omega
  have hXp : X ≤ 3 / 8 * (p : ℝ) := by
    have := XOverPrime.intersectionNumber_baseChange f r a B₀ p hf hN hB hpB
    rw [div_le_iff₀ hp0] at this
    linarith
  have hY0 : 0 ≤ Y := by positivity

  have hterm : ∀ τ : Fin f, ∀ k ∈ Finset.Icc 2 (r + a),
      |∑' n : ℕ, ((p : ℝ) ^ ((n + 1) * k))⁻¹ *
        ((e p (n + 1) τ k * restTerm f (r + a) Q k τ
          (smallPowerSum f r a c (k - 1) (s p (n + 1) τ)) : ℚ) : ℝ)| ≤
        (Y * X ^ (k - 1) / (k.factorial : ℝ)) * (2 * ((p : ℝ) ^ k)⁻¹) := by
    intro τ k hk
    rw [Finset.mem_Icc] at hk
    refine (h₁ (p : ℝ) k _ _ hp2 (by omega) ?_).2
    intro n
    have hb := hT k hk.1 hk.2 τ (s p (n + 1) τ)
    have habs : |e p (n + 1) τ k * restTerm f (r + a) Q k τ
        (smallPowerSum f r a c (k - 1) (s p (n + 1) τ))| =
        |restTerm f (r + a) Q k τ (smallPowerSum f r a c (k - 1) (s p (n + 1) τ))| := by
      rw [abs_mul]
      rcases he p (n + 1) τ k with h | h <;> simp [h]
    rw [← Rat.cast_abs, habs]
    calc ((|restTerm f (r + a) Q k τ (smallPowerSum f r a c (k - 1) (s p (n + 1) τ))| : ℚ) : ℝ)
        ≤ ((((f * (r * a) + 1 : ℕ) : ℚ) * |fibreDegree f r a c| * restX r a ^ (k - 1) /
            (k.factorial : ℚ) : ℚ) : ℝ) := Rat.cast_le.mpr hb
      _ = Y * X ^ (k - 1) / (k.factorial : ℝ) := by
        rw [hY, hX]; push_cast; ring
  have hsumk := h₂ (p : ℝ) X (r + a) hp0 hX0 hXp
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  unfold restPrimeModel
  rw [abs_mul, abs_of_nonneg hlog]
  calc Real.log p * |∑ τ : Fin f, ∑ k ∈ Finset.Icc 2 (r + a), ∑' n : ℕ,
        ((p : ℝ) ^ ((n + 1) * k))⁻¹ *
          ((e p (n + 1) τ k * restTerm f (r + a) Q k τ
            (smallPowerSum f r a c (k - 1) (s p (n + 1) τ)) : ℚ) : ℝ)|
      ≤ Real.log p * ∑ τ : Fin f, ∑ k ∈ Finset.Icc 2 (r + a),
          (Y * X ^ (k - 1) / (k.factorial : ℝ)) * (2 * ((p : ℝ) ^ k)⁻¹) := by
        apply mul_le_mul_of_nonneg_left _ hlog
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun τ _ => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
        exact hterm τ k hk
    _ = Real.log p * ((f : ℝ) * (Y * ∑ k ∈ Finset.Icc 2 (r + a),
          2 * ((p : ℝ) ^ k)⁻¹ * X ^ (k - 1) / (k.factorial : ℝ))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        congr 1
        congr 1
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ ≤ Real.log p * ((f : ℝ) * (Y * (1.5 * X / (p : ℝ) ^ 2))) := by
        gcongr
    _ = 1.5 * (f : ℝ) * X * (Real.log p / (p : ℝ) ^ 2) * Y := by ring
    _ = 1.5 * f * (restX r a : ℝ) * (Real.log p / (p : ℝ) ^ 2) *
          ((f * (r * a) + 1 : ℕ) : ℝ) * |(fibreDegree f r a c : ℝ)| := by
        rw [hY, hX]; ring

end

end RestTerms

end GroundTheory.Heights₂.Heights
