import Mathlib
import Formalism.QuotientMetricDivisors.StatementACE
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic

open Module NumberField IsDedekindDomain
open scoped Matrix

noncomputable section

namespace Formalism.DivisionValues

namespace ValuationZeroReduction

variable {K : Type} [Field K] [NumberField K] [StarRing K]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Apply an available result and prove the equalities needed to match it to the conclusion.

A detailed English derivation is pending.
-/
theorem vw_eq_zero_of_not_mem (w : HeightOneSpectrum (𝓞 K)) (s : 𝓞 K) (hs : s ∉ w.asIdeal) :
    vw w (s : K) = 0 := by
  have hs0 : s ≠ 0 := fun h => hs (h ▸ w.asIdeal.zero_mem)
  have hJ : Ideal.span {s} ≠ (0 : Ideal (𝓞 K)) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hs0
  classical
  have hnd : ¬ w.asIdeal ∣ Ideal.span {s} := by
    rw [Ideal.dvd_span_singleton]; exact hs
  have hirr : Irreducible w.asIdeal := (Ideal.prime_of_isPrime w.ne_bot w.isPrime).irreducible
  have hc := mt (Associates.count_ne_zero_iff_dvd hJ hirr).mp hnd
  push_neg at hc
  unfold vw
  rw [show (s : K) = algebraMap (𝓞 K) K s from rfl, ← FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.count_coe K w hJ, Nat.cast_eq_zero]
  convert hc

end ValuationZeroReduction

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Consider separately whether the proposition holds or fails.

Prove the first alternative. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts.

A detailed English derivation is pending.
-/
theorem reduction_first_step : StepA := by
  intro K _ _ _ w n D M π ι B P ζ σ hζ hvζ hP hM x hx
  obtain ⟨s, hs, hsx⟩ := hx
  have hs' : s ∉ w.asIdeal := hs
  obtain ⟨y, hy, hyx⟩ := hsx
  obtain ⟨F, hF, hFy⟩ := hy
  simp only [LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply] at hFy hyx
  have hs0 : s ≠ 0 := fun h => hs' (h ▸ w.asIdeal.zero_mem)
  have hsK : algebraMap (𝓞 K) K s ≠ 0 := by
    intro h; apply hs0; apply IsFractionRing.injective (𝓞 K) K; rw [map_zero]; exact h
  have hPF : P F = ζ * (algebraMap (𝓞 K) K s * B x) := by
    rw [hP F, hFy, hyx, ← algebraMap_smul K s x, map_smul, smul_eq_mul]
  have hvmul : ∀ a b : K, a ≠ 0 → b ≠ 0 → vw w (a * b) = vw w a + vw w b := by
    intro a b ha hb
    unfold vw
    rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, FractionalIdeal.count_mul K w
      (fun h => ha (FractionalIdeal.spanSingleton_eq_zero_iff.mp h))
      (fun h => hb (FractionalIdeal.spanSingleton_eq_zero_iff.mp h))]
  have hv0 : vw w (algebraMap (𝓞 K) K s) = 0 := ValuationZeroReduction.vw_eq_zero_of_not_mem w s hs'
  by_cases hBx : B x = 0
  · exact Or.inl hBx
  · right
    have hPF0 : P F ≠ 0 := by rw [hPF]; exact mul_ne_zero hζ (mul_ne_zero hsK hBx)
    rcases hM F hF with h0 | hσ
    · exact absurd h0 hPF0
    · rw [hPF, hvmul _ _ hζ (mul_ne_zero hsK hBx), hvmul _ _ hsK hBx, hvζ, hv0] at hσ
      simpa using hσ

end Formalism.DivisionValues
