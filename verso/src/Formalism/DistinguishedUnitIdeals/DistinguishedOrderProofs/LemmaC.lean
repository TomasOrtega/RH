import Mathlib
import Formalism.DistinguishedUnitIdeals.CoprimeProd
import Formalism.EisensteinCokernelLengths.FactorialValuationBounds.LemmaCRam

noncomputable section

namespace Formalism.ExponentWindows

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem eisE_of_assoc {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
    (hϖ : Irreducible ϖ) {ℓ e N : ℕ} (hℓe : Associated (ℓ : O) (ϖ ^ e)) (E : Polynomial O)
    (hm : E.Monic) (hd : E.natDegree = N) (hc : ∀ i < N, (ℓ : O) ∣ E.coeff i)
    (h0 : Associated (E.coeff 0) (ℓ : O)) : Formalism.ZetaNonvanishing.EisensteinGaussValuationBounds.EisE ϖ e E N := by
  refine ⟨hm, hd, fun i hi => ?_, ?_⟩
  · rw [Ideal.mem_span_singleton]
    exact dvd_trans hℓe.symm.dvd (hc i hi)
  · rw [Ideal.mem_span_singleton]
    intro hdiv
    have h1 : ϖ ^ (e + 1) ∣ ϖ ^ e := dvd_trans hdiv (h0.trans hℓe).dvd
    have hne : ϖ ^ e ≠ 0 := pow_ne_zero _ hϖ.ne_zero
    rw [pow_succ] at h1
    have h2 : ϖ ^ e * ϖ ∣ ϖ ^ e * 1 := by rwa [mul_one]
    have h3 := (mul_dvd_mul_iff_left hne).1 h2
    exact hϖ.not_isUnit (isUnit_of_dvd_one h3)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

Establish an intermediate fact. Establish an intermediate fact. Move the embeddings inside the algebraic operations. Use the polynomial consequences of the given equalities and inequalities. Extract witnesses or component facts from the available result.

Move the embeddings inside the algebraic operations. Prove the components needed by the constructor for the conclusion. Chain the equalities or inequalities of the calculation. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lemma_C_valuation_real : LemmaCValR := by
  intro O _ _ _ ϖ hϖ ℓ e hℓ he hℓe E u hmon hdeg hcoef h0 hu ell g a b₀ b₁ s₀ s₁ k hs h1 h2 hmem
  have hEis : ∀ s, Formalism.ZetaNonvanishing.EisensteinGaussValuationBounds.EisE ϖ e (E s) (ℓ ^ s) := fun s =>
    eisE_of_assoc hϖ hℓe (E s) (hmon s) (hdeg s) (hcoef s) (h0 s)
  obtain ⟨w, hw⟩ := hℓe

  have hmem' : PowerSeries.C (ϖ ^ (e * a)) *
        (∏ s ∈ Finset.range ell, (u s * (E s : PowerSeries O)) ^ g) ^ 2 *
        (u s₀ * (E s₀ : PowerSeries O)) ^ b₀ ∈
      Ideal.span {PowerSeries.C (ϖ ^ k), (u s₁ * (E s₁ : PowerSeries O)) ^ b₁} := by
    have hpow : ϖ ^ (e * a) = (ℓ : O) ^ a * ((w : O) ^ a) := by
      rw [pow_mul, ← hw, mul_pow]
    have := Ideal.mul_mem_left _ (PowerSeries.C ((w : O) ^ a)) hmem
    convert this using 1
    rw [hpow, map_mul]
    ring
  have hepos : (0 : ℝ) < e := by exact_mod_cast (by omega : 0 < e)
  have h1' : 2 * (((e * a : ℕ) : ℝ) + 2 * e * g * ell) < e * b₁ := by
    push_cast
    nlinarith
  obtain ⟨k1, k2⟩ := Formalism.ZetaNonvanishing.EisensteinGaussValuationBounds.lemmaCValRam_proof O ϖ hϖ e he ℓ hℓ E u hEis hu ell g (e * a)
    b₀ b₁ s₀ s₁ k hs h1' h2 hmem'
  push_cast at k1 k2
  constructor
  · calc (k : ℝ) ≤ ((e : ℝ) * a + 2 * e * g * ell) * b₁ / (b₁ - b₀ / ℓ) := k1
      _ = e * (((a : ℝ) + 2 * g * ell) * b₁ / (b₁ - b₀ / ℓ)) := by ring
  · linarith

end Formalism.ExponentWindows
