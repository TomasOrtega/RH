import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPrimeZariskiDense
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsComplexFormsOnPoints
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPrimeComplexRadical
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsComplexMinimalPrimesContract
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem PrimeZariskiDense.eval_eq_zero_of_mem_map {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) {F : MvPolynomial (Σ k, ι k) ℂ}
    (hF : F ∈ P.map (MvPolynomial.map (Int.castRingHom ℂ))) : eval z F = 0 := by
  have hle : P.map (MvPolynomial.map (Int.castRingHom ℂ)) ≤ RingHom.ker (eval z) := by
    rw [Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap, RingHom.mem_ker]
    exact hz.2 f hf
  exact RingHom.mem_ker.mp (hle hF)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Express the relevant assertion in an equivalent form by its definition. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. It suffices to derive a contradiction. Simplify using the standard rewrite rules.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem PrimeZariskiDense.proof (h1 : ComplexFormsOnPoints.Statement) (h2 : PrimeComplexRadical.Statement)
    (h3 : ComplexMinimalPrimesContract.Statement) : PrimeZariskiDense.Statement := by
  intro K _ ι _ P j hP hj g hg z hz
  by_cases hrel : IsRelevant P
  · set Pc := P.map (MvPolynomial.map (Int.castRingHom ℂ)) with hPc
    have hgj : g * map (Int.castRingHom ℂ) j ∈ Pc := by
      refine h1 K ι P hP hrel _ fun w hw => ?_
      rw [map_mul]
      by_cases hjw : eval w (map (Int.castRingHom ℂ) j) = 0
      · rw [hjw, mul_zero]
      · rw [hg w hw hjw, zero_mul]
    have hrad : Pc.radical = Pc := (h2 (Σ k, ι k) P hP).radical
    have hgPc : g ∈ Pc := by
      rw [← hrad, ← Ideal.sInf_minimalPrimes, Ideal.mem_sInf]
      intro Q hQ
      change Q ∈ Pc.minimalPrimes at hQ
      have hQp : Q.IsPrime := hQ.1.1
      have hjQ : map (Int.castRingHom ℂ) j ∉ Q := by
        intro h
        apply hj
        rw [← h3 (Σ k, ι k) P hP Q hQ, Ideal.mem_comap]
        exact h
      exact (hQp.mem_or_mem (hQ.1.2 hgj)).resolve_right hjQ
    exact PrimeZariskiDense.eval_eq_zero_of_mem_map P hz hgPc
  · exfalso
    simp only [IsRelevant, not_forall, not_exists, not_not] at hrel
    obtain ⟨k, hk⟩ := hrel
    obtain ⟨i, hi⟩ := hz.1 k
    apply hi
    simpa using hz.2 _ (hk i)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
