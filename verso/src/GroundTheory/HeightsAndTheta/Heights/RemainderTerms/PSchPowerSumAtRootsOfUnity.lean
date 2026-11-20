import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsSchur
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

/- English proof (translation)
Simplify to obtain the desired conclusion from the available facts.
-/
theorem SchPowerSumAtRootsOfUnity.rootOfUnity_isPrimitiveRoot {k : ℕ} (hk : 1 ≤ k) : IsPrimitiveRoot (rootOfUnity k) k := by
  simpa [rootOfUnity] using Complex.isPrimitiveRoot_exp k (by omega)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem SchPowerSumAtRootsOfUnity.proof : SchPowerSumAtRootsOfUnity.Statement := by
  intro N k j hk hkN hj
  have hprim := SchPowerSumAtRootsOfUnity.rootOfUnity_isPrimitiveRoot hk
  simp only [psum, map_sum, map_pow, aeval_X]
  have hsum : ∑ i : Fin N, rootOfUnityPoint N k i ^ j =
      ∑ i ∈ range k, (rootOfUnity k ^ j) ^ i := by
    unfold rootOfUnityPoint
    rw [Fin.sum_univ_eq_sum_range (fun i => (if i < k then rootOfUnity k ^ i else 0) ^ j) N,
      ← Finset.sum_range_add_sum_Ico _ hkN]
    rw [Finset.sum_eq_zero (s := Ico k N) (fun i hi => by
      simp only [Finset.mem_Ico] at hi
      simp [show ¬ i < k by omega, zero_pow (show j ≠ 0 by omega)]), add_zero]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_range] at hi
    simp [hi, ← pow_mul, mul_comm]
  rw [hsum]
  split_ifs with hd
  · have h1 : rootOfUnity k ^ j = 1 := (hprim.pow_eq_one_iff_dvd j).2 hd
    simp [h1]
  · have h1 : rootOfUnity k ^ j ≠ 1 := fun h => hd ((hprim.pow_eq_one_iff_dvd j).1 h)
    have h2 : (rootOfUnity k ^ j) ^ k = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow]
    rw [geom_sum_eq h1, h2, sub_self, zero_div]

end

end GroundTheory.Heights₂.Heights.RestTerms
