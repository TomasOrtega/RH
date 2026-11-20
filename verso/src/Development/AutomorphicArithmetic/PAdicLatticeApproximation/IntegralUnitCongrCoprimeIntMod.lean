import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.WitSys
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCompletionEqLatticeVectorAddNsmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDvdOfEqNatMulIntegralAdeleAwayFromP

open NumberField
open GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo UpperTheory.Gal.W2.Wit
open scoped TensorProduct

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem UpperTheory.integral_unit_congr_coprime_int_mod :
    ∀ (p : ℕ) [Fact p.Prime] (ε : (AfP p)ˣ), IsIntAf (ε : AfP p) → IsIntAf ((ε⁻¹ : (AfP p)ˣ) : AfP p) → ∀ n : ℕ, 0 < n → n.Coprime p → ∃ (ν : ℤ) (b : AfP p), IsIntAf b ∧ (ε : AfP p) = (ν : AfP p) + (n : AfP p) * b ∧ IsCoprime ν (n : ℤ) := by
  intro p _ ε hε hε' n hn hnp
  obtain ⟨ν, b, hb, hνb⟩ := LaHatMod.exists_int_add_mul n hn hnp _ hε
  obtain ⟨μ, b', hb', hμb⟩ := LaHatMod.exists_int_add_mul n hn hnp _ hε'
  refine ⟨ν, b, hb, hνb, ?_⟩
  have hint : IsIntAf ((ν : AfP p) * b' + (μ : AfP p) * b + (n : AfP p) * b * b') := by
    intro v
    simp only [map_add, map_mul, map_intCast, map_natCast]
    exact add_mem (add_mem (mul_mem (intCast_mem _ ν) (hb' v)) (mul_mem (intCast_mem _ μ) (hb v)))
      (mul_mem (mul_mem (natCast_mem _ n) (hb v)) (hb' v))
  have hprod : (1 : AfP p) = (ν : AfP p) * μ +
      n * ((ν : AfP p) * b' + (μ : AfP p) * b + (n : AfP p) * b * b') := by
    have : (ε : AfP p) * ((ε⁻¹ : (AfP p)ˣ) : AfP p) = 1 := Units.mul_inv ε
    rw [← this, hνb, hμb]
    ring
  have hdvd : (n : ℤ) ∣ 1 - ν * μ := by
    apply IntDvd.int_dvd_of_eq_mul_isIntAf p n hn hnp _ _ hint
    rw [map_intCast, Int.cast_sub, Int.cast_one, Int.cast_mul]
    linear_combination hprod
  obtain ⟨k, hk⟩ := hdvd
  exact ⟨μ, k, by linear_combination -hk⟩
