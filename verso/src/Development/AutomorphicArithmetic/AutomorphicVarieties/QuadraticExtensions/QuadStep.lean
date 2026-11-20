import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.IdxTwo
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.IneChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.IneConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.AbBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.DegBasic

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. The claim follows by propositional logic. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Two.quadStep :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : AbF) (p N n : ℕ), p.Prime → p ∣ N → CardLe (CharOff (cycU 2 (abU Ω A)) (ineOff ℚ Ω N) 2) n → CardLe (CharOff (cycU 2 (abU Ω (A.sup (AbF.quad p)))) (ineOff ℚ Ω N) 2) (n ^ 2) := by
  intro Ω _ _ _ A p N n hp hpN h
  have hsup := (abBasic Ω).1 A (AbF.quad p)
  have hq := (abBasic Ω).2.1 (AbF.quad p)
  have key : cycU 2 (abU Ω (A.sup (AbF.quad p))) = abU Ω (AbF.quad p) ⊓ cycU 2 (abU Ω A) := by
    ext g
    simp only [cycU, hsup, Subgroup.mem_inf]
    tauto
  rw [key]
  have hidx : (abU Ω (AbF.quad p)).index ∣ 2 := by
    rw [hq.1]
    exact degBasic.2.2.1 p hp
  have hnorm : (abU Ω (AbF.quad p)).Normal := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hidx with h1 | h2
    · rw [Subgroup.index_eq_one] at h1
      rw [h1]
      infer_instance
    · exact Subgroup.normal_of_index_eq_two h2
  refine idxTwo (G ℚ Ω) _ (cycU 2 (abU Ω A)) (ineOff ℚ Ω N) n inf_le_right ?_ ?_ ?_ ?_ h
  · rw [Subgroup.inf_subgroupOf_right, Subgroup.coe_subgroupOf]
    exact hq.2.2.1.preimage continuous_subtype_val
  · rw [Subgroup.inf_relIndex_right]
    exact (Subgroup.relIndex_dvd_index_of_normal _ _).trans hidx
  · intro v _ s hs
    exact (ineConj ℚ Ω v).2.2 N s hs
  · intro s hs hsV
    refine Subgroup.mem_inf.2 ⟨?_, hsV⟩
    obtain ⟨B, hB, hsB⟩ := hs
    haveI : NeZero (AbF.quad p).m := ⟨by simp [AbF.quad]⟩
    have hv : ¬ B.valuation ((AbF.quad p).m : Ω) < 1 := by
      intro hlt
      apply hB
      obtain ⟨k, rfl⟩ := hpN
      have hm : (AbF.quad p).m = p := max_eq_left hp.one_lt.le
      rw [hm] at hlt
      rw [Nat.cast_mul, map_mul]
      have hk : B.valuation (k : Ω) ≤ 1 := (B.valuation_le_one_iff _).2 (natCast_mem B k)
      exact lt_of_le_of_lt (mul_le_of_le_one_right' hk) hlt
    exact hq.2.2.2 (ineChar Ω (AbF.quad p).m B hv hsB)
