import Mathlib

noncomputable section

open NumberField IsDedekindDomain

namespace PositivityTheory.UnitarySelfGeneration.Mend

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem specInt_norm_le_one_iff_mem (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (x : v.adicCompletion F) : ‖x‖ ≤ 1 ↔ x ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  exact Valued.toNormedField.norm_le_one_iff

open Polynomial in
/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem specInt_isIntegral_iff_coeff {K L : Type*} [Field K] [Field L] [Algebra K L] (O : ValuationSubring K)
    [Algebra O L] [IsScalarTower O K L] (y : L) (hy : IsIntegral K y) :
    IsIntegral O y ↔ ∀ n, (minpoly K y).coeff n ∈ O := by
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' K h, coeff_map]
    exact Subtype.property _
  · intro h
    have hl : minpoly K y ∈ lifts (algebraMap O K) := by
      rw [lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hm⟩ := lifts_and_natDegree_eq_and_monic hl (minpoly.monic hy)
    refine ⟨q, hm, ?_⟩
    rw [← aeval_def, ← aeval_map_algebraMap K, hq, minpoly.aeval]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem spectralNorm_le_one_iff_isIntegral (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (y : AlgebraicClosure (v.adicCompletion F)) :
    spectralNorm (v.adicCompletion F) (AlgebraicClosure (v.adicCompletion F)) y ≤ 1 ↔
      IsIntegral (v.adicCompletionIntegers F) y := by
  have hy : IsIntegral (v.adicCompletion F) y := Algebra.IsIntegral.isIntegral y
  rw [specInt_isIntegral_iff_coeff (v.adicCompletionIntegers F) y hy, spectralNorm,
    spectralValue_le_one_iff (minpoly.monic hy)]
  simp only [specInt_norm_le_one_iff_mem]

end PositivityTheory.UnitarySelfGeneration.Mend
