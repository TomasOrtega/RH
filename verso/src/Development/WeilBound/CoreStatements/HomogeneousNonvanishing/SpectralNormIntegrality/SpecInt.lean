import Mathlib

noncomputable section

open NumberField IsDedekindDomain

namespace PositivityTheory.UnitarySelfGeneration.Mend

/- English proof (translation)
Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Conclude with `Valued.toNormedField.norm_le_one_iff`.
-/
theorem specInt_norm_le_one_iff_mem (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (x : v.adicCompletion F) : ‖x‖ ≤ 1 ↔ x ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  exact Valued.toNormedField.norm_le_one_iff

open Polynomial in
/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h n`. Rewrite using `[minpoly.isIntegrallyClosed_eq_field_fractions' K h, coeff_map]`. Conclude with `Subtype.property _`. Introduce `h`.

Establish `hl : minpoly K y ∈ lifts (algebraMap O K)`. Rewrite using `[lifts_iff_coeff_lifts]`. Introduce `n`. Conclude with `⟨⟨_, h n⟩, rfl⟩`. Take `⟨q, hq, -, hm⟩` from `lifts_and_natDegree_eq_and_monic hl (minpoly.monic hy)`.

Use `⟨q, hm, ?_⟩` and prove the remaining obligations. Rewrite using `[← aeval_def, ← aeval_map_algebraMap K, hq, minpoly.aeval]`.
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
Establish `hy : IsIntegral (v.adicCompletion F) y` using `Algebra.IsIntegral.isIntegral y`. Rewrite using `[specInt_isIntegral_iff_coeff (v.adicCompletionIntegers F) y hy, spectralNorm, spectralValue_le_one_iff (minpoly.monic hy)]`. Simplify using `only [specInt_norm_le_one_iff_mem]`.
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
