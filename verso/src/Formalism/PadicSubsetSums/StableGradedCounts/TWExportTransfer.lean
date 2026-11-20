import Formalism.PadicSubsetSums.StableGradedCounts.TWIndexScale

namespace Formalism.IrreducibleCountingLemmas.TW

/- English proof (translation)
Introduce `O K V _ _ _ _ _ _ _ _ _ _ _ M B N N' c e ε hM hB hN hN' hc he hle`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Take `⟨n, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ`. Rewrite `hle` using `[index_scaling O K V B N' ϖ u n hB hN' hϖ, index_scaling O K V B N ϖ u n hB hN hϖ]`. Establish `a` using `(index_additive O K V M N N' hM hN hN').2`.

Establish `b` using `(index_additive O K V B N N' hB hN hN').2`. Establish `d : sIdx M N' - sIdx M N = sIdx B N' - sIdx B N` using `by omega`. Establish `d' : (sIdx M N' : ℝ) - sIdx M N = sIdx B N' - sIdx B N` using `by exact_mod_cast d`. Move the coercions through the operations in `at hle`. Rewrite `hle` using `[add_div, add_div]`.

Establish `h1 : (sIdx M N' : ℝ) / e - sIdx M N / e = sIdx B N' / e - sIdx B N / e`. Rewrite using `[← sub_div, ← sub_div, d']`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem export_transfer_holds : ExportTransfer := by
  intro O K V _ _ _ _ _ _ _ _ _ _ _ M B N N' c e ε hM hB hN hN' hc he hle
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
  rw [index_scaling O K V B N' ϖ u n hB hN' hϖ, index_scaling O K V B N ϖ u n hB hN hϖ]
    at hle
  have a := (index_additive O K V M N N' hM hN hN').2
  have b := (index_additive O K V B N N' hB hN hN').2
  have d : sIdx M N' - sIdx M N = sIdx B N' - sIdx B N := by omega
  have d' : (sIdx M N' : ℝ) - sIdx M N = sIdx B N' - sIdx B N := by exact_mod_cast d
  push_cast at hle
  rw [add_div, add_div] at hle
  have h1 : (sIdx M N' : ℝ) / e - sIdx M N / e = sIdx B N' / e - sIdx B N / e := by
    rw [← sub_div, ← sub_div, d']
  linarith

end Formalism.IrreducibleCountingLemmas.TW
