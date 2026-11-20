import Development.EtaleCohomology.DivisorCycles.OpenCoset

namespace LateralTheory.DivDb.SpecPtPf

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact.

Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result.

Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem SpecPt_of : LateralTheory.DivDb.SpecPt := by
  intro C R σ _ _ _ _ _ _ x G hG hx
  classical
  let I : Ideal (MvPolynomial σ C) := RingHom.ker (MvPolynomial.aeval (R := C) x)
  have hI : I.IsPrime := RingHom.ker_isPrime _
  let P : MvPolynomial σ C := ∏ g ∈ hG.toFinset, g
  have hP : MvPolynomial.aeval x P ≠ 0 := by
    simp only [P, map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun g hg => hx g (hG.mem_toFinset.mp hg)
  have hPI : P ∉ I.radical := by
    rw [hI.radical]; exact hP
  rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := C), MvPolynomial.mem_vanishingIdeal_iff] at hPI
  push Not at hPI
  obtain ⟨y, hy, hyP⟩ := hPI
  rw [MvPolynomial.mem_zeroLocus_iff] at hy
  refine ⟨y, fun f hf => ?_, fun g hg => ?_⟩
  · have := hy f (RingHom.mem_ker.mpr hf)
    simpa [MvPolynomial.coe_aeval_eq_eval] using this
  · simp only [P, map_prod] at hyP
    exact (Finset.prod_ne_zero_iff.mp hyP) g (hG.mem_toFinset.mpr hg)

end LateralTheory.DivDb.SpecPtPf
