import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.StepFormula
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.CasimirBounds.Expand
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.CasimirBounds.CountCross

open Matrix

namespace PositivityTheory.Rg.Cz

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem casBound_holds : CasBound := by
  intro n Q _ _ C _ col b S hT hS f hf
  rw [cas_expand']
  have key : (star f ⬝ᵥ ((((n * S.card : ℕ) : ℂ) • (1 : Module.End ℂ (TV n ℂ Q)) +
      ∑ p ∈ S, ∑ q ∈ S.erase p, pm (Equiv.swap p q) : Module.End ℂ (TV n ℂ Q)) f)).re =
      ((n * S.card : ℕ) : ℝ) * (star f ⬝ᵥ f).re +
        ∑ p ∈ S, ∑ q ∈ S.erase p, (star f ⬝ᵥ pm (Equiv.swap p q) f).re := by
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, LinearMap.sum_apply,
      dotProduct_add, dotProduct_smul, dotProduct_sum, Complex.add_re, Complex.re_sum, smul_eq_mul]
    simp
  rw [key]
  refine cas_count hT hS (fun p q => (star f ⬝ᵥ pm (Equiv.swap p q) f).re) _ ?_ ?_ ?_
  · intro p q
    simp only [Equiv.swap_comm]
  · intro p q hpq hne
    simp [hf p q hpq hne]
  · intro p _ c hc
    have h1 := re_swapSum_le' f (S.filter fun q => col q = c) p
      (by simp only [Finset.mem_filter, not_and]; exact fun _ h => hc h.symm)
      (by
        intro q hq q' hq' hne
        simp only [Finset.mem_filter] at hq hq'
        exact hf q q' (hq.2.trans hq'.2.symm) hne)
    simpa only [Complex.re_sum] using h1

end PositivityTheory.Rg.Cz
