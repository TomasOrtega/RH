import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.CapelliQdetStatement

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Reduce the equality to equality of the corresponding arguments. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations.

Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem capelliQdet : CapelliQdetStatement := by
  refine ⟨fun 𝒰 _ _ n E x => ?_, fun n lam ω => ?_⟩
  · unfold Capelli.capelliC Capelli.cminor Formalism.REAL.qdet Formalism.REAL.qminor
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [zsmul_eq_mul]
    congr 1
    congr 1
    refine congrArg List.ofFn (funext fun j => ?_)
    simp only [Capelli.capEntry, Formalism.REAL.Tm, id, add_comm]
  · unfold Formalism.QuantumDeterminants.capP thV
    refine Finset.prod_congr rfl fun t _ => ?_
    push_cast
    ring

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
