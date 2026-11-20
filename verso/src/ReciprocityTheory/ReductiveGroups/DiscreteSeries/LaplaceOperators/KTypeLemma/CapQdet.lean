import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.CapelliQdetStatement

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

/- English proof (translation)
Use `⟨fun 𝒰 _ _ n E x => ?_, fun n lam ω => ?_⟩` and prove the remaining obligations. Unfold `Capelli.capelliC Capelli.cminor Formalism.REAL.qdet Formalism.REAL.qminor`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[zsmul_eq_mul]`. Use `congr 1`.

Use `congr 1`. Use `congrArg List.ofFn (funext fun j => ?_)` and prove the remaining obligations. Simplify using `only [Capelli.capEntry, Formalism.REAL.Tm, id, add_comm]`. Unfold `Formalism.QuantumDeterminants.capP thV`. Use `Finset.prod_congr rfl fun t _ => ?_` and prove the remaining obligations.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
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
