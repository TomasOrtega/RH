import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TensorOperator.Development

open MvPolynomial

noncomputable section

namespace PI.TOW.MonoW

open PI.TO PI.TOW

/- English proof (translation)
Introduce `K _ n' k μ`. Simplify using `only [embS, rename_monomial]`. It suffices to establish `hμ : μ = ∑ t, Finsupp.mapDomain (fun c => (t, c)) (partS μ t) by`. Rewrite using `[← MvPolynomial.monomial_sum_one, ← hμ]`. Use extensionality with `⟨t, c⟩`.

Rewrite using `[Finsupp.finset_sum_apply, Finset.sum_eq_single t]`. Rewrite using `[Finsupp.mapDomain_apply (fun a b h => by simpa using h)]`. Simplify using `[partS]`. Introduce `t' _ ht'`. Rewrite using `[Finsupp.mapDomain_notin_range]`.

Introduce and unpack `⟨c', hc'⟩`. Conclude with `ht' (congrArg Prod.fst hc')`. Simplify using the standard rewrite rules.
-/
theorem stepMonoFactor : StepMonoFactor := by
  intro K _ n' k μ
  simp only [embS, rename_monomial]
  suffices hμ : μ = ∑ t, Finsupp.mapDomain (fun c => (t, c)) (partS μ t) by
    rw [← MvPolynomial.monomial_sum_one, ← hμ]
  ext ⟨t, c⟩
  rw [Finsupp.finset_sum_apply, Finset.sum_eq_single t]
  · rw [Finsupp.mapDomain_apply (fun a b h => by simpa using h)]
    simp [partS]
  · intro t' _ ht'
    rw [Finsupp.mapDomain_notin_range]
    rintro ⟨c', hc'⟩
    exact ht' (congrArg Prod.fst hc')
  · simp

end PI.TOW.MonoW
