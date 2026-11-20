import Mathlib
open MeasureTheory
namespace GlobalTheory.FinsetSumSmulCoe

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => filter_upwards [Lp.coeFn_zero ℂ (2 : ENNReal) μ] with x hx`. Simplify using `using hx`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha]`.

Use `filter_upwards [Lp.coeFn_add (c a • u a) (∑ i ∈ s, c i • u i), Lp.coeFn_smul (c a) (u a), ih] with x h1 h2 h3`. Rewrite using `[Finset.sum_insert ha]`. Express the relevant statement in the definitionally equal form `(((c a • u a + ∑ i ∈ s, c i • u i : Lp ℂ (2 : ENNReal) μ)) : α → ℂ) x = _`. Rewrite using `[h1, Pi.add_apply, h2, h3, Pi.smul_apply, smul_eq_mul]`.
-/
theorem coeFn_finset_sum_smul {α : Type} [MeasurableSpace α] {μ : Measure α} {ι : Type}
    (c : ι → ℂ) (u : ι → Lp ℂ (2 : ENNReal) μ) (s : Finset ι) :
    (((∑ i ∈ s, c i • u i : Lp ℂ (2 : ENNReal) μ) : α →ₘ[μ] ℂ) : α → ℂ) =ᵐ[μ]
      fun x => ∑ i ∈ s, c i * (((u i : α →ₘ[μ] ℂ)) : α → ℂ) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero ℂ (2 : ENNReal) μ] with x hx
    simpa using hx
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (c a • u a) (∑ i ∈ s, c i • u i), Lp.coeFn_smul (c a) (u a), ih]
      with x h1 h2 h3
    rw [Finset.sum_insert ha]
    change (((c a • u a + ∑ i ∈ s, c i • u i : Lp ℂ (2 : ENNReal) μ)) : α → ℂ) x = _
    rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, smul_eq_mul]

/- English proof (translation)
Introduce `α _ μ ι _ c u`. Conclude with `coeFn_finset_sum_smul c u Finset.univ`.
-/
theorem main : ∀ {α : Type} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} {ι : Type} [inst_1 : Fintype ι] (c : ι → ℂ) (u : ι → ↥(MeasureTheory.Lp ℂ (2 : ENNReal) μ)), (↑(↑(∑ i : ι, c i • u i) : α →ₘ[μ] ℂ) : α → ℂ) =ᵐ[μ] fun (x : α) ↦ ∑ i : ι, c i * (↑(↑(u i) : α →ₘ[μ] ℂ) : α → ℂ) x := by
  intro α _ μ ι _ c u
  exact coeFn_finset_sum_smul c u Finset.univ

end GlobalTheory.FinsetSumSmulCoe
