import Mathlib

/- English proof (translation)
Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => simp only [Finset.prod_empty]`. Conclude with `IsLocallyConstant.const (1 : ℂ)`. Consider the case `insert a s ha ih`. Simplify using `only [Finset.prod_insert ha]`.

Conclude with `(h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`.
-/
theorem UpperTheory.Reformulated.B.Qf48.isLC_prod {X : Type*} {ι : Type*} [TopologicalSpace X] (T : Finset ι) (f : ι → X → ℂ)
    (h : ∀ i ∈ T, IsLocallyConstant (f i)) : IsLocallyConstant fun x ↦ ∏ i ∈ T, f i x := by
  classical
  induction T using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact IsLocallyConstant.const (1 : ℂ)
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
