import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

/- English proof (translation)
Introduce `X Y _ μ V hV F hF hI`. Set `ev : Y → (V →ₗ[ℂ] ℂ)` to `fun y => (LinearMap.proj y).comp V.subtype`. Establish `hspan : Submodule.span ℂ (Set.range ev) = ⊤`. Apply `Submodule.span_eq_top_of_ne_zero` to reduce the goal to its premises. Introduce `z hz`.

Assume the negation of the conclusion as `h`. Apply `hz` to reduce the goal to its premises. Use extensionality with `y`. Assume the negation of the conclusion as `hy`. Conclude with `h ⟨ev y, ⟨y, rfl⟩, hy⟩`.

Establish `hint : ∀ φ : V →ₗ[ℂ] ℂ, Integrable (fun x => φ ⟨F x, hF x⟩) μ`. Introduce `φ`. Establish `hφ : φ ∈ Submodule.span ℂ (Set.range ev)` using `hspan ▸ Submodule.mem_top`. Proceed by induction on `hφ using Submodule.span_induction with`. Consider the case `mem f hf => obtain ⟨y, rfl⟩ := hf`.

Conclude with `hI y`. Consider the case `zero => simp`. Consider the case `add f g _ _ hf hg => exact hf.add hg`. Consider the case `smul c f _ hf => exact hf.const_mul c`. Set `b` to `Module.finBasis ℂ V`.

Establish `key : (fun y => ∫ x, F x y ∂μ) = ∑ i, (∫ x, b.coord i ⟨F x, hF x⟩ ∂μ) • ((b i : V) : Y → ℂ)`. Use function extensionality and compare the values at `y`. Establish `h1 : ∀ x, F x y = ∑ i, b.coord i ⟨F x, hF x⟩ * ((b i : V) : Y → ℂ) y`. Introduce `x`. Establish `h` using `congrArg (ev y) (b.sum_repr ⟨F x, hF x⟩)`.

Rewrite `h` using `[map_sum]`. Simplify using `only [map_smul] at h`. Conclude with `h.symm`. Simplify using `only [h1, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[integral_finset_sum _ (fun i _ => (hint (b.coord i)).mul_const _)]`.

Conclude with `Finset.sum_congr rfl fun i _ => integral_mul_const _ _`. Rewrite using `[key]`. Conclude with `V.sum_mem fun i _ => V.smul_mem _ (b i).2`.
-/
theorem UpperTheory.locallyFinite_of_algMod_criterion :
    ∀ (X Y : Type) [MeasurableSpace X] (μ : Measure X) (V : Submodule ℂ (Y → ℂ)), FiniteDimensional ℂ V → ∀ F : X → Y → ℂ, (∀ x, F x ∈ V) → (∀ y, Integrable (fun x => F x y) μ) → (fun y => ∫ x, F x y ∂μ) ∈ V := by
  intro X Y _ μ V hV F hF hI
  classical
  let ev : Y → (V →ₗ[ℂ] ℂ) := fun y => (LinearMap.proj y).comp V.subtype
  have hspan : Submodule.span ℂ (Set.range ev) = ⊤ := by
    apply Submodule.span_eq_top_of_ne_zero
    intro z hz
    by_contra h
    apply hz
    ext y
    by_contra hy
    exact h ⟨ev y, ⟨y, rfl⟩, hy⟩
  have hint : ∀ φ : V →ₗ[ℂ] ℂ, Integrable (fun x => φ ⟨F x, hF x⟩) μ := by
    intro φ
    have hφ : φ ∈ Submodule.span ℂ (Set.range ev) := hspan ▸ Submodule.mem_top
    induction hφ using Submodule.span_induction with
    | mem f hf => obtain ⟨y, rfl⟩ := hf; exact hI y
    | zero => simp
    | add f g _ _ hf hg => exact hf.add hg
    | smul c f _ hf => exact hf.const_mul c
  let b := Module.finBasis ℂ V
  have key : (fun y => ∫ x, F x y ∂μ)
      = ∑ i, (∫ x, b.coord i ⟨F x, hF x⟩ ∂μ) • ((b i : V) : Y → ℂ) := by
    funext y
    have h1 : ∀ x, F x y = ∑ i, b.coord i ⟨F x, hF x⟩ * ((b i : V) : Y → ℂ) y := by
      intro x
      have h := congrArg (ev y) (b.sum_repr ⟨F x, hF x⟩)
      rw [map_sum] at h
      simp only [map_smul] at h
      exact h.symm
    simp only [h1, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [integral_finset_sum _ (fun i _ => (hint (b.coord i)).mul_const _)]
    exact Finset.sum_congr rfl fun i _ => integral_mul_const _ _
  rw [key]
  exact V.sum_mem fun i _ => V.smul_mem _ (b i).2
