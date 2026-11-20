import Mathlib

/- English proof (translation)
Introduce `G V M _ _ _ _ _ _ R f h`. Set `b` to `Module.finBasis ℂ V`. Establish `key : {g : G | R g ∘ₗ f = f} = ⋂ i, {g : G | R g (f (b i)) = f (b i)}`. Use extensionality with `g`. Simplify using `only [Set.mem_setOf_eq, Set.mem_iInter]`.

Prove the components needed by the constructor for the conclusion. Introduce `hg i`. Conclude with `LinearMap.congr_fun hg (b i)`. Introduce `hg`. Conclude with `b.ext fun i => hg i`.

Rewrite using `[key]`. Conclude with `isOpen_iInter_of_finite fun i => h (b i)`.
-/
theorem UpperTheory.isOpen_stabilizer_linear_map :
    ∀ {G V M : Type} [TopologicalSpace G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup M] [Module ℂ M] (R : G → M →ₗ[ℂ] M) (f : V →ₗ[ℂ] M), (∀ v : V, IsOpen {g : G | R g (f v) = f v}) → IsOpen {g : G | R g ∘ₗ f = f} := by
  intro G V M _ _ _ _ _ _ R f h
  let b := Module.finBasis ℂ V
  have key : {g : G | R g ∘ₗ f = f} = ⋂ i, {g : G | R g (f (b i)) = f (b i)} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro hg i
      exact LinearMap.congr_fun hg (b i)
    · intro hg
      exact b.ext fun i => hg i
  rw [key]
  exact isOpen_iInter_of_finite fun i => h (b i)
