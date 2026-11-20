import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Introduce `hF W V U r p _ _ Ω _ x M _ c`. Establish `hset : fib (r ≫ p) x = ⋃ y ∈ fib p x, fib r y`. Use extensionality with `z`. Simplify using `only [fib, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]`. Prove the components needed by the constructor for the conclusion.

Introduce `hz`. Conclude with `⟨z ≫ r, by rw [Category.assoc]; exact hz, rfl⟩`. Introduce and unpack `⟨y, hy, hz⟩`. Rewrite using `[← Category.assoc, hz, hy]`. Establish `hdisj : (fib p x).PairwiseDisjoint (fun y => fib r y)`.

Introduce `y₁ _ y₂ _ hne`. Use `Set.disjoint_left.mpr ?_` and prove the remaining obligations. Introduce `z h₁ h₂`. Apply `hne` to reduce the goal to its premises. Simplify using `only [fib, Set.mem_setOf_eq] at h₁ h₂`.

Rewrite using `[← h₁, ← h₂]`. Express the relevant statement in the definitionally equal form `∑ᶠ z ∈ fib (r ≫ p) x, c z = ∑ᶠ y ∈ fib p x, ∑ᶠ z ∈ fib r y, c z`. Rewrite using `[hset]`. Conclude with `finsum_mem_biUnion hdisj (hF p Ω x) (fun y _ => hF r Ω y)`.
-/
theorem UpperTheory.Gal.TranscendenceTraces.sumComp_of :
    FibFin → SumComp := by
  intro hF W V U r p _ _ Ω _ x M _ c
  have hset : fib (r ≫ p) x = ⋃ y ∈ fib p x, fib r y := by
    ext z
    simp only [fib, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    constructor
    · intro hz
      exact ⟨z ≫ r, by rw [Category.assoc]; exact hz, rfl⟩
    · rintro ⟨y, hy, hz⟩
      rw [← Category.assoc, hz, hy]
  have hdisj : (fib p x).PairwiseDisjoint (fun y => fib r y) := by
    intro y₁ _ y₂ _ hne
    refine Set.disjoint_left.mpr ?_
    intro z h₁ h₂
    apply hne
    simp only [fib, Set.mem_setOf_eq] at h₁ h₂
    rw [← h₁, ← h₂]
  change ∑ᶠ z ∈ fib (r ≫ p) x, c z = ∑ᶠ y ∈ fib p x, ∑ᶠ z ∈ fib r y, c z
  rw [hset]
  exact finsum_mem_biUnion hdisj (hF p Ω x) (fun y _ => hF r Ω y)
