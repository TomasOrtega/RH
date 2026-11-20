import Mathlib

namespace GlobalTheory.FinitePointsDetect

/- English proof (translation)
Introduce `X W _`. Set `ev : X → (W →ₗ[ℂ] ℂ)` to `fun x => (LinearMap.proj x).comp W.subtype`. Set `K : Finset X → Submodule ℂ W` to `fun s => ⨅ x ∈ s, LinearMap.ker (ev x)`. Take `⟨_, ⟨s, rfl⟩, hs⟩` from `(wellFounded_lt (α := Submodule ℂ W)).has_min (Set.range K) ⟨K ∅, ∅, rfl⟩`. Establish `key : ∀ v ∈ K s, ∀ y : X, (↑v : X → ℂ) y = 0`.

Introduce `v hv y`. Establish `hle : K (insert y s) ≤ K s`. Introduce `w hw`. Simplify using `only [K, Submodule.mem_iInf] at hw ⊢`. Introduce `x hx`.

Conclude with `hw x (Finset.mem_insert_of_mem hx)`. Establish `heq : K (insert y s) = K s` using `eq_of_le_of_not_lt hle (hs _ ⟨_, rfl⟩)`. Rewrite `hv` using `[← heq]`. Simplify using `only [K, Submodule.mem_iInf] at hv`. Use `hv y (Finset.mem_insert_self y s)` as an intermediate fact.

Simplify `this` using `[ev]`. Use `⟨s, fun v hv => ?_⟩` and prove the remaining obligations. Establish `hvK : v ∈ K s`. Simplify using `only [K, Submodule.mem_iInf]`. Introduce `x hx`.

Simplify `hv x hx` using `[ev]`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `y`. Simplify using `using key v hvK y`.
-/
theorem finite_points_detect : ∀ {X : Type} (W : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ ↥W],
    ∃ (s : Finset X), ∀ (v : ↥W), (∀ x ∈ s, (↑v : X → ℂ) x = (0 : ℂ)) → v = (0 : ↥W) := by
  intro X W _
  classical
  let ev : X → (W →ₗ[ℂ] ℂ) := fun x => (LinearMap.proj x).comp W.subtype
  let K : Finset X → Submodule ℂ W := fun s => ⨅ x ∈ s, LinearMap.ker (ev x)
  obtain ⟨_, ⟨s, rfl⟩, hs⟩ :=
    (wellFounded_lt (α := Submodule ℂ W)).has_min (Set.range K) ⟨K ∅, ∅, rfl⟩
  have key : ∀ v ∈ K s, ∀ y : X, (↑v : X → ℂ) y = 0 := by
    intro v hv y
    have hle : K (insert y s) ≤ K s := by
      intro w hw
      simp only [K, Submodule.mem_iInf] at hw ⊢
      intro x hx
      exact hw x (Finset.mem_insert_of_mem hx)
    have heq : K (insert y s) = K s := eq_of_le_of_not_lt hle (hs _ ⟨_, rfl⟩)
    rw [← heq] at hv
    simp only [K, Submodule.mem_iInf] at hv
    have := hv y (Finset.mem_insert_self y s)
    simpa [ev] using this
  refine ⟨s, fun v hv => ?_⟩
  have hvK : v ∈ K s := by
    simp only [K, Submodule.mem_iInf]
    intro x hx
    simpa [ev] using hv x hx
  apply Subtype.ext
  funext y
  simpa using key v hvK y

end GlobalTheory.FinitePointsDetect
