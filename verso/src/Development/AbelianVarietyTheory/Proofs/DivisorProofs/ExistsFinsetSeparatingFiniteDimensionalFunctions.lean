import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory

/- English proof (translation)
Use `haveI := hW`. Set `N : Finset K → Submodule ℂ (K → ℂ)` to `fun s => W ⊓ ⨅ k ∈ s, LinearMap.ker (LinearMap.proj k : (K → ℂ) →ₗ[ℂ] ℂ)`. Establish `memN : ∀ s w, w ∈ N s ↔ w ∈ W ∧ ∀ k ∈ s, w k = 0`. Introduce `s w`. Simplify using `[N, Submodule.mem_iInf]`.

Establish `hex : ∃ n, ∃ s : Finset K, Module.finrank ℂ (N s) = n` using `⟨_, ∅, rfl⟩`. Take `⟨s0, hs0⟩` from `Nat.find_spec hex`. Establish `hmin : ∀ s : Finset K, Nat.find hex ≤ Module.finrank ℂ (N s)` using `fun s => Nat.find_min' hex ⟨s, rfl⟩`. Establish `hfin : ∀ s, FiniteDimensional ℂ (N s)` using `fun s => Submodule.finiteDimensional_of_le (inf_le_left)`. Use `⟨s0, fun w hw hvan => ?_⟩` and prove the remaining obligations.

Establish `hwN : w ∈ N s0` using `(memN s0 w).2 ⟨hw, hvan⟩`. Use function extensionality and compare the values at `k`. Establish `hle : N (insert k s0) ≤ N s0`. Introduce `v hv`. Rewrite `hv`, the goal using `[memN]`.

Conclude with `⟨hv.1, fun j hj => hv.2 j (Finset.mem_insert_of_mem hj)⟩`. Establish `heq : N (insert k s0) = N s0` using `Submodule.eq_of_le_of_finrank_le hle (by rw [hs0]; exact hmin _)`. Rewrite `hwN` using `[← heq, memN]`. Conclude with `hwN.2 k (Finset.mem_insert_self k s0)`.
-/
theorem finiteDim_functions_detected_by_finset (K : Type) (W : Submodule ℂ (K → ℂ))
    (hW : FiniteDimensional ℂ W) :
    ∃ s : Finset K, ∀ w ∈ W, (∀ k ∈ s, w k = 0) → w = 0 := by
  classical
  haveI := hW
  let N : Finset K → Submodule ℂ (K → ℂ) := fun s =>
    W ⊓ ⨅ k ∈ s, LinearMap.ker (LinearMap.proj k : (K → ℂ) →ₗ[ℂ] ℂ)
  have memN : ∀ s w, w ∈ N s ↔ w ∈ W ∧ ∀ k ∈ s, w k = 0 := by
    intro s w
    simp [N, Submodule.mem_iInf]
  have hex : ∃ n, ∃ s : Finset K, Module.finrank ℂ (N s) = n := ⟨_, ∅, rfl⟩
  obtain ⟨s0, hs0⟩ := Nat.find_spec hex
  have hmin : ∀ s : Finset K, Nat.find hex ≤ Module.finrank ℂ (N s) :=
    fun s => Nat.find_min' hex ⟨s, rfl⟩
  have hfin : ∀ s, FiniteDimensional ℂ (N s) := fun s =>
    Submodule.finiteDimensional_of_le (inf_le_left)
  refine ⟨s0, fun w hw hvan => ?_⟩
  have hwN : w ∈ N s0 := (memN s0 w).2 ⟨hw, hvan⟩
  funext k
  have hle : N (insert k s0) ≤ N s0 := by
    intro v hv
    rw [memN] at hv ⊢
    exact ⟨hv.1, fun j hj => hv.2 j (Finset.mem_insert_of_mem hj)⟩
  have heq : N (insert k s0) = N s0 :=
    Submodule.eq_of_le_of_finrank_le hle (by rw [hs0]; exact hmin _)
  rw [← heq, memN] at hwN
  exact hwN.2 k (Finset.mem_insert_self k s0)

/- English proof (translation)
The claim follows from `finiteDim_functions_detected_by_finset`.
-/
example : ∀ (K : Type) (W : Submodule ℂ (K → ℂ)), FiniteDimensional ℂ W → ∃ s : Finset K, ∀ w ∈ W, (∀ k ∈ s, w k = 0) → w = 0 :=
  finiteDim_functions_detected_by_finset

end GlobalTheory
