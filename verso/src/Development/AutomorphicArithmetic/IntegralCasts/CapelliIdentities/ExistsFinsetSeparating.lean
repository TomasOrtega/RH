import Mathlib

/- English proof (translation)
Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `V _ hn`. Distinguish the cases in `hV : ∀ v ∈ V, v = 0`. Conclude with `⟨∅, fun v hv _ => hV v hv⟩`.

Take `⟨w, hw⟩` from `not_forall.mp hV`. Take `⟨hwV, hw0⟩` from `Classical.not_imp.mp hw`. Take `⟨x, hx⟩` from `Function.ne_iff.mp hw0`. Set `U : Submodule ℂ (X → ℂ)` to `V ⊓ LinearMap.ker (LinearMap.proj x : (X → ℂ) →ₗ[ℂ] ℂ)`. Establish `hle : U ≤ V` using `inf_le_left`.

Establish `hlt : U < V`. Use `lt_of_le_of_ne hle ?_` and prove the remaining obligations. Introduce `h`. Establish `hwU : w ∈ U` using `h ▸ hwV`. Conclude with `hx (LinearMap.mem_ker.mp (Submodule.mem_inf.mp hwU).2)`.

Use `haveI : FiniteDimensional ℂ U := Submodule.finiteDimensional_of_le hle`. Establish `hr : Module.finrank ℂ U < n` using `hn ▸ Submodule.finrank_lt_finrank_of_lt hlt`. Take `⟨T, hT⟩` from `ih _ hr U rfl`. Use `⟨insert x T, fun v hv h => hT v ?_ fun y hy => h y (Finset.mem_insert_of_mem hy)⟩` and prove the remaining obligations. Conclude with `Submodule.mem_inf.mpr ⟨hv, LinearMap.mem_ker.mpr (h x (Finset.mem_insert_self x T))⟩`.
-/
private theorem UpperTheory.Reformulated.B.Qp2.aux {X : Type} (n : ℕ) :
    ∀ (V : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ ↥V], Module.finrank ℂ V = n →
    ∃ (T : Finset X), ∀ v ∈ V, (∀ x ∈ T, v x = (0 : ℂ)) → v = (0 : X → ℂ) := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V _ hn
    by_cases hV : ∀ v ∈ V, v = 0
    · exact ⟨∅, fun v hv _ => hV v hv⟩
    · obtain ⟨w, hw⟩ := not_forall.mp hV
      obtain ⟨hwV, hw0⟩ := Classical.not_imp.mp hw
      obtain ⟨x, hx⟩ := Function.ne_iff.mp hw0
      let U : Submodule ℂ (X → ℂ) := V ⊓ LinearMap.ker (LinearMap.proj x : (X → ℂ) →ₗ[ℂ] ℂ)
      have hle : U ≤ V := inf_le_left
      have hlt : U < V := by
        refine lt_of_le_of_ne hle ?_
        intro h
        have hwU : w ∈ U := h ▸ hwV
        exact hx (LinearMap.mem_ker.mp (Submodule.mem_inf.mp hwU).2)
      haveI : FiniteDimensional ℂ U := Submodule.finiteDimensional_of_le hle
      have hr : Module.finrank ℂ U < n := hn ▸ Submodule.finrank_lt_finrank_of_lt hlt
      obtain ⟨T, hT⟩ := ih _ hr U rfl
      refine ⟨insert x T, fun v hv h => hT v ?_ fun y hy => h y (Finset.mem_insert_of_mem hy)⟩
      exact Submodule.mem_inf.mpr ⟨hv, LinearMap.mem_ker.mpr (h x (Finset.mem_insert_self x T))⟩

/- English proof (translation)
Introduce `X V _`. Conclude with `UpperTheory.Reformulated.B.Qp2.aux _ V rfl`.
-/
theorem UpperTheory.Reformulated.B.Qp2.exists_finset_separating :
    ∀ {X : Type} (V : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ ↥V],
    ∃ (T : Finset X), ∀ v ∈ V, (∀ x ∈ T, v x = (0 : ℂ)) → v = (0 : X → ℂ) := by
  intro X V _
  exact UpperTheory.Reformulated.B.Qp2.aux _ V rfl
