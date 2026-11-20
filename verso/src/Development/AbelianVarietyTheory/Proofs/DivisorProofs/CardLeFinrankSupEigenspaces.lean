import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `W _ _ _ O T hc I _ ψ hψ hpos`. Use `set V : I → Submodule ℂ W := fun i => ⨅ a, Module.End.eigenspace (T a) (ψ i a) with hVdef`. Establish `hind` using `Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo T (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hc j i) φ)`. Establish `hV : iSupIndep V`. Use `(hind.comp hψ).mono ?_` and prove the remaining obligations.

Introduce `i`. Conclude with `iInf_mono fun a => Module.End.eigenspace_le_maxGenEigenspace`. Establish `hne : ∀ i, ∃ v ∈ V i, v ≠ 0`. Introduce `i`. Establish `: V i ≠ ⊥`.

Introduce `h`. Establish `h2` using `hpos i`. Express the relevant statement in the definitionally equal form `1 ≤ Module.finrank ℂ (V i) at h2`. Rewrite `h2` using `[h, finrank_bot]`. Use linear arithmetic over natural numbers and integers.

Conclude with `Submodule.exists_mem_ne_zero_of_ne_bot this`. Use `choose v hvV hv0 using hne`. Use `set S : Submodule ℂ W := ⨆ i, V i`. Establish `hvS : ∀ i, v i ∈ S` using `fun i => Submodule.mem_iSup_of_mem i (hvV i)`. Establish `hli : LinearIndependent ℂ v` using `iSupIndep.linearIndependent V hV hvV hv0`.

Set `w : I → S` to `fun i => ⟨v i, hvS i⟩`. Establish `hw : LinearIndependent ℂ w`. Apply `LinearIndependent.of_comp S.subtype` to reduce the goal to its premises. Conclude with `hli`. Conclude with `hw.fintype_card_le_finrank`.
-/
theorem finrank_iSup_iInf_eigenspace_ge_card : ∀ (W : Type 1) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (O : Type) (T : O → Module.End ℂ W),
    (∀ a b, Commute (T a) (T b)) → ∀ (I : Type) [Fintype I] (ψ : I → O → ℂ), Function.Injective ψ →
    (∀ i, 1 ≤ Module.finrank ℂ (⨅ a, Module.End.eigenspace (T a) (ψ i a) : Submodule ℂ W)) →
    Fintype.card I ≤ Module.finrank ℂ (⨆ i, ⨅ a, Module.End.eigenspace (T a) (ψ i a) : Submodule ℂ W) := by
  intro W _ _ _ O T hc I _ ψ hψ hpos
  set V : I → Submodule ℂ W := fun i => ⨅ a, Module.End.eigenspace (T a) (ψ i a) with hVdef
  have hind := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo T
    (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hc j i) φ)
  have hV : iSupIndep V := by
    refine (hind.comp hψ).mono ?_
    intro i
    exact iInf_mono fun a => Module.End.eigenspace_le_maxGenEigenspace
  have hne : ∀ i, ∃ v ∈ V i, v ≠ 0 := by
    intro i
    have : V i ≠ ⊥ := by
      intro h
      have h2 := hpos i
      change 1 ≤ Module.finrank ℂ (V i) at h2
      rw [h, finrank_bot] at h2
      omega
    exact Submodule.exists_mem_ne_zero_of_ne_bot this
  choose v hvV hv0 using hne
  set S : Submodule ℂ W := ⨆ i, V i
  have hvS : ∀ i, v i ∈ S := fun i => Submodule.mem_iSup_of_mem i (hvV i)
  have hli : LinearIndependent ℂ v := iSupIndep.linearIndependent V hV hvV hv0
  let w : I → S := fun i => ⟨v i, hvS i⟩
  have hw : LinearIndependent ℂ w := by
    apply LinearIndependent.of_comp S.subtype
    exact hli
  exact hw.fintype_card_le_finrank

end GlobalTheory
