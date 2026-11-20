import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZModTorsorIff
open CategoryTheory Limits TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `R D _ _ _ _ hP hF`. Take `⟨s, hs⟩` from `Module.projective_def'.mp hP`. Set `ev : (D →ₗ[R] R) →ₗ[R] R` to `{ toFun := fun τ => τ 1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }`. Distinguish the cases in `hI : LinearMap.range ev = ⊤`. Take `⟨τ, hτ⟩` from `LinearMap.mem_range.mp (hI ▸ Submodule.mem_top : (1 : R) ∈ LinearMap.range ev)`.

Conclude with `⟨τ, hτ⟩`. Take `⟨m, hm, hIm⟩` from `Ideal.exists_le_maximal (LinearMap.range ev) hI`. It suffices to derive a contradiction. Establish `hcoord : ∀ x : D, s 1 x ∈ m` using `fun x => hIm (LinearMap.mem_range.mpr ⟨Finsupp.lapply x ∘ₗ s, rfl⟩)`. Establish `h1 : (1 : D) ∈ m • (⊤ : Submodule R D)`.

Establish `: Finsupp.linearCombination R id (s 1) = (1 : D)` using `LinearMap.congr_fun hs 1`. Rewrite using `[← this, Finsupp.linearCombination_apply]`. Conclude with `Submodule.sum_mem _ fun x _ => Submodule.smul_mem_smul (hcoord x) Submodule.mem_top`. Establish `hmul : ∀ d : D, ∀ y ∈ m • (⊤ : Submodule R D), d * y ∈ m • (⊤ : Submodule R D)`. Introduce `d y hy`.

Use `Submodule.smul_induction_on hy ?_ ?_` and prove the remaining obligations. Introduce `r hr n _`. Rewrite using `[mul_smul_comm]`. Conclude with `Submodule.smul_mem_smul hr Submodule.mem_top`. Introduce `x z hx hz`.

Rewrite using `[mul_add]`. Conclude with `Submodule.add_mem _ hx hz`. Apply `Module.FaithfullyFlat.submodule_ne_top (M := D) hm` to reduce the goal to its premises. Rewrite using `[eq_top_iff]`. Introduce `d _`.

Simplify using `using hmul d 1 h1`.
-/
theorem unit_splits_of_projective_faithfullyFlat :
    ∀ (R D : Type) [CommRing R] [CommRing D] [Algebra R D], Module.Finite R D →
    Module.Projective R D → Module.FaithfullyFlat R D → ∃ τ : D →ₗ[R] R, τ 1 = 1 := by
  intro R D _ _ _ _ hP hF
  obtain ⟨s, hs⟩ := Module.projective_def'.mp hP
  let ev : (D →ₗ[R] R) →ₗ[R] R :=
    { toFun := fun τ => τ 1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  by_cases hI : LinearMap.range ev = ⊤
  · obtain ⟨τ, hτ⟩ := LinearMap.mem_range.mp (hI ▸ Submodule.mem_top : (1 : R) ∈ LinearMap.range ev)
    exact ⟨τ, hτ⟩
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal (LinearMap.range ev) hI
  exfalso
  have hcoord : ∀ x : D, s 1 x ∈ m := fun x =>
    hIm (LinearMap.mem_range.mpr ⟨Finsupp.lapply x ∘ₗ s, rfl⟩)
  have h1 : (1 : D) ∈ m • (⊤ : Submodule R D) := by
    have : Finsupp.linearCombination R id (s 1) = (1 : D) := LinearMap.congr_fun hs 1
    rw [← this, Finsupp.linearCombination_apply]
    exact Submodule.sum_mem _ fun x _ => Submodule.smul_mem_smul (hcoord x) Submodule.mem_top
  have hmul : ∀ d : D, ∀ y ∈ m • (⊤ : Submodule R D), d * y ∈ m • (⊤ : Submodule R D) := by
    intro d y hy
    refine Submodule.smul_induction_on hy ?_ ?_
    · intro r hr n _
      rw [mul_smul_comm]; exact Submodule.smul_mem_smul hr Submodule.mem_top
    · intro x z hx hz
      rw [mul_add]; exact Submodule.add_mem _ hx hz
  apply Module.FaithfullyFlat.submodule_ne_top (M := D) hm
  rw [eq_top_iff]
  intro d _
  simpa using hmul d 1 h1

end GlobalTheory
