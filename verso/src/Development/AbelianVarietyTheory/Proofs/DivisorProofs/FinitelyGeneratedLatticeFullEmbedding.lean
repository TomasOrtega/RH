import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm
open NumberField ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.LieHt

namespace GlobalTheory

/- English proof (translation)
Introduce `K _ _ m W hW`. Set `S : Submodule K (Fin m → K)` to `Submodule.span K (W : Set (Fin m → K))`. Set `b : Module.Basis (Fin (latRank K W)) K S` to `Module.finBasisOfFinrankEq K S rfl`. Set `α : (Fin (latRank K W) → K) →ₗ[K] (Fin m → K)` to `S.subtype ∘ₗ b.equivFun.symm.toLinearMap`. Establish `hinj : Function.Injective α` using `S.injective_subtype.comp b.equivFun.symm.injective`.

Establish `hrange : LinearMap.range α = S`. Simplify using `only [α]`. Rewrite using `[LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]`. Establish `hmap : (W.comap (α.restrictScalars (𝓞 K))).map (α.restrictScalars (𝓞 K)) = W`. Apply `Submodule.map_comap_eq_self` to reduce the goal to its premises.

Introduce `x hx`. Establish `hxS : x ∈ LinearMap.range α`. Rewrite using `[hrange]`. Conclude with `Submodule.subset_span hx`. Take `⟨y, hy⟩` from `hxS`.

Conclude with `⟨y, hy⟩`. Use `⟨α, hinj, ⟨?_, ?_⟩, hmap⟩` and prove the remaining obligations. Apply `Submodule.fg_of_fg_map_injective (α.restrictScalars (𝓞 K)) hinj` to reduce the goal to its premises. Rewrite using `[hmap]`. Conclude with `hW`.

Apply `Submodule.map_injective_of_injective hinj` to reduce the goal to its premises. Establish `himg : α '' ((W.comap (α.restrictScalars (𝓞 K)) : Submodule (𝓞 K) _) : Set _) = (W : Set (Fin m → K))`. Use `congrArg (fun T : Submodule (𝓞 K) (Fin m → K) => (T : Set (Fin m → K))) hmap` as an intermediate fact. Simplify `this` using `only [Submodule.map_coe, LinearMap.coe_restrictScalars]`. Rewrite using `[Submodule.map_span, himg, Submodule.map_top, hrange]`.
-/
theorem exists_injective_full_comap_map_eq : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ) (W : Submodule (𝓞 K) (Fin m → K)), W.FG → ∃ α : (Fin (latRank K W) → K) →ₗ[K] (Fin m → K), Function.Injective α ∧ Full (W.comap (α.restrictScalars (𝓞 K))) ∧ (W.comap (α.restrictScalars (𝓞 K))).map (α.restrictScalars (𝓞 K)) = W := by
  intro K _ _ m W hW
  let S : Submodule K (Fin m → K) := Submodule.span K (W : Set (Fin m → K))
  let b : Module.Basis (Fin (latRank K W)) K S := Module.finBasisOfFinrankEq K S rfl
  let α : (Fin (latRank K W) → K) →ₗ[K] (Fin m → K) := S.subtype ∘ₗ b.equivFun.symm.toLinearMap
  have hinj : Function.Injective α := S.injective_subtype.comp b.equivFun.symm.injective
  have hrange : LinearMap.range α = S := by
    simp only [α]
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]
  have hmap : (W.comap (α.restrictScalars (𝓞 K))).map (α.restrictScalars (𝓞 K)) = W := by
    apply Submodule.map_comap_eq_self
    intro x hx
    have hxS : x ∈ LinearMap.range α := by
      rw [hrange]; exact Submodule.subset_span hx
    obtain ⟨y, hy⟩ := hxS
    exact ⟨y, hy⟩
  refine ⟨α, hinj, ⟨?_, ?_⟩, hmap⟩
  · apply Submodule.fg_of_fg_map_injective (α.restrictScalars (𝓞 K)) hinj
    rw [hmap]; exact hW
  · apply Submodule.map_injective_of_injective hinj
    have himg : α '' ((W.comap (α.restrictScalars (𝓞 K)) : Submodule (𝓞 K) _) : Set _) = (W : Set (Fin m → K)) := by
      have := congrArg (fun T : Submodule (𝓞 K) (Fin m → K) => (T : Set (Fin m → K))) hmap
      simpa only [Submodule.map_coe, LinearMap.coe_restrictScalars] using this
    rw [Submodule.map_span, himg, Submodule.map_top, hrange]

end GlobalTheory
