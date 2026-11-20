import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm
open NumberField ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.LieHt

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
