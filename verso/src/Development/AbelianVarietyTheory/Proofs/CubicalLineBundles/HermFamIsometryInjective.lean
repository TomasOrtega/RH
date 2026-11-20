import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ArakelovDegreeEqDegreeOfFamily

open NumberField ReciprocityTheory.GeometryOfNumbersTheory
open scoped ComplexOrder

namespace GlobalTheory.LamF

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem hermFam_isometry_injective {K : Type*} [Field K] [NumberField K] {V V' : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
    (h : HermFam K V) (h' : HermFam K V') (M : V →ₗ[K] V')
    (hM : ∀ s a b, h'.form s (M a) (M b) = h.form s a b) : Function.Injective M := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h0
  obtain ⟨s⟩ : Nonempty (K →+* ℂ) := inferInstance
  have hli : LinearIndependent K ![x] := by
    rw [linearIndependent_unique_iff]; simpa using h0
  have h1 := (h.posDef s 1 ![x] hli).diag_pos (i := 0)
  have h2 : h'.form s (M x) (M x) = 0 := by
    have := h'.smul_right s 0 (M x) (M x)
    rw [zero_smul, map_zero, zero_mul] at this
    rw [← this, hx]
  rw [hM] at h2
  simp [h2] at h1

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions.

Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem deg_map_isometry : ∀ (K : Type) [Field K] [NumberField K] (V V' : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h : HermFam K V) (h' : HermFam K V') (M : V →ₗ[K] V') (Λ : Submodule (𝓞 K) V), Λ.FG → (∀ s a b, h'.form s (M a) (M b) = h.form s a b) → ReciprocityTheory.GeometryOfNumbersTheory.deg h' (Λ.map (M.restrictScalars (𝓞 K))) = ReciprocityTheory.GeometryOfNumbersTheory.deg h Λ := by
  intro K _ _ V V' _ _ _ _ _ _ _ _ h h' M E hE hM
  have hinj := hermFam_isometry_injective h h' M hM
  obtain ⟨v, hv⟩ := exists_isFrame E hE
  have hv' : IsFrame K (E.map (M.restrictScalars (𝓞 K))) (M ∘ v) := by
    refine ⟨fun i => ⟨v i, hv.1 i, rfl⟩, hv.2.1.map' M (LinearMap.ker_eq_bot.2 hinj), ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    rw [Set.range_comp, Submodule.span_image]
    exact ⟨x, hv.2.2 hx, rfl⟩
  rw [arakelovDegree_eq_degreeOfFamily h hE hv, arakelovDegree_eq_degreeOfFamily h' (hE.map _) hv']
  unfold degreeOfFamily
  have e1 : ∀ s, h'.gram s (M ∘ v) = h.gram s v := fun s => by
    ext i j; simp [HermFam.gram, hM]
  have e2 : Submodule.span (𝓞 K) (Set.range (M ∘ v)) =
      (Submodule.span (𝓞 K) (Set.range v)).map (M.restrictScalars (𝓞 K)) := by
    rw [Submodule.map_span, Set.range_comp]; rfl
  simp only [e1, e2, Submodule.map_toAddSubgroup]
  rw [AddSubgroup.relIndex_map_map_of_injective _ _ (by exact hinj)]

end GlobalTheory.LamF
