import Mathlib

open scoped Matrix TensorProduct
open Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

/- English proof (translation)
Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Establish an intermediate fact.

Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules.

Assume the hypotheses and unpack their components. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Supply the required witnesses or components. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem comap_fg_of_valuationRing (R : Type) [CommRing R] [IsDomain R] [ValuationRing R]
    (ι κ : Type) [Fintype ι] [Fintype κ] (φ : (ι → R) →ₗ[R] (κ → R)) (W : Submodule R (κ → R))
    (hW : W.FG) : (W.comap φ).FG := by
  obtain ⟨c, w, hw⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hW
  let ψ : ((ι → R) × (Fin c → R)) →ₗ[R] (κ → R) := φ.coprod (Fintype.linearCombination R w)
  have hflat : Module.Flat R (LinearMap.range ψ) := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout]
    exact Submodule.isTorsionFree_iff_torsion_eq_bot.mp inferInstance
  have hfree : Module.Free R (LinearMap.range ψ) := Module.free_of_flat_of_isLocalRing
  have hfp : Module.FinitePresentation R (LinearMap.range ψ) :=
    Module.finitePresentation_of_projective _ _
  have hsurj : Function.Surjective ψ.rangeRestrict := by
    rintro ⟨y, x, rfl⟩
    exact ⟨x, rfl⟩
  have hker : (LinearMap.ker ψ.rangeRestrict).FG :=
    Module.FinitePresentation.fg_ker _ hsurj
  have heq : W.comap φ = (LinearMap.ker ψ.rangeRestrict).map (LinearMap.fst R (ι → R) (Fin c → R)) := by
    ext l
    simp only [Submodule.mem_comap, Submodule.mem_map, LinearMap.mem_ker, LinearMap.fst_apply]
    constructor
    · intro hl
      rw [← hw, ← Fintype.range_linearCombination] at hl
      obtain ⟨a, ha⟩ := hl
      refine ⟨(l, -a), ?_, rfl⟩
      apply Subtype.ext
      simp [ψ, ha]
    · rintro ⟨⟨l', a⟩, h, rfl⟩
      have h' : φ l' + Fintype.linearCombination R w a = 0 := by
        simpa [ψ] using congrArg Subtype.val h
      have hm : Fintype.linearCombination R w a ∈ W := by
        rw [← hw, ← Fintype.range_linearCombination]
        exact ⟨a, rfl⟩
      rw [eq_neg_of_add_eq_zero_left h']
      exact W.neg_mem hm
  rw [heq]
  exact hker.map _

end GlobalTheory.CompanionTheory.Ar.GR
