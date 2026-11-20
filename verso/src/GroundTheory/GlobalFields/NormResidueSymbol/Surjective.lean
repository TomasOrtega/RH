import Mathlib
import GroundTheory.GlobalFields.NormResidueSymbol.RestrictNormalInfiniteLocalSymbol
import GroundTheory.GlobalFields.FirstInequality

namespace GroundTheory.Global

open IsDedekindDomain NumberField IdeleGroup IntermediateField

noncomputable section

section Trivial

variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem range_ideleNorm_eq_top_of_ideleSymbol_eq_one (h : ∀ x, ideleSymbol K L x = 1) :
    (ideleNorm K L).range = ⊤ := by
  classical
  refine eq_top_iff.2 fun x _ ↦ (IdeleNorm.mem_range_ideleNorm_iff_forall L x).2
    ⟨fun v ↦ ?_, fun v ↦ ?_⟩
  · obtain ⟨w⟩ := nonempty_placesOver L v
    have h1 : finiteProj v x ∈ (localSymbol L v).ker := by
      rw [MonoidHom.mem_ker, ← ideleSymbol_finiteEmbedding]
      exact h _
    rw [ker_localSymbol L v w] at h1
    obtain ⟨y, hy⟩ := h1
    exact ⟨Pi.mulSingle w y, by rw [IdeleNorm.finiteLocalNorm_mulSingle]; exact hy⟩
  · obtain ⟨w⟩ := IdeleNorm.nonempty_infinitePlacesOver L v
    have h1 : infiniteProj v x ∈ (infiniteLocalSymbol L v).ker := by
      rw [MonoidHom.mem_ker, ← ideleSymbol_infiniteEmbedding]
      exact h _
    rw [ker_infiniteLocalSymbol L v w] at h1
    obtain ⟨y, hy⟩ := h1
    exact ⟨Pi.mulSingle w y, by rw [IdeleNorm.infiniteLocalNorm_mulSingle]; exact hy⟩

end Trivial

universe u

section Cyclic

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem finrank_eq_one_of_ideleSymbol_eq_one (h : ∀ x, ideleSymbol K L x = 1) :
    Module.finrank K L = 1 :=
  firstInequality.finrank_eq_one_of_sup_eq_top
    (top_le_iff.1 (range_ideleNorm_eq_top_of_ideleSymbol_eq_one L h ▸ le_sup_left))

end Cyclic

section Surjective

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]

attribute [local instance] galCommGroup

omit [NumberField K] [NumberField L] [IsMulCommutative (L ≃ₐ[K] L)] in

/- English proof (translation)
By extensionality, compare the relevant components. Express the relevant assertion in an equivalent form by its definition. A detailed English derivation is pending.
-/
theorem restrictNormal_fixedField_eq_one {N : Subgroup (L ≃ₐ[K] L)} [N.Normal] {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ N) : σ.restrictNormal (fixedField N) = 1 := by
  ext y
  change ((σ.restrictNormal (fixedField N) y : fixedField N) : L) = y
  exact (AlgEquiv.restrictNormal_commutes σ (fixedField N) y).trans
    ((mem_fixedField_iff N y).1 y.2 σ hσ)

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Use the resulting assumption. Extract witnesses or component facts from the available result. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem ideleSymbol_surjective : Function.Surjective (ideleSymbol K L) := by
  classical
  by_contra hs
  obtain ⟨σ, hσ⟩ := not_forall.1 hs
  set H := (ideleSymbol K L).range with hH
  have hσH : σ ∉ H := fun ⟨x, hx⟩ ↦ hσ ⟨x, hx⟩
  obtain ⟨ι, _, n, _, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite
    ((L ≃ₐ[K] L) ⧸ H)
  have hne : (QuotientGroup.mk' H σ) ≠ 1 := by
    rwa [ne_eq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  obtain ⟨i, hi⟩ : ∃ i, e (QuotientGroup.mk' H σ) i ≠ 1 := by
    by_contra hall
    push Not at hall
    exact hne ((MulEquiv.map_eq_one_iff e).1 (funext hall))
  set χ : (L ≃ₐ[K] L) →* Multiplicative (ZMod (n i)) :=
    (Pi.evalMonoidHom (fun j ↦ Multiplicative (ZMod (n j))) i).comp
      (e.toMonoidHom.comp (QuotientGroup.mk' H)) with hχ
  set N := χ.ker with hN
  have hHN : ∀ x, ideleSymbol K L x ∈ N := fun x ↦ by
    have hq : QuotientGroup.mk' H (ideleSymbol K L x) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact ⟨x, rfl⟩
    rw [hN, MonoidHom.mem_ker, hχ, MonoidHom.comp_apply, MonoidHom.comp_apply, hq, map_one, map_one]
  have hσN : σ ∉ N := hi
  set F := fixedField N with hF
  have : IsCyclic (F ≃ₐ[K] F) := by
    have e1 : (F ≃ₐ[K] F) ≃* χ.range :=
      (IsGalois.normalAutEquivQuotient N).symm.trans (QuotientGroup.quotientKerEquivRange χ)
    exact isCyclic_of_surjective e1.symm.toMonoidHom e1.symm.surjective
  have hF1 : ∀ x, ideleSymbol K F x = 1 := fun x ↦ by
    rw [← restrictNormal_ideleSymbol F L x]
    exact restrictNormal_fixedField_eq_one (hHN x)
  have hbot : F = ⊥ := finrank_eq_one_iff.1 (finrank_eq_one_of_ideleSymbol_eq_one hF1)
  have htop : N = ⊤ := by
    rw [← fixingSubgroup_fixedField N, ← hF, hbot, fixingSubgroup_bot]
  exact hσN (htop ▸ Subgroup.mem_top σ)

end Surjective

end

end GroundTheory.Global
