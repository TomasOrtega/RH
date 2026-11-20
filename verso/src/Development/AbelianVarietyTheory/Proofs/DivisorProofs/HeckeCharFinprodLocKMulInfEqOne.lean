import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Formalism.LocalToGlobal.UnitaryNorms.CharProd
import Formalism.LocalToGlobal.NumberFieldFamilies.IdTransSM
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalIdeleSndSelf

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.HCharUnit

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions.

Use linear arithmetic over natural numbers and integers. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem locK_eq_one {E : Type} [Field E] [NumberField E] (χ : HChar E) (k : Eˣ) (v : HeightOneSpectrum (𝓞 E))
    (hu : χ.UnrAt v) (ho : ordF v k = 0) : χ.locK v k = 1 := by
  apply hu
  show Valued.v (((k : E) : v.adicCompletion E)) = 1
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  have h0 : v.valuation E (k : E) ≠ 0 := by simp
  have hl : WithZero.log (v.valuation E (k : E)) = 0 := by
    unfold ordF at ho; omega
  rw [← WithZero.exp_log h0, hl, WithZero.exp_zero]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Assume the negation of the conclusion and derive a contradiction. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Rewrite the conclusion using the stated equalities.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem finprod_locK_mul_inf : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (k : Eˣ),
    (Function.mulSupport fun w : Pl E => χ.locK w k).Finite ∧ (∏ᶠ w : Pl E, χ.locK w k) * χ.inf k = 1 := by
  intro E _ _ χ k
  have hT : ({v | ¬ χ.UnrAt v} ∪ {v : HeightOneSpectrum (𝓞 E) | ordF v k ≠ 0}).Finite :=
    Set.Finite.union (Filter.eventually_cofinite.mp (Formalism.L2.Fam.IdTrans.unrAe χ)) (GlobalTheory.HeckeProduct.finite_ordF k)
  set S := hT.toFinset with hSdef
  have hsub : (Function.mulSupport fun w : Pl E => χ.locK w k) ⊆ (S : Set (HeightOneSpectrum (𝓞 E))) := by
    intro v hv
    rw [hSdef, Set.Finite.coe_toFinset]
    by_contra h
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at h
    exact hv (locK_eq_one χ k v h.1 h.2)
  refine ⟨S.finite_toSet.subset hsub, ?_⟩
  have hS : ∀ v, v ∉ S → χ.UnrAt v := by
    intro v hv
    by_contra h
    exact hv (by rw [hSdef, Set.Finite.mem_toFinset]; exact Or.inl h)
  have hpr := Formalism.L2.Host.HChar.productRule χ S hS k
  have hrest : (∏ᶠ (v : HeightOneSpectrum (𝓞 E)) (_ : v ∉ S), χ.val v ^ ordF v k) = 1 := by
    apply finprod_eq_one_of_forall_eq_one
    intro v
    rw [finprod_eq_if]
    split_ifs with hv
    · rfl
    have : ordF v k = 0 := by
      by_contra h
      exact hv (by rw [hSdef, Set.Finite.mem_toFinset]; exact Or.inr h)
    rw [this, zpow_zero]
  rw [hrest, mul_one] at hpr
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub, mul_comm]
  exact hpr

end GlobalTheory.HCharUnit
