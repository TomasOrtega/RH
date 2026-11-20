import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegerSpanningFamilyOfUnramifiedExt

noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Equip the data with the indicated structure. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem intMap_isIntegral_of_unr : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ →
    ∃ φO : K.O →+* K'.O, (∀ x, algebraMap K'.O K'.E (φO x) = φ (algebraMap K.O K.E x)) ∧
      @Algebra.IsIntegral K.O K'.O _ _ φO.toAlgebra := by
  intro K K' d φ hU
  obtain ⟨φO, hφO⟩ := exists_intMap_of_unr hU
  refine ⟨φO, hφO, ?_⟩
  letI : Algebra K.O K'.O := φO.toAlgebra
  obtain ⟨u, hu⟩ := exists_int_basis_of_unr K K' d φ hU
  have hspan : Submodule.span K.O (Set.range u) = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨a, ha⟩ := hu y
    have hy : y = ∑ i, a i • u i := by
      apply IsFractionRing.injective K'.O K'.E
      rw [ha, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, map_mul]
      change φ (algebraMap K.O K.E (a i)) * _ = algebraMap K'.O K'.E (φO (a i)) * _
      rw [hφO]
    rw [hy]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  haveI : Module.Finite K.O K'.O := ⟨Submodule.fg_def.2 ⟨_, Set.finite_range u, hspan⟩⟩
  exact Algebra.IsIntegral.of_finite K.O K'.O

end GlobalTheory.UnitLemma.Unr
