import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFunctionFieldDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

open scoped nonZeroDivisors

noncomputable section

set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Introduce a local definition for the expression. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Use symmetry to reverse the relation. Reduce the conclusion to the remaining proof obligations.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Treat this case separately.

Treat this case separately. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

A detailed English derivation is pending.
-/
theorem FunctionFieldDegree.proof : FunctionFieldDegree.Statement := by
  intro n d J A hJ hA
  let := projAlgebra J A
  let : Module (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := Algebra.toModule
  intro K L _ _ _ _ _ _ _ _ _ _
  have := hJ
  have : Module.Finite (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := hA.finite
  have : FaithfulSMul (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (by exact hA.injective)
  have : Algebra.IsAlgebraic (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    Algebra.IsIntegral.isAlgebraic

  have hbc : IsBaseChange K (IsScalarTower.toAlgHom (MvPolynomial (Fin d) ℂ)
      (MvPolynomial (Fin n) ℂ ⧸ J) L).toLinearMap :=
    IsLocalizedModule.isBaseChange (MvPolynomial (Fin d) ℂ)⁰ K _
  have hfin : FiniteDimensional K L := Module.Finite.equiv hbc.equiv
  refine ⟨hfin, ?_, ?_⟩
  ·
    rw [← hbc.equiv.finrank_eq, projDegree]
    let e : FractionRing (MvPolynomial (Fin d) ℂ) ≃ₐ[MvPolynomial (Fin d) ℂ] K :=
      FractionRing.algEquiv (MvPolynomial (Fin d) ℂ) K
    symm
    refine Algebra.finrank_eq_of_equiv_equiv e.toRingEquiv
      (Algebra.TensorProduct.congr e AlgEquiv.refl).toRingEquiv ?_
    ext x
    simp [Algebra.TensorProduct.algebraMap_apply]
  ·
    rw [eq_top_iff]
    intro z _
    set F := IntermediateField.adjoin K (Set.range fun j =>
      algebraMap (MvPolynomial (Fin n) ℂ ⧸ J) L (Ideal.Quotient.mk J (X j)))
    have hB : ∀ p : MvPolynomial (Fin n) ℂ,
        algebraMap (MvPolynomial (Fin n) ℂ ⧸ J) L (Ideal.Quotient.mk J p) ∈ F := by
      intro p
      induction p using MvPolynomial.induction_on with
      | C a =>
        have hC : Ideal.Quotient.mk J (C a) =
            algebraMap (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) (C a) := by
          change _ = Ideal.Quotient.mk J (pullback A (C a))
          have h := (pullback A).commutes a
          simp only [MvPolynomial.algebraMap_eq] at h
          rw [h]
        rw [hC, ← IsScalarTower.algebraMap_apply,
          IsScalarTower.algebraMap_apply (MvPolynomial (Fin d) ℂ) K L]
        exact F.algebraMap_mem _
      | add p q hp hq => rw [map_add, map_add]; exact F.add_mem hp hq
      | mul_X p j hp =>
        rw [map_mul, map_mul]
        exact F.mul_mem hp (IntermediateField.subset_adjoin _ _ ⟨j, rfl⟩)
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (Fin n) ℂ ⧸ J) z
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact F.div_mem (hB p) (hB q)

end

end GroundTheory.Heights₂.Heights.ComplexSets
