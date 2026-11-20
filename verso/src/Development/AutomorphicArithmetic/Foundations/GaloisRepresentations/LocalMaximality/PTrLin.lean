import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.productCup_of_system.trLin_of :
    TrLin := by
  intro V _ _ ι _ φ v hv
  have hfin : FiniteDimensional ℂ V := by
    refine Module.Finite.of_surjective (Fintype.linearCombination ℂ v) ?_
    intro y
    exact ⟨fun k => φ k y, by rw [Fintype.linearCombination_apply]; exact (hv y).symm⟩
  refine ⟨hfin, fun u => ?_⟩
  have hu : u = ∑ k, dualTensorHom ℂ V V (φ k ⊗ₜ u (v k)) := by
    ext y
    rw [LinearMap.sum_apply]
    simp only [dualTensorHom_apply]
    conv_lhs => rw [hv y]
    rw [map_sum]
    simp [map_smul]
  conv_lhs => rw [hu]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.trace_eq_contract_apply]
  simp
