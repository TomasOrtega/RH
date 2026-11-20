import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.MemLocFrom

noncomputable section

namespace PI.FinKW

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst)

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem psiV_tmul (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (x : I.E) (a : Formalism.MainNotions.S.Af I.F) :
    psiV I v (x ⊗ₜ[I.F] a) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV I.F v a ⊗ₜ[I.F] x := by
  simp [psiV]

open Classical in

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Treat this case separately.
-/
theorem coeff_psiV (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (z : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)
    (j : Module.Basis.ofVectorSpaceIndex I.F I.E) :
    TensorProduct.equivFinsuppOfBasisRight (Module.Basis.ofVectorSpace I.F I.E) (psiV I v z) j =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV I.F v
        (TensorProduct.equivFinsuppOfBasisLeft (Module.Basis.ofVectorSpace I.F I.E) z j) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x a =>
    rw [psiV_tmul, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply,
      TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, map_smul]
  | add z w hz hw => simp only [map_add, Finsupp.add_apply, hz, hw]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

A detailed English derivation is pending.
-/
theorem local_vector_injective : InjV := by
  classical
  intro I z hz
  apply (TensorProduct.equivFinsuppOfBasisLeft (Module.Basis.ofVectorSpace I.F I.E)).injective
  rw [map_zero]
  refine Finsupp.ext fun j => ?_
  rw [Finsupp.zero_apply]
  have hj : ∀ v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV I.F v
      (TensorProduct.equivFinsuppOfBasisLeft (Module.Basis.ofVectorSpace I.F I.E) z j) = 0 := by
    intro v
    rw [← coeff_psiV, hz v, map_zero, Finsupp.zero_apply]

  apply RestrictedProduct.ext
  intro v
  exact hj v

end PI.FinKW
