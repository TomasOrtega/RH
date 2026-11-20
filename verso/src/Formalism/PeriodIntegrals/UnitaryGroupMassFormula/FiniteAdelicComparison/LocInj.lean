import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.MemLocFrom

noncomputable section

namespace PI.FinKW

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst)

/- English proof (translation)
Simplify using `[psiV]`.
-/
theorem psiV_tmul (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (x : I.E) (a : Formalism.MainNotions.S.Af I.F) :
    psiV I v (x ⊗ₜ[I.F] a) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV I.F v a ⊗ₜ[I.F] x := by
  simp [psiV]

open Classical in

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x a`. Rewrite using `[psiV_tmul, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, map_smul]`. Consider the case `add z w hz hw => simp only [map_add, Finsupp.add_apply, hz, hw]`.
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
Introduce `I z hz`. Apply `(TensorProduct.equivFinsuppOfBasisLeft (Module.Basis.ofVectorSpace I.F I.E)).injective` to reduce the goal to its premises. Rewrite using `[map_zero]`. Use `Finsupp.ext fun j => ?_` and prove the remaining obligations. Rewrite using `[Finsupp.zero_apply]`.

Establish `hj : ∀ v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV I.F v (TensorProduct.equivFinsuppOfBasisLeft (Module.Basis.ofVectorSpace I.F I.E) z j) = 0`. Introduce `v`. Rewrite using `[← coeff_psiV, hz v, map_zero, Finsupp.zero_apply]`. Apply `RestrictedProduct.ext` to reduce the goal to its premises. Introduce `v`.

Conclude with `hj v`.
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
