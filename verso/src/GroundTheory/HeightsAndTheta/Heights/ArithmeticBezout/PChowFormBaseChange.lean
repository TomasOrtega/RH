import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Characterised
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsBaseChange
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LowerBoundConditional
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

/- English proof (translation)
Rewrite the hypotheses and the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the hypotheses and the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isHomogIdeal_map {R S : Type*} [CommRing R] [CommRing S] {n : ℕ} (φ : R →+* S)
    {I : Ideal (MvPolynomial (Fin n) R)} (hI : IsHomogIdeal I) :
    IsHomogIdeal (I.map (MvPolynomial.map φ)) := by
  rw [isHomogIdeal_iff] at hI ⊢
  obtain ⟨T, hT⟩ := (Ideal.IsHomogeneous.iff_exists _ _).mp hI
  rw [hT, Ideal.map_span]
  refine Ideal.homogeneous_span _ _ ?_
  rintro _ ⟨_, ⟨x, -, rfl⟩, rfl⟩
  obtain ⟨d, hd⟩ := x.2
  refine ⟨d, ?_⟩
  rw [mem_homogeneousSubmodule] at hd ⊢
  exact hd.map φ

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem ChowFormBaseChange.proof (hRad : RadicalBaseChange.Statement)
    (hExt : ChowFormExtend.Statement) (hRed : ChowFormReduced.Statement) :
    ChowFormBaseChange.Statement := by
  intro K _ _ n k I f σ hI hf
  have hJ : IsHomogIdeal (I.map (MvPolynomial.map σ)) := isHomogIdeal_map σ hI.isHomog
  refine ⟨fun W hW => isProjPrime_of_mem_support_fundCycle hJ hW, ?_⟩
  exact hRed ℂ n k _ _ hJ (hRad K ℂ σ (Fin n) I hI.isPrime.isRadical) (hExt K ℂ σ n k I f hf)

end GroundTheory.Heights₂.Heights
