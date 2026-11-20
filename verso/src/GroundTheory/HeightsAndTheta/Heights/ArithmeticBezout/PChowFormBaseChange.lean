import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Characterised
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsBaseChange
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LowerBoundConditional
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

/- English proof (translation)
Rewrite `hI`, the goal using `[isHomogIdeal_iff]`. Take `⟨T, hT⟩` from `(Ideal.IsHomogeneous.iff_exists _ _).mp hI`. Rewrite using `[hT, Ideal.map_span]`. Use `Ideal.homogeneous_span _ _ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨x, -, rfl⟩, rfl⟩`.

Take `⟨d, hd⟩` from `x.2`. Use `⟨d, ?_⟩` and prove the remaining obligations. Rewrite `hd`, the goal using `[mem_homogeneousSubmodule]`. Conclude with `hd.map φ`.
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
Introduce `K _ _ n k I f σ hI hf`. Establish `hJ : IsHomogIdeal (I.map (MvPolynomial.map σ))` using `isHomogIdeal_map σ hI.isHomog`. Use `⟨fun W hW => isProjPrime_of_mem_support_fundCycle hJ hW, ?_⟩` and prove the remaining obligations. Conclude with `hRed ℂ n k _ _ hJ (hRad K ℂ σ (Fin n) I hI.isPrime.isRadical) (hExt K ℂ σ n k I f hf)`.
-/
theorem ChowFormBaseChange.proof (hRad : RadicalBaseChange.Statement)
    (hExt : ChowFormExtend.Statement) (hRed : ChowFormReduced.Statement) :
    ChowFormBaseChange.Statement := by
  intro K _ _ n k I f σ hI hf
  have hJ : IsHomogIdeal (I.map (MvPolynomial.map σ)) := isHomogIdeal_map σ hI.isHomog
  refine ⟨fun W hW => isProjPrime_of_mem_support_fundCycle hJ hW, ?_⟩
  exact hRed ℂ n k _ _ hJ (hRad K ℂ σ (Fin n) I hI.isPrime.isRadical) (hExt K ℂ σ n k I f hf)

end GroundTheory.Heights₂.Heights
