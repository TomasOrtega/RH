import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem map_eq_maximalIdeal_of_isRadical {A : Type*} [CommRing A] {J W : Ideal A} [W.IsPrime]
    (hJ : J.IsRadical) (hW : W ∈ J.minimalPrimes) :
    J.map (algebraMap A (Localization.AtPrime W)) = IsLocalRing.maximalIdeal (Localization.AtPrime W) := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal W (Localization.AtPrime W),
    ← IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes (Localization.AtPrime W) W J hW,
    ← IsLocalization.map_radical W.primeCompl (Localization.AtPrime W) J, hJ.radical]

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression.
-/
theorem localMult_eq_one_of_isRadical {A : Type*} [CommRing A] {J W : Ideal A} (hJ : J.IsRadical)
    (hW : W ∈ J.minimalPrimes) : localMult J W = 1 := by
  have hWp : W.IsPrime := hW.1.1
  unfold localMult
  rw [dif_pos hWp, map_eq_maximalIdeal_of_isRadical hJ hW]
  have : IsSimpleModule (Localization.AtPrime W)
      (Localization.AtPrime W ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime W)) :=
    isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp (IsLocalRing.maximalIdeal.isMaximal _))
  rw [Module.length_eq_one]
  rfl

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem fundCycle_apply_of_isRadical {R : Type*} [CommRing R] [IsNoetherianRing R] {n : ℕ}
    {J : Ideal (MvPolynomial (Fin n) R)} (hJ : J.IsRadical) {W : Ideal (MvPolynomial (Fin n) R)}
    (hW : W ∈ (fundCycle J).support) : fundCycle J W = 1 := by
  classical
  have hval : fundCycle J W ≠ 0 := Finsupp.mem_support_iff.mp hW
  have hrel : W ∈ relComps J := by
    by_contra h
    apply hval
    unfold fundCycle
    rw [Finsupp.onFinset_apply, if_neg h]
  unfold fundCycle
  rw [Finsupp.onFinset_apply, if_pos hrel]
  exact localMult_eq_one_of_isRadical hJ hrel.1

end GroundTheory.Heights₂.Heights
