import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsLocalCoeffRing
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem LocalQuotPrimes.proof : LocalQuotPrimes.Statement.{u} := by
  intro R _ P U _ hPU
  let S := Localization.AtPrime U
  let PS : Ideal S := P.map (algebraMap R S)
  have hsurj : Function.Surjective (Ideal.Quotient.mk PS) := Ideal.Quotient.mk_surjective
  have hmap : ∀ I : Ideal R,
      I.map (localQuotMap P U) = (I.map (algebraMap R S)).map (Ideal.Quotient.mk PS) := by
    intro I
    rw [Ideal.map_map]
    rfl
  have hcomap : ∀ J : Ideal (localQuot P U),
      J.comap (localQuotMap P U) = (J.comap (Ideal.Quotient.mk PS)).comap (algebraMap R S) := by
    intro J
    rw [Ideal.comap_comap]
    rfl
  refine ⟨fun W hW hPW hWU => ?_, fun p hp => ?_⟩
  · have hdisj : Disjoint (U.primeCompl : Set R) W := by
      rw [Set.disjoint_left]
      intro x hx hxW
      exact hx (hWU hxW)
    have hWS : (W.map (algebraMap R S)).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint U.primeCompl S W hW hdisj
    have hWSc : (W.map (algebraMap R S)).comap (algebraMap R S) = W :=
      IsLocalization.under_map_of_isPrime_disjoint U.primeCompl S hW hdisj
    have hker : RingHom.ker (Ideal.Quotient.mk PS) ≤ W.map (algebraMap R S) := by
      rw [Ideal.mk_ker]
      exact Ideal.map_mono hPW
    refine ⟨?_, ?_⟩
    · rw [hmap]
      exact Ideal.map_isPrime_of_surjective hsurj hker
    · rw [hmap, hcomap, Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot,
        sup_eq_left.mpr hker, hWSc]
  · let q : Ideal S := p.comap (Ideal.Quotient.mk PS)
    have hq : q.IsPrime := Ideal.comap_isPrime _ p
    have hq' := (IsLocalization.isPrime_iff_isPrime_disjoint U.primeCompl S q).mp hq
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rw [Ideal.mem_comap]
      have h0 : localQuotMap P U x = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hx)
      rw [h0]
      exact p.zero_mem
    · intro x hx
      by_contra hxU
      rw [hcomap] at hx
      exact Set.disjoint_left.mp hq'.2 (show x ∈ U.primeCompl from hxU) hx
    · rw [hmap, hcomap]
      have hloc : (q.comap (algebraMap R S)).map (algebraMap R S) = q :=
        IsLocalization.map_under U.primeCompl S q
      rw [hloc]
      exact Ideal.map_comap_of_surjective _ hsurj p

end GroundTheory.Heights₂.Heights.NumbersDVR
