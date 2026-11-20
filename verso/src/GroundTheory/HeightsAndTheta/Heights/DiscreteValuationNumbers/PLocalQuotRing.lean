import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsLocalCoeffRing
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

/- English proof (translation)
Introduce `R _ P U _ hP hPU`. Establish `hdisj : Disjoint (U.primeCompl : Set R) (P : Set R)` using `Set.disjoint_left.mpr fun x hx hxP => hx (hPU hxP)`. Establish `hPS : (P.map (algebraMap R (Localization.AtPrime U))).IsPrime` using `IsLocalization.isPrime_of_isPrime_disjoint U.primeCompl (Localization.AtPrime U) P hP hdisj`. Establish `hker : (P.map (algebraMap R (Localization.AtPrime U))).comap (algebraMap R (Localization.AtPrime U)) = P` using `IsLocalization.under_map_of_isPrime_disjoint U.primeCompl (Localization.AtPrime U) hP hdisj`. Use `haveI := hPS`.

Establish `hdom : IsDomain (localQuot P U)` using `Ideal.Quotient.isDomain _`. Establish `hloc : IsLocalRing (localQuot P U)` using `IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective`. Establish `hmax : U.map (localQuotMap P U) = IsLocalRing.maximalIdeal (localQuot P U)`. Rewrite using `[localQuotMap, ← Ideal.map_map, Localization.AtPrime.map_eq_maximalIdeal]`. Conclude with `IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective`.

Use `⟨hdom, hloc, fun y => ?_, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[hmax, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]`. Rewrite using `[localQuotMap, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap, hker]`.
-/
theorem LocalQuotRing.proof : LocalQuotRing.Statement.{u} := by
  intro R _ P U _ hP hPU
  have hdisj : Disjoint (U.primeCompl : Set R) (P : Set R) :=
    Set.disjoint_left.mpr fun x hx hxP => hx (hPU hxP)
  have hPS : (P.map (algebraMap R (Localization.AtPrime U))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint U.primeCompl (Localization.AtPrime U) P hP hdisj
  have hker : (P.map (algebraMap R (Localization.AtPrime U))).comap
      (algebraMap R (Localization.AtPrime U)) = P :=
    IsLocalization.under_map_of_isPrime_disjoint U.primeCompl (Localization.AtPrime U) hP hdisj
  haveI := hPS
  have hdom : IsDomain (localQuot P U) := Ideal.Quotient.isDomain _
  have hloc : IsLocalRing (localQuot P U) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hmax : U.map (localQuotMap P U) = IsLocalRing.maximalIdeal (localQuot P U) := by
    rw [localQuotMap, ← Ideal.map_map, Localization.AtPrime.map_eq_maximalIdeal]
    exact IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  refine ⟨hdom, hloc, fun y => ?_, fun x => ?_⟩
  · rw [hmax, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
  · rw [localQuotMap, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap, hker]

end GroundTheory.Heights₂.Heights.NumbersDVR
