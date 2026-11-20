import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsLocalCoeffRing
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

/- English proof (translation)
Introduce `R _ P U _ hPU`. Set `S` to `Localization.AtPrime U`. Set `PS : Ideal S` to `P.map (algebraMap R S)`. Establish `hsurj : Function.Surjective (Ideal.Quotient.mk PS)` using `Ideal.Quotient.mk_surjective`. Establish `hmap : ∀ I : Ideal R, I.map (localQuotMap P U) = (I.map (algebraMap R S)).map (Ideal.Quotient.mk PS)`.

Introduce `I`. Rewrite using `[Ideal.map_map]`. Both sides reduce to the same expression. Establish `hcomap : ∀ J : Ideal (localQuot P U), J.comap (localQuotMap P U) = (J.comap (Ideal.Quotient.mk PS)).comap (algebraMap R S)`. Introduce `J`.

Rewrite using `[Ideal.comap_comap]`. Both sides reduce to the same expression. Use `⟨fun W hW hPW hWU => ?_, fun p hp => ?_⟩` and prove the remaining obligations. Establish `hdisj : Disjoint (U.primeCompl : Set R) W`. Rewrite using `[Set.disjoint_left]`.

Introduce `x hx hxW`. Conclude with `hx (hWU hxW)`. Establish `hWS : (W.map (algebraMap R S)).IsPrime` using `IsLocalization.isPrime_of_isPrime_disjoint U.primeCompl S W hW hdisj`. Establish `hWSc : (W.map (algebraMap R S)).comap (algebraMap R S) = W` using `IsLocalization.under_map_of_isPrime_disjoint U.primeCompl S hW hdisj`. Establish `hker : RingHom.ker (Ideal.Quotient.mk PS) ≤ W.map (algebraMap R S)`.

Rewrite using `[Ideal.mk_ker]`. Conclude with `Ideal.map_mono hPW`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hmap]`. Conclude with `Ideal.map_isPrime_of_surjective hsurj hker`.

Rewrite using `[hmap, hcomap, Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hker, hWSc]`. Set `q : Ideal S` to `p.comap (Ideal.Quotient.mk PS)`. Establish `hq : q.IsPrime` using `Ideal.comap_isPrime _ p`. Establish `hq'` using `(IsLocalization.isPrime_iff_isPrime_disjoint U.primeCompl S q).mp hq`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `x hx`. Rewrite using `[Ideal.mem_comap]`. Establish `h0 : localQuotMap P U x = 0` using `Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hx)`. Rewrite using `[h0]`. Conclude with `p.zero_mem`.

Introduce `x hx`. Assume the negation of the conclusion as `hxU`. Rewrite `hx` using `[hcomap]`. Conclude with `Set.disjoint_left.mp hq'.2 (show x ∈ U.primeCompl from hxU) hx`. Rewrite using `[hmap, hcomap]`.

Establish `hloc : (q.comap (algebraMap R S)).map (algebraMap R S) = q` using `IsLocalization.map_under U.primeCompl S q`. Rewrite using `[hloc]`. Conclude with `Ideal.map_comap_of_surjective _ hsurj p`.
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
