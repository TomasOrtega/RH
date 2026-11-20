import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCMRingUnmixed
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.CMDepthAssoc
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.HeightCoheightQuotient
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing RingTheory.Sequence

/- English proof (translation)
Introduce `A _ _ p hp`. Take `⟨rs, hm, hreg, hdim⟩` from `IsCohenMacaulayLocalRing.exists_isWeaklyRegular (B := A)`. Take `⟨hprime, y, hy⟩` from `isAssociatedPrime_iff.mp hp`. Establish `hy0 : y ≠ 0`. Introduce and unpack `rfl`.

Apply `hprime.ne_top` to reduce the goal to its premises. Rewrite using `[hy, eq_top_iff]`. Introduce `r _`. Rewrite using `[Submodule.mem_colon_singleton, smul_zero]`. Conclude with `Submodule.zero_mem _`.

Establish `hD` using `length_le_ringKrullDim_quotient_colon rs y hy0 hm hreg`. Rewrite `hD` using `[← hy, ← hdim]`. Establish `heq : ringKrullDim (A ⧸ p) = ringKrullDim A` using `le_antisymm (ringKrullDim_le_of_surjective _ Ideal.Quotient.mk_surjective) hD`. Use `⟨⟨⟨hprime, bot_le⟩, fun q hq hqp => ?_⟩, heq⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hpq`.

Establish `hlt : q < p` using `lt_of_le_of_ne hqp fun h => hpq (h ▸ le_rfl)`. Establish `hq' : q.IsPrime` using `hq.1`. Establish `h1` using `Order.coheight_add_one_le (α := PrimeSpectrum A) (a := ⟨p, hprime⟩) (b := ⟨q, hq'⟩) hlt`. Establish `h2 : ringKrullDim (A ⧸ q) ≤ ringKrullDim A` using `ringKrullDim_le_of_surjective _ Ideal.Quotient.mk_surjective`. Rewrite `h2` using `[ringKrullDim_quotient_eq_coheight, hdim]`.

Rewrite `heq` using `[ringKrullDim_quotient_eq_coheight, hdim]`. Establish `e1 : Order.coheight (⟨p, hprime⟩ : PrimeSpectrum A) = (rs.length : ℕ∞)` using `by exact_mod_cast heq`. Establish `e2 : Order.coheight (⟨q, hq'⟩ : PrimeSpectrum A) ≤ (rs.length : ℕ∞)` using `by exact_mod_cast h2`. Rewrite `h1` using `[e1]`. Establish `h3 : ((rs.length + 1 : ℕ) : ℕ∞) ≤ (rs.length : ℕ)` using `by exact_mod_cast h1.trans e2`.

Establish `h4 : rs.length + 1 ≤ rs.length` using `by exact_mod_cast h3`. Use linear arithmetic over natural numbers and integers.
-/
theorem CMRingUnmixed.proof : CMRingUnmixed.Statement := by
  intro A _ _ p hp
  obtain ⟨rs, hm, hreg, hdim⟩ := IsCohenMacaulayLocalRing.exists_isWeaklyRegular (B := A)
  obtain ⟨hprime, y, hy⟩ := isAssociatedPrime_iff.mp hp
  have hy0 : y ≠ 0 := by
    rintro rfl
    apply hprime.ne_top
    rw [hy, eq_top_iff]
    intro r _
    rw [Submodule.mem_colon_singleton, smul_zero]
    exact Submodule.zero_mem _
  have hD := length_le_ringKrullDim_quotient_colon rs y hy0 hm hreg
  rw [← hy, ← hdim] at hD
  have heq : ringKrullDim (A ⧸ p) = ringKrullDim A :=
    le_antisymm (ringKrullDim_le_of_surjective _ Ideal.Quotient.mk_surjective) hD
  refine ⟨⟨⟨hprime, bot_le⟩, fun q hq hqp => ?_⟩, heq⟩
  by_contra hpq
  have hlt : q < p := lt_of_le_of_ne hqp fun h => hpq (h ▸ le_rfl)
  have hq' : q.IsPrime := hq.1
  have h1 := Order.coheight_add_one_le (α := PrimeSpectrum A) (a := ⟨p, hprime⟩) (b := ⟨q, hq'⟩) hlt
  have h2 : ringKrullDim (A ⧸ q) ≤ ringKrullDim A :=
    ringKrullDim_le_of_surjective _ Ideal.Quotient.mk_surjective
  rw [ringKrullDim_quotient_eq_coheight, hdim] at h2
  rw [ringKrullDim_quotient_eq_coheight, hdim] at heq
  have e1 : Order.coheight (⟨p, hprime⟩ : PrimeSpectrum A) = (rs.length : ℕ∞) := by exact_mod_cast heq
  have e2 : Order.coheight (⟨q, hq'⟩ : PrimeSpectrum A) ≤ (rs.length : ℕ∞) := by exact_mod_cast h2
  rw [e1] at h1
  have h3 : ((rs.length + 1 : ℕ) : ℕ∞) ≤ (rs.length : ℕ) := by exact_mod_cast h1.trans e2
  have h4 : rs.length + 1 ≤ rs.length := by exact_mod_cast h3
  omega

end GroundTheory.Heights₂.Heights
