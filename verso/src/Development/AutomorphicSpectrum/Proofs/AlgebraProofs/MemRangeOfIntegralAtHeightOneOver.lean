import Mathlib
import GroundTheory.ArithmeticGeometry.ToricVarieties.KrullDomain

namespace GlobalTheory.CompanionTheory.Ar.Flat

/- English proof (translation)
Introduce `B K _ _ _ _ _ _ _ ϖ x _ hN hP`. Take `⟨N, b, hb⟩` from `hN`. Take `⟨y, hy⟩` from `GroundTheory.Arith.Toric.mem_range_of_forall_height_one (A := B) (K := K) x (fun p hp h1 => by`. Distinguish the cases in `hm : ϖ ∈ p`. Take `⟨b', c, hc, hbc⟩` from `hP p hp h1 hm`.

Conclude with `⟨b', c, hc, by rw [hbc, mul_comm]⟩`. Conclude with `⟨b, ϖ ^ N, fun h => hm (hp.mem_of_pow_mem N h), by rw [hb, map_pow, mul_comm]⟩)`. Conclude with `⟨y, hy⟩`.
-/
theorem mem_range_of_integral_at_heightOne_over :
    ∀ (B K : Type) [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]
      [Field K] [Algebra B K] [IsFractionRing B K] (ϖ : B) (x : K), ϖ ≠ 0 →
      (∃ (N : ℕ) (b : B), algebraMap B K b = algebraMap B K ϖ ^ N * x) →
      (∀ P : Ideal B, P.IsPrime → P.height = 1 → ϖ ∈ P →
        ∃ (b c : B), c ∉ P ∧ algebraMap B K b = algebraMap B K c * x) →
      ∃ b : B, algebraMap B K b = x := by
  intro B K _ _ _ _ _ _ _ ϖ x _ hN hP
  obtain ⟨N, b, hb⟩ := hN
  obtain ⟨y, hy⟩ := GroundTheory.Arith.Toric.mem_range_of_forall_height_one (A := B) (K := K) x
    (fun p hp h1 => by
      by_cases hm : ϖ ∈ p
      · obtain ⟨b', c, hc, hbc⟩ := hP p hp h1 hm
        exact ⟨b', c, hc, by rw [hbc, mul_comm]⟩
      · exact ⟨b, ϖ ^ N, fun h => hm (hp.mem_of_pow_mem N h), by rw [hb, map_pow, mul_comm]⟩)
  exact ⟨y, hy⟩

end GlobalTheory.CompanionTheory.Ar.Flat
