import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsLocalCoeffLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

/- English proof (translation)
Introduce `A _ _ _ x hx W`. Prove the components needed by the constructor for the conclusion. Introduce `hW`. Establish `hWp : W.IsPrime` using `hW.isPrime`. Establish `hxW : x ∈ W` using `hW.1.2 (Ideal.mem_span_singleton_self x)`.

Use `⟨hWp, ?_, hxW⟩` and prove the remaining obligations. Establish `hle : W.height ≤ 1` using `Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {x}) W hW`. Establish `hne : W.height ≠ 0`. Rewrite using `[Ne, Ideal.height_eq_zero_iff_eq_bot]`. Introduce `hbot`.

Rewrite `hxW` using `[hbot, Ideal.mem_bot]`. Conclude with `hx hxW`. Conclude with `le_antisymm hle (Order.one_le_iff_ne_zero.mpr hne)`. Introduce and unpack `⟨hWp, hh, hxW⟩`. Use `⟨⟨hWp, (Ideal.span_singleton_le_iff_mem W).mpr hxW⟩, ?_⟩` and prove the remaining obligations.

Introduce and unpack `Q ⟨hQp, hxQ⟩ hQW`. Assume the negation of the conclusion as `hWQ`. Establish `hlt : Q < W` using `lt_of_le_of_ne hQW (fun h => hWQ (h ▸ le_refl Q))`. Establish `hfin : W.FiniteHeight` using `W.finiteHeight_iff.mpr (Or.inr (by rw [hh]; exact ENat.one_ne_top))`. Establish `hQh : Q.height < 1` using `hh ▸ Ideal.height_strict_mono_of_isPrime_of_isPrime hlt`.

Establish `hQ0 : Q.height = 0` using `Order.lt_one_iff.mp hQh`. Rewrite `hQ0` using `[Ideal.height_eq_zero_iff_eq_bot]`. Establish `hx0 : x ∈ (⊥ : Ideal A)` using `hQ0 ▸ (Ideal.span_singleton_le_iff_mem Q).mp hxQ`. Conclude with `hx ((Ideal.mem_bot).mp hx0)`.
-/
theorem MinimalPrimesSpanSingleton.proof : MinimalPrimesSpanSingleton.Statement.{u} := by
  intro A _ _ _ x hx W
  constructor
  · intro hW
    have hWp : W.IsPrime := hW.isPrime
    have hxW : x ∈ W := hW.1.2 (Ideal.mem_span_singleton_self x)
    refine ⟨hWp, ?_, hxW⟩
    have hle : W.height ≤ 1 :=
      Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {x}) W hW
    have hne : W.height ≠ 0 := by
      rw [Ne, Ideal.height_eq_zero_iff_eq_bot]
      intro hbot
      rw [hbot, Ideal.mem_bot] at hxW
      exact hx hxW
    exact le_antisymm hle (Order.one_le_iff_ne_zero.mpr hne)
  · rintro ⟨hWp, hh, hxW⟩
    refine ⟨⟨hWp, (Ideal.span_singleton_le_iff_mem W).mpr hxW⟩, ?_⟩
    rintro Q ⟨hQp, hxQ⟩ hQW
    by_contra hWQ
    have hlt : Q < W := lt_of_le_of_ne hQW (fun h => hWQ (h ▸ le_refl Q))
    have hfin : W.FiniteHeight := W.finiteHeight_iff.mpr (Or.inr (by rw [hh]; exact ENat.one_ne_top))
    have hQh : Q.height < 1 := hh ▸ Ideal.height_strict_mono_of_isPrime_of_isPrime hlt
    have hQ0 : Q.height = 0 := Order.lt_one_iff.mp hQh
    rw [Ideal.height_eq_zero_iff_eq_bot] at hQ0
    have hx0 : x ∈ (⊥ : Ideal A) := hQ0 ▸ (Ideal.span_singleton_le_iff_mem Q).mp hxQ
    exact hx ((Ideal.mem_bot).mp hx0)

end GroundTheory.Heights₂.Heights.NumbersDVR
