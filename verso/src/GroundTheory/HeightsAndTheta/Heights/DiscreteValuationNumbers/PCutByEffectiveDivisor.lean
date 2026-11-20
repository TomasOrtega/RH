import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Statements
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsMultiHomogIdealSpanSingleton
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

/- English proof (translation)
Take `⟨bf, bg, hf, hg, hb⟩` from `hD.degrees`. Use `IsVerticalDivisor.of_unit_off_special ⟨bf, bg, ?_, hg, hb⟩ ?_ hD.den_not_mem ?_` and prove the remaining obligations. Establish `h0 : IsMultiHomog (C ϖ ^ n : MRing ι O) 0`. Rewrite using `[← map_pow]`. Conclude with `isWeightedHomogeneous_C _ _`.

Use `h0.mul hf` as an intermediate fact. Rewrite `this` using `[zero_add]`. Then use the resulting hypothesis. Conclude with `hH.mul_notMem (fun h => hϖ (hH.mem_of_pow_mem n h)) hD.num_not_mem`. Introduce `W hW hHW hrel hϖW`. Take `⟨u, v, hu, hv, huv⟩` from `hD.unit_off_special W hW hHW hrel hϖW`.

Use `⟨u, C ϖ ^ n * v, hu, hW.mul_notMem (fun h => hϖW (hW.mem_of_pow_mem n h)) hv, ?_⟩` and prove the remaining obligations. Establish `e : u * (C ϖ ^ n * f) - C ϖ ^ n * v * g = C ϖ ^ n * (u * f - v * g)` using `by ring`. Rewrite using `[e]`. Conclude with `H.mul_mem_left _ huv`.
-/
theorem IsVerticalDivisor.uniformiser_pow_mul {K : Type*} [DecidableEq K] {ι : K → Type*}
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {H : Ideal (MRing ι O)}
    [hH : H.IsPrime] {ϖ : O} (hϖ : (C ϖ : MRing ι O) ∉ H) {b : K → ℤ} {f g : MRing ι O}
    (hD : IsVerticalDivisor H ϖ b f g) (n : ℕ) :
    IsVerticalDivisor H ϖ b (C ϖ ^ n * f) g := by
  obtain ⟨bf, bg, hf, hg, hb⟩ := hD.degrees
  refine IsVerticalDivisor.of_unit_off_special ⟨bf, bg, ?_, hg, hb⟩ ?_ hD.den_not_mem ?_
  · have h0 : IsMultiHomog (C ϖ ^ n : MRing ι O) 0 := by
      rw [← map_pow]
      exact isWeightedHomogeneous_C _ _
    have := h0.mul hf
    rwa [zero_add] at this
  · exact hH.mul_notMem (fun h => hϖ (hH.mem_of_pow_mem n h)) hD.num_not_mem
  · intro W hW hHW hrel hϖW
    obtain ⟨u, v, hu, hv, huv⟩ := hD.unit_off_special W hW hHW hrel hϖW
    refine ⟨u, C ϖ ^ n * v, hu, hW.mul_notMem (fun h => hϖW (hW.mem_of_pow_mem n h)) hv, ?_⟩
    have e : u * (C ϖ ^ n * f) - C ϖ ^ n * v * g = C ϖ ^ n * (u * f - v * g) := by ring
    rw [e]
    exact H.mul_mem_left _ huv

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hH L`. Take `⟨n, hEff⟩` from `h4 O ϖ hϖ K ι P (d + 1) hP b f g hD`. Establish `hH' : ∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → IsVerticalDivisor H ϖ b (C ϖ ^ n * f) g`. Introduce `H hsH hϖH`. Use `(le_and_isRelevant_of_divCycle_ne_zero hsH).1` as an intermediate fact.

Conclude with `(hH H hsH hϖH).uniformiser_pow_mul hϖH n`. Establish `e1` using `h1 O ϖ hϖ K ι P d hP b (C ϖ ^ n * f) g hEff c s hs hsP hH' L`. Establish `e2` using `h2 O ϖ hϖ K ι P d hP c s hs hsP L`. Conclude with `h3 O ϖ hϖ K ι P d hP b f g hD c s hs hsP hH L n e1 e2`.
-/
theorem CutByEffectiveDivisor.proof (h1 : EffectiveCase.Statement.{u})
    (h2 : UniformiserCase.Statement.{u}) (h3 : ShiftByUniformiser.Statement.{u})
    (h4 : EffectiveShift.Statement.{u}) : CutByEffectiveDivisor.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hH L
  obtain ⟨n, hEff⟩ := h4 O ϖ hϖ K ι P (d + 1) hP b f g hD
  have hH' : ∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H →
      IsVerticalDivisor H ϖ b (C ϖ ^ n * f) g := by
    intro H hsH hϖH
    have := (le_and_isRelevant_of_divCycle_ne_zero hsH).1
    exact (hH H hsH hϖH).uniformiser_pow_mul hϖH n
  have e1 := h1 O ϖ hϖ K ι P d hP b (C ϖ ^ n * f) g hEff c s hs hsP hH' L
  have e2 := h2 O ϖ hϖ K ι P d hP c s hs hsP L
  exact h3 O ϖ hϖ K ι P d hP b f g hD c s hs hsP hH L n e1 e2

end

end GroundTheory.Heights₂.Heights.NumbersDVR
