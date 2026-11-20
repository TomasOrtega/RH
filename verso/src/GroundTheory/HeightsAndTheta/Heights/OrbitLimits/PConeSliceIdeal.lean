import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StConeSliceIdeal
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartHomogenise
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PGoodChartZeroSet
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

/- English proof (translation)
Introduce `n C t V hC hV f hf`. Establish `hℓ : (linForm t).IsHomogeneous 1` using `IsHomogeneous.sum _ _ _ fun _ _ => isHomogeneous_C_mul_X _ _`. Take `⟨G, D, hG, hGf⟩` from `ChartHomogenise.exists_homogeneous_sub_mem_span (linForm t) f hℓ`. Establish `hLG : linForm t * G ∈ V`. Use `hV ?_` and prove the remaining obligations.

Rewrite using `[mem_vanishingIdeal_iff]`. Introduce `c hc`. Use `show eval c (linForm t * G) = 0`. Rewrite using `[map_mul]`. Distinguish the cases in `hl : eval c (linForm t) = 0`.

Rewrite using `[hl, zero_mul]`. Use `set l := eval c (linForm t)`. Establish `hsl : eval (l⁻¹ • c) (linForm t) = 1`. Rewrite using `[GoodChartZeroSet.eval_smul_of_isHomogeneous hℓ, pow_one, inv_mul_cancel₀ hl]`. Establish `hmem : l⁻¹ • c ∈ {x | x ∈ C ∧ eval x (linForm t) = 1}` using `⟨hC c hc _ (inv_ne_zero hl), hsl⟩`.

Establish `hf0 : eval (l⁻¹ • c) f = 0` using `(mem_vanishingIdeal_iff.mp hf) _ hmem`. Take `⟨q, hq⟩` from `Ideal.mem_span_singleton.mp hGf`. Establish `hGv : eval (l⁻¹ • c) G = 0`. Establish `h` using `congrArg (eval (l⁻¹ • c)) hq`. Rewrite `h` using `[map_sub, map_mul, map_sub, hsl, hf0, map_one]`.

Simplify using `using h`. Establish `hc' : c = l • (l⁻¹ • c)` using `by rw [smul_smul, mul_inv_cancel₀ hl, one_smul]`. Rewrite using `[hc', GoodChartZeroSet.eval_smul_of_isHomogeneous hG, hGv, mul_zero, mul_zero]`. Establish `e : f = linForm t * G - (linForm t - 1) * G - (G - f)` using `by ring`. Rewrite using `[e]`.

Use `Ideal.sub_mem _ (Ideal.sub_mem _ (Ideal.mem_sup_left hLG) ?_) (Ideal.mem_sup_right hGf)` and prove the remaining obligations. Conclude with `Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))`.
-/
theorem ConeSliceIdeal.proof : ConeSliceIdeal.Statement := by
  intro n C t V hC hV f hf
  have hℓ : (linForm t).IsHomogeneous 1 :=
    IsHomogeneous.sum _ _ _ fun _ _ => isHomogeneous_C_mul_X _ _
  obtain ⟨G, D, hG, hGf⟩ := ChartHomogenise.exists_homogeneous_sub_mem_span (linForm t) f hℓ
  have hLG : linForm t * G ∈ V := by
    refine hV ?_
    rw [mem_vanishingIdeal_iff]
    intro c hc
    show eval c (linForm t * G) = 0
    rw [map_mul]
    by_cases hl : eval c (linForm t) = 0
    · rw [hl, zero_mul]
    · set l := eval c (linForm t)
      have hsl : eval (l⁻¹ • c) (linForm t) = 1 := by
        rw [GoodChartZeroSet.eval_smul_of_isHomogeneous hℓ, pow_one, inv_mul_cancel₀ hl]
      have hmem : l⁻¹ • c ∈ {x | x ∈ C ∧ eval x (linForm t) = 1} :=
        ⟨hC c hc _ (inv_ne_zero hl), hsl⟩
      have hf0 : eval (l⁻¹ • c) f = 0 := (mem_vanishingIdeal_iff.mp hf) _ hmem
      obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hGf
      have hGv : eval (l⁻¹ • c) G = 0 := by
        have h := congrArg (eval (l⁻¹ • c)) hq
        rw [map_sub, map_mul, map_sub, hsl, hf0, map_one] at h
        simpa using h
      have hc' : c = l • (l⁻¹ • c) := by rw [smul_smul, mul_inv_cancel₀ hl, one_smul]
      rw [hc', GoodChartZeroSet.eval_smul_of_isHomogeneous hG, hGv, mul_zero, mul_zero]
  have e : f = linForm t * G - (linForm t - 1) * G - (G - f) := by ring
  rw [e]
  refine Ideal.sub_mem _ (Ideal.sub_mem _ (Ideal.mem_sup_left hLG) ?_) (Ideal.mem_sup_right hGf)
  exact Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))

end GroundTheory.Heights₂.Heights
