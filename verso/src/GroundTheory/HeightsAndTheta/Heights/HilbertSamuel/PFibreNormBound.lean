import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreNormBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjAvoidingForm
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreRepresentatives
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreNormMax
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsMetricMaxComparison
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

/- English proof (translation)
Introduce `K _ ι _ Ω _ y D A df f hV hB hA hf hfP`. Take `⟨e, L, G, he, hL, hL0, hG, hGf⟩` from `h₁ K ι Ω y D df f hV hf hfP`. Take `⟨n, c, B, hn, hB1, hF⟩` from `h₃ K ι Ω y D A.a e L hV hB he hL hL0`. Take `⟨C, hC, hAC⟩` from `h₄ K ι A hA`. Use `choose S hS₁ hS₂ using h₂ K ι Ω y D e L he hL hL0`.

Use `⟨n, c, B * C ^ n, G, S, hn, one_le_mul_of_one_le_of_one_le hB1 (one_le_pow₀ hC), hG, ?_, ?_⟩` and prove the remaining obligations. Introduce `ζ _ hGζ z hz`. Take `⟨hzP, t, ht⟩` from `hS₁ ζ z hz`. Conclude with `⟨hzP, hGf ζ hGζ z hzP ⟨t, ht⟩⟩`. Introduce `τ u hu hu0`.

Take `⟨F, hF0, hFdeg, hFb⟩` from `hF τ u hu hu0`. Use `⟨F, hF0, hFdeg, fun ζ hζ _ M hM hrep => ?_⟩` and prove the remaining obligations. Establish `hC0 : (0 : ℝ) ≤ C` using `zero_le_one.trans hC`. Establish `key` using `hFb ζ hζ (S ζ) (hS₂ ζ) (M * C ^ τ) (by positivity) (fun z hz => by`. Take `⟨dg, dh, g, h, hg, hh, hd, hgh, hz0, hle⟩` from `hrep z hz`.

Use `⟨dg, dh, g, h, hg, hh, hd, hgh, hz0, ?_⟩` and prove the remaining obligations. Establish `hzb` using `(hS₁ ζ z hz).1.1`. Establish `h0 : 0 ≤ A.h z` using `(A.pos z hzb).le`. Combine the equalities or inequalities in the displayed calculation. Conclude with `hAC z hzb`.

Use `_ = M * C ^ τ * (HermLine.ofMetrics (fun k => maxMetric ℂ (ι k)) A.a).h z ^ τ * ‖eval z (map (Int.castRingHom ℂ) h)‖ := by ring)`. Establish `hB0 : (0 : ℝ) ≤ B` using `zero_le_one.trans hB1`. Establish `hpow : C ^ (τ * n) ≤ C ^ (n * (τ + 1))` using `pow_le_pow_right₀ hC (by rw [Nat.mul_comm n]; exact Nat.mul_le_mul_right n (Nat.le_succ τ))`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem FibreNormBound.proof (h₁ : ProjAvoidingForm.Statement) (h₂ : FibreRepresentatives.Statement)
    (h₃ : FibreNormMax.Statement) (h₄ : MetricMaxComparison.Statement) : FibreNormBound.Statement := by
  intro K _ ι _ Ω _ y D A df f hV hB hA hf hfP
  obtain ⟨e, L, G, he, hL, hL0, hG, hGf⟩ := h₁ K ι Ω y D df f hV hf hfP
  obtain ⟨n, c, B, hn, hB1, hF⟩ := h₃ K ι Ω y D A.a e L hV hB he hL hL0
  obtain ⟨C, hC, hAC⟩ := h₄ K ι A hA
  choose S hS₁ hS₂ using h₂ K ι Ω y D e L he hL hL0
  refine ⟨n, c, B * C ^ n, G, S, hn, one_le_mul_of_one_le_of_one_le hB1 (one_le_pow₀ hC), hG, ?_, ?_⟩
  · intro ζ _ hGζ z hz
    obtain ⟨hzP, t, ht⟩ := hS₁ ζ z hz
    exact ⟨hzP, hGf ζ hGζ z hzP ⟨t, ht⟩⟩
  · intro τ u hu hu0
    obtain ⟨F, hF0, hFdeg, hFb⟩ := hF τ u hu hu0
    refine ⟨F, hF0, hFdeg, fun ζ hζ _ M hM hrep => ?_⟩
    have hC0 : (0 : ℝ) ≤ C := zero_le_one.trans hC
    have key := hFb ζ hζ (S ζ) (hS₂ ζ) (M * C ^ τ) (by positivity) (fun z hz => by
      obtain ⟨dg, dh, g, h, hg, hh, hd, hgh, hz0, hle⟩ := hrep z hz
      refine ⟨dg, dh, g, h, hg, hh, hd, hgh, hz0, ?_⟩
      have hzb := (hS₁ ζ z hz).1.1
      have h0 : 0 ≤ A.h z := (A.pos z hzb).le
      calc ‖eval z (map (Int.castRingHom ℂ) g)‖
          ≤ M * A.h z ^ τ * ‖eval z (map (Int.castRingHom ℂ) h)‖ := hle
        _ ≤ M * (C * (HermLine.ofMetrics (fun k => maxMetric ℂ (ι k)) A.a).h z) ^ τ *
              ‖eval z (map (Int.castRingHom ℂ) h)‖ := by
            gcongr
            exact hAC z hzb
        _ = M * C ^ τ * (HermLine.ofMetrics (fun k => maxMetric ℂ (ι k)) A.a).h z ^ τ *
              ‖eval z (map (Int.castRingHom ℂ) h)‖ := by ring)
    have hB0 : (0 : ℝ) ≤ B := zero_le_one.trans hB1
    have hpow : C ^ (τ * n) ≤ C ^ (n * (τ + 1)) :=
      pow_le_pow_right₀ hC (by rw [Nat.mul_comm n]; exact Nat.mul_le_mul_right n (Nat.le_succ τ))
    calc ‖eval ζ (map (Int.castRingHom ℂ) F)‖ ≤ B ^ (τ + 1) * (M * C ^ τ) ^ n := key
      _ = B ^ (τ + 1) * M ^ n * C ^ (τ * n) := by rw [mul_pow, ← pow_mul]; ring
      _ ≤ B ^ (τ + 1) * M ^ n * C ^ (n * (τ + 1)) := by gcongr
      _ = (B * C ^ n) ^ (τ + 1) * M ^ n := by rw [mul_pow, ← pow_mul]; ring

end GroundTheory.Heights₂.Heights.HilbertSamuel
