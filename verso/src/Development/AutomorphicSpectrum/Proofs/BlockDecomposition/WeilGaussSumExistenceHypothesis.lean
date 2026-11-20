import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WSteps
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormFormIntegralFourierFactorizationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormFormBallIntegralStabilizesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormFormBallIntegralScalingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonNormBallIntegralVanishesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonNormGaussIntegralSignStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonNormWeilConstantValueStatement

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.WGaussEx

/- English proof (translation)
Introduce `F _ _ _ _ _ _ _ χ hχ hχ1 E _ _ _ _ _ _ _ hfr hcont σ hσ η hη`. Establish `hcore` using `GlobalTheory.T.norm_form_integral_fourier_factorization F χ hχ hχ1 E hfr hcont σ hσ η hη`. Establish `hst` using `GlobalTheory.T.norm_form_ball_integral_stabilizes GlobalTheory.T.norm_form_integral_fourier_factorization F χ hχ hχ1 E hfr hcont σ hσ η hη`. Establish `hsc` using `GlobalTheory.T.norm_form_ball_integral_scaling F χ hχ hχ1 E hfr hcont σ hσ η hη`. Establish `hnon` using `GlobalTheory.T.non_norm_weil_constant_value (GlobalTheory.T.non_norm_gauss_integral_sign GlobalTheory.T.non_norm_ball_integral_vanishes) F χ hχ hχ1 E hfr hcont σ hσ η hη`.

Use `choose c n₀ hc using hst`. Use `⟨c 1, fun a Φ hΦ => ?_⟩` and prove the remaining obligations. Take `⟨n₁, h₁⟩` from `hcore a Φ hΦ`. Establish `hL` using `h₁ (min n₁ (n₀ a)) (min_le_left _ _)`. Rewrite `hL` using `[hc a _ (min_le_right _ _)]`.

Rewrite using `[hL]`. Use `congr 1`. Establish `hne : ((modulus (a : F) : ℝ) : ℂ) ≠ 0`. Establish `: (modulus (a : F) : ℝ) ≠ 0`. Simplify using `using modulus_ne_zero a.ne_zero`.

Conclude with `this` after adjusting the coercions. Distinguish the cases in `ha : ∃ t : Eˣ, Algebra.norm F (t : E) = a`. Take `⟨t, ht⟩` from `ha`. Establish `hn : nsg E (a : F) = 1`. Rewrite using `[nsg, if_pos ⟨t, ht⟩]`.

Set `m` to `min (n₀ a) (min (n₀ 1) (n₀ 1 - ord (t : E)))`. Establish `e` using `hsc t m`. Establish `e1 : ∫ u in (valBall E m : Set E), (χ (Algebra.norm F (t : E) * Algebra.norm F u) : ℂ) ∂muE E χ = c a`. Rewrite using `[ht]`. Conclude with `hc a m (min_le_left _ _)`.

Establish `e2 : ∫ u in (valBall E (m + ord (t : E)) : Set E), (χ (Algebra.norm F u) : ℂ) ∂muE E χ = c 1`. Use `hc 1 (m + ord (t : E)) (by` as an intermediate fact. Establish `: m ≤ n₀ 1 - ord (t : E)` using `(min_le_right _ _).trans (min_le_right _ _)`. Use the proof step `omega)`. Simplify using `using this`.

Rewrite `e` using `[e1, e2, ht]`. Rewrite using `[e, hn]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hn : nsg E (a : F) = -1`.

Rewrite using `[nsg, if_neg ha]`. Take `⟨m₁, hm₁, m₂, hm₂, e⟩` from `hnon a ha (min (n₀ 1) (n₀ a))`. Establish `e1 : ∫ u in (valBall E m₁ : Set E), (χ (Algebra.norm F u) : ℂ) ∂muE E χ = c 1`. Use `hc 1 m₁ (hm₁.trans (min_le_left _ _))` as an intermediate fact. Simplify using `using this`.

Rewrite `e` using `[e1, hc a m₂ (hm₂.trans (min_le_right _ _))]`. Rewrite using `[hn]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Take the linear combination `e`.
-/
theorem wGaussEx : Ad3.K.GL2LocalData.WGaussEx := by
  intro F _ _ _ _ _ _ _ χ hχ hχ1 E _ _ _ _ _ _ _ hfr hcont σ hσ η hη
  have hcore := GlobalTheory.T.norm_form_integral_fourier_factorization F χ hχ hχ1 E hfr hcont σ hσ η hη
  have hst := GlobalTheory.T.norm_form_ball_integral_stabilizes GlobalTheory.T.norm_form_integral_fourier_factorization F χ hχ hχ1 E hfr hcont σ hσ η hη
  have hsc := GlobalTheory.T.norm_form_ball_integral_scaling F χ hχ hχ1 E hfr hcont σ hσ η hη
  have hnon := GlobalTheory.T.non_norm_weil_constant_value (GlobalTheory.T.non_norm_gauss_integral_sign GlobalTheory.T.non_norm_ball_integral_vanishes) F χ hχ hχ1 E hfr hcont σ hσ η hη
  choose c n₀ hc using hst
  refine ⟨c 1, fun a Φ hΦ => ?_⟩
  obtain ⟨n₁, h₁⟩ := hcore a Φ hΦ
  have hL := h₁ (min n₁ (n₀ a)) (min_le_left _ _)
  rw [hc a _ (min_le_right _ _)] at hL
  rw [hL]
  congr 1
  have hne : ((modulus (a : F) : ℝ) : ℂ) ≠ 0 := by
    have : (modulus (a : F) : ℝ) ≠ 0 := by
      simpa using modulus_ne_zero a.ne_zero
    exact_mod_cast this
  by_cases ha : ∃ t : Eˣ, Algebra.norm F (t : E) = a
  · obtain ⟨t, ht⟩ := ha
    have hn : nsg E (a : F) = 1 := by
      rw [nsg, if_pos ⟨t, ht⟩]
    let m := min (n₀ a) (min (n₀ 1) (n₀ 1 - ord (t : E)))
    have e := hsc t m
    have e1 : ∫ u in (valBall E m : Set E), (χ (Algebra.norm F (t : E) * Algebra.norm F u) : ℂ) ∂muE E χ = c a := by
      rw [ht]; exact hc a m (min_le_left _ _)
    have e2 : ∫ u in (valBall E (m + ord (t : E)) : Set E), (χ (Algebra.norm F u) : ℂ) ∂muE E χ = c 1 := by
      have := hc 1 (m + ord (t : E)) (by
        have : m ≤ n₀ 1 - ord (t : E) := (min_le_right _ _).trans (min_le_right _ _)
        omega)
      simpa using this
    rw [e1, e2, ht] at e
    rw [e, hn]
    push_cast
    ring
  · have hn : nsg E (a : F) = -1 := by
      rw [nsg, if_neg ha]
    obtain ⟨m₁, hm₁, m₂, hm₂, e⟩ := hnon a ha (min (n₀ 1) (n₀ a))
    have e1 : ∫ u in (valBall E m₁ : Set E), (χ (Algebra.norm F u) : ℂ) ∂muE E χ = c 1 := by
      have := hc 1 m₁ (hm₁.trans (min_le_left _ _))
      simpa using this
    rw [e1, hc a m₂ (hm₂.trans (min_le_right _ _))] at e
    rw [hn]
    push_cast
    field_simp
    linear_combination e

end GlobalTheory.CompanionTheory.WGaussEx
