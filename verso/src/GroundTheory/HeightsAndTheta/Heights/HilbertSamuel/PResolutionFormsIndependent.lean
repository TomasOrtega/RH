import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionFormsIndependent
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNonvanishingDense
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory

noncomputable section

/- English proof (translation)
Introduce `D Ω _ _ κ _ d n r b hb a ha`. Take `⟨g, hgJ, hgP⟩` from `SetLike.not_le_iff_exists.1 d.R.nondeg`. Use `set F : (Ix κ → ℂ) → ℂ := fun z => ∑ k, a k * secFun (b k) z with hF`. Establish `hFc : Continuous F` using `continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_secFun _)`. Establish `hoff : ∀ z, z ∈ mcPts (ι` using `GlobalTheory κ) (coordIdeal ℤ d.x) → eval z (map (Int.castRingHom ℂ) g) ≠ 0 → F z = 0 := by`.

Introduce `z hz hgz`. Take `⟨y, c, hc, hyz⟩` from `d.R.surj z hz (fun hJ => hgz (hJ.2 g hgJ))`. Establish `h1 : resPt d y = c () • z`. Use function extensionality and compare the values at `p`. Simplify using `[resPt, hyz]`.

Establish `h2 : F (resPt d y) = 0` using `ha y`. Rewrite `h2` using `[h1, hF]`. Simplify using `only at h2`. Rewrite `h2` using `[sum_secFun_smul hb.1]`. Conclude with `(mul_eq_zero.1 h2).resolve_left (pow_ne_zero _ (hc ()))`.

Establish `hpts : ∀ z ∈ mcPts (ι` using `GlobalTheory κ) (coordIdeal ℤ d.x), F z = 0 := by`. Introduce `z hz`. Establish `hcl` using `hND Unit (GlobalTheory κ) (coordIdeal ℤ d.x) (D + 1) g d.arith hgP hz`. Conclude with `(isClosed_eq hFc continuous_const).closure_subset_iff.2 (fun z' hz' => hoff z' hz'.1 hz'.2) hcl`. Establish `: IsProbabilityMeasure d.dV` using `d.vol.1`.

Choose the witnesses or unpack the hypotheses as in `⟨y₀⟩ : Nonempty d.R.X := by`. Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_nonempty_iff]`. Establish `h1` using `measure_univ (μ := d.dV)`. Rewrite `h1` using `[Set.univ_eq_empty_iff.2 h, measure_empty]`.

Conclude with `zero_ne_one h1`. Establish `hz₀ : resPt d y₀ ∈ mcPts (ι` using `GlobalTheory κ) (coordIdeal ℤ d.x) := d.R.mem y₀ y₀ (d.R.mem_U y₀)`. Use `coeff_eq_zero_of_vanish (linIndep_rat_of_isSecBasis hb) fun z hz => ?_` and prove the remaining obligations. Distinguish the cases in `h0 : z = 0`. Establish `h1` using `hpts _ hz₀`.

Rewrite `h1` using `[hF]`. Simplify using `only at h1`. Rewrite using `[h0, ← zero_smul ℂ (resPt d y₀), sum_secFun_smul hb.1, h1, mul_zero]`. Use `hpts z ⟨fun k => ?_, hz⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hk`.

Use `push Not at hk`. Conclude with `h0 (funext fun p => by obtain ⟨⟨⟩, i⟩ := p; exact hk i)`.
-/
theorem ResolutionFormsIndependent.proof (hND : NonvanishingDense.Statement) :
    ResolutionFormsIndependent.Statement := by
  intro D Ω _ _ κ _ d n r b hb a ha
  obtain ⟨g, hgJ, hgP⟩ := SetLike.not_le_iff_exists.1 d.R.nondeg
  set F : (Ix κ → ℂ) → ℂ := fun z => ∑ k, a k * secFun (b k) z with hF
  have hFc : Continuous F :=
    continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_secFun _)

  have hoff : ∀ z, z ∈ mcPts (ι := GlobalTheory κ) (coordIdeal ℤ d.x) →
      eval z (map (Int.castRingHom ℂ) g) ≠ 0 → F z = 0 := by
    intro z hz hgz
    obtain ⟨y, c, hc, hyz⟩ := d.R.surj z hz (fun hJ => hgz (hJ.2 g hgJ))
    have h1 : resPt d y = c () • z := by
      funext p
      simp [resPt, hyz]
    have h2 : F (resPt d y) = 0 := ha y
    rw [h1, hF] at h2
    simp only at h2
    rw [sum_secFun_smul hb.1] at h2
    exact (mul_eq_zero.1 h2).resolve_left (pow_ne_zero _ (hc ()))

  have hpts : ∀ z ∈ mcPts (ι := GlobalTheory κ) (coordIdeal ℤ d.x), F z = 0 := by
    intro z hz
    have hcl := hND Unit (GlobalTheory κ) (coordIdeal ℤ d.x) (D + 1) g d.arith hgP hz
    exact (isClosed_eq hFc continuous_const).closure_subset_iff.2 (fun z' hz' => hoff z' hz'.1 hz'.2) hcl

  have : IsProbabilityMeasure d.dV := d.vol.1
  obtain ⟨y₀⟩ : Nonempty d.R.X := by
    by_contra h
    rw [not_nonempty_iff] at h
    have h1 := measure_univ (μ := d.dV)
    rw [Set.univ_eq_empty_iff.2 h, measure_empty] at h1
    exact zero_ne_one h1
  have hz₀ : resPt d y₀ ∈ mcPts (ι := GlobalTheory κ) (coordIdeal ℤ d.x) := d.R.mem y₀ y₀ (d.R.mem_U y₀)
  refine coeff_eq_zero_of_vanish (linIndep_rat_of_isSecBasis hb) fun z hz => ?_
  by_cases h0 : z = 0
  · have h1 := hpts _ hz₀
    rw [hF] at h1
    simp only at h1
    rw [h0, ← zero_smul ℂ (resPt d y₀), sum_secFun_smul hb.1, h1, mul_zero]
  · refine hpts z ⟨fun k => ?_, hz⟩
    by_contra hk
    push Not at hk
    exact h0 (funext fun p => by obtain ⟨⟨⟩, i⟩ := p; exact hk i)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
