import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionImageSup
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNonvanishingDense
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory Filter Topology

noncomputable section

namespace ResolutionSupBound

/- English proof (translation)
Rewrite using `[eval_eq, eval_eq, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun e he => ?_` and prove the remaining obligations. Establish `hdeg : e.degree = n`. Assume the negation of the conclusion as `h`. Conclude with `(mem_support_iff.mp he) (hf.coeff_eq_zero h)`.

Simplify using `only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]`. Establish `hs : e.degree = ∑ i ∈ e.support, e i` using `rfl`. Rewrite using `[← hdeg, hs]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eval_smul_homog {ι : Type*} {f : MvPolynomial ι ℂ} {n : ℕ} (hf : f.IsHomogeneous n) (c : ℂ)
    (z : ι → ℂ) : eval (c • z) f = c ^ n * eval z f := by
  classical
  rw [eval_eq, eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  have hdeg : e.degree = n := by
    by_contra h
    exact (mem_support_iff.mp he) (hf.coeff_eq_zero h)
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have hs : e.degree = ∑ i ∈ e.support, e i := rfl
  rw [← hdeg, hs]
  ring

/- English proof (translation)
Establish `hc' : (0 : ℝ) < ‖c‖ ^ n` using `pow_pos (norm_pos_iff.2 hc) n`. Simplify using `only [ptNorm, MvPolynomial.map_id, eval_smul_homog hf, m.smul, norm_mul, norm_pow, mul_pow]`. Conclude with `mul_div_mul_left _ _ hc'.ne'`.
-/
theorem ptNorm_smul {ι : Type*} (m : ConeMetric ℂ ι) {n : ℕ} {f : MvPolynomial ι ℂ} (hf : f.IsHomogeneous n)
    {c : ℂ} (hc : c ≠ 0) (z : ι → ℂ) :
    ptNorm m (RingHom.id ℂ) n f (c • z) = ptNorm m (RingHom.id ℂ) n f z := by
  have hc' : (0 : ℝ) < ‖c‖ ^ n := pow_pos (norm_pos_iff.2 hc) n
  simp only [ptNorm, MvPolynomial.map_id, eval_smul_homog hf, m.smul, norm_mul, norm_pow, mul_pow]
  exact mul_div_mul_left _ _ hc'.ne'

/- English proof (translation)
Introduce `D Ω _ _ κ _ d`. Take `⟨C, hC⟩` from `hI D Ω κ d`. Use `⟨C, fun n hn f hf z hz => ?_⟩` and prove the remaining obligations. Use `set B := C * (n : ℝ) ^ ((D : ℝ) / 2) * resolutionVolumeL2Complex d n f`. Take `⟨g, hgJ, hgP⟩` from `SetLike.not_le_iff_exists.1 d.R.nondeg`.

Use `set S := {w | w ∈ mcPts (ι := GlobalTheory κ) (coordIdeal ℤ d.x) ∧ eval w (map (Int.castRingHom ℂ) g) ≠ 0}`. Establish `hzm : z ∈ mcPts (ι` using `GlobalTheory κ) (coordIdeal ℤ d.x) := by`. Use `⟨fun _ => ?_, hz.2⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Simplify using `only [not_exists, not_not] at h`.

Conclude with `hz.1 (funext fun q => h q.2)`. Establish `hzS : z ∈ closure S` using `hND Unit (GlobalTheory κ) (coordIdeal ℤ d.x) (D + 1) g d.arith hgP hzm`. Establish `key : ∀ w ∈ S, ptNorm d.m (RingHom.id ℂ) n f w ≤ B`. Introduce and unpack `w ⟨hw, hwg⟩`. Take `⟨y, c, hc, hyc⟩` from `d.R.surj w hw fun h => hwg (h.2 g hgJ)`.

Establish `hy : resPt d y = c () • w`. Rewrite using `[resPt, hyc]`. Both sides reduce to the same expression. Rewrite using `[← ptNorm_smul d.m hf (hc ()), ← hy]`. Conclude with `hC n hn f hf y`.

Establish `hρ : ContinuousAt d.m.ρ z` using `(d.smooth.continuousOn).continuousAt (isOpen_ne.mem_nhds hz.1)`. Establish `hcont : ContinuousAt (ptNorm d.m (RingHom.id ℂ) n f) z`. Unfold `ptNorm`. Simplify using `only [MvPolynomial.map_id]`. Conclude with `((MvPolynomial.continuous_eval f).norm.continuousAt).div (hρ.pow n) (pow_pos (d.m.pos z hz.1) n).ne'`.

Use `mem_closure_iff_nhdsWithin_neBot.1 hzS` as an intermediate fact. Conclude with `le_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds) (eventually_nhdsWithin_of_forall key)`.
-/
theorem proof (hI : ResolutionImageSup.Statement) (hND : NonvanishingDense.Statement) :
    ResolutionSupBound.Statement := by
  intro D Ω _ _ κ _ d
  obtain ⟨C, hC⟩ := hI D Ω κ d
  refine ⟨C, fun n hn f hf z hz => ?_⟩
  set B := C * (n : ℝ) ^ ((D : ℝ) / 2) * resolutionVolumeL2Complex d n f
  obtain ⟨g, hgJ, hgP⟩ := SetLike.not_le_iff_exists.1 d.R.nondeg
  set S := {w | w ∈ mcPts (ι := GlobalTheory κ) (coordIdeal ℤ d.x) ∧ eval w (map (Int.castRingHom ℂ) g) ≠ 0}
  have hzm : z ∈ mcPts (ι := GlobalTheory κ) (coordIdeal ℤ d.x) := by
    refine ⟨fun _ => ?_, hz.2⟩
    by_contra h
    simp only [not_exists, not_not] at h
    exact hz.1 (funext fun q => h q.2)
  have hzS : z ∈ closure S := hND Unit (GlobalTheory κ) (coordIdeal ℤ d.x) (D + 1) g d.arith hgP hzm
  have key : ∀ w ∈ S, ptNorm d.m (RingHom.id ℂ) n f w ≤ B := by
    rintro w ⟨hw, hwg⟩
    obtain ⟨y, c, hc, hyc⟩ := d.R.surj w hw fun h => hwg (h.2 g hgJ)
    have hy : resPt d y = c () • w := by
      rw [resPt, hyc]
      rfl
    rw [← ptNorm_smul d.m hf (hc ()), ← hy]
    exact hC n hn f hf y
  have hρ : ContinuousAt d.m.ρ z :=
    (d.smooth.continuousOn).continuousAt (isOpen_ne.mem_nhds hz.1)
  have hcont : ContinuousAt (ptNorm d.m (RingHom.id ℂ) n f) z := by
    unfold ptNorm
    simp only [MvPolynomial.map_id]
    exact ((MvPolynomial.continuous_eval f).norm.continuousAt).div (hρ.pow n)
      (pow_pos (d.m.pos z hz.1) n).ne'
  have := mem_closure_iff_nhdsWithin_neBot.1 hzS
  exact le_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds) (eventually_nhdsWithin_of_forall key)

end ResolutionSupBound

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
