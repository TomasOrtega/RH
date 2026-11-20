import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory

/- English proof (translation)
Introduce `X U Y _ _ _ G _ ν νU μ _ _ i p Inv hi hp Dom H f hf hinv hfi`. Establish `hpm : Measurable (fun q : U × Y => p q.1 q.2)` using `hp`. Establish `hprod : ∀ g : G → ENNReal, Measurable g → (∀ t, Inv t → ∀ n ∈ Dom, g (t n) = g n) → ∫⁻ x, g (i x) ∂ν = ∫⁻ q, g (p q.1 q.2) ∂(νU.prod μ)`. Introduce `g hg hgi`. Rewrite using `[H g hg hgi, lintegral_prod (fun q : U × Y => g (p q.1 q.2)) (hg.comp hpm).aemeasurable]`.

Establish `hint : Integrable (fun q : U × Y => f (p q.1 q.2)) (νU.prod μ)`. Use `⟨(hf.comp hpm).aestronglyMeasurable, ?_⟩` and prove the remaining obligations. Rewrite using `[hasFiniteIntegral_iff_enorm]`. Use `hprod (fun n => ‖f n‖ₑ) hf.enorm (fun t ht n hn => by simp only [hinv t ht n hn])` as an intermediate fact. Rewrite using `[← this]`.

Conclude with `hfi.2`. Use `⟨hint, ?_⟩` and prove the remaining obligations. Rewrite using `[← integral_prod _ hint]`. Establish `hreal : ∀ g : G → ℝ, Measurable g → (∀ t, Inv t → ∀ n ∈ Dom, g (t n) = g n) → Integrable (fun x => g (i x)) ν → Integrable (fun q : U × Y => g (p q.1 q.2)) (νU.prod μ) → ∫ x, g (i x) ∂ν = ∫ q, g (p q.1 q.2) ∂(νU.prod μ)`. Introduce `g hg hgi h1 h2`.

Rewrite using `[integral_eq_lintegral_pos_part_sub_lintegral_neg_part h1, integral_eq_lintegral_pos_part_sub_lintegral_neg_part h2]`. Establish `e1` using `hprod (fun n => ENNReal.ofReal (g n)) (ENNReal.measurable_ofReal.comp hg) (fun t ht n hn => by simp only [hgi t ht n hn])`. Establish `e2` using `hprod (fun n => ENNReal.ofReal (- g n)) (ENNReal.measurable_ofReal.comp hg.neg) (fun t ht n hn => by simp only [hgi t ht n hn])`. Rewrite using `[e1, e2]`. Apply `Complex.ext` to reduce the goal to its premises.

Establish `a` using `integral_re hfi`. Establish `b` using `integral_re hint`. Simplify using `only [RCLike.re_to_complex] at a b`. Rewrite using `[← a, ← b]`. Conclude with `hreal (fun n => (f n).re) (Complex.measurable_re.comp hf) (fun t ht n hn => by simp only [hinv t ht n hn]) hfi.re hint.re`.

Establish `a` using `integral_im hfi`. Establish `b` using `integral_im hint`. Simplify using `only [RCLike.im_to_complex] at a b`. Rewrite using `[← a, ← b]`. Conclude with `hreal (fun n => (f n).im) (Complex.measurable_im.comp hf) (fun t ht n hn => by simp only [hinv t ht n hn]) hfi.im hint.im`.
-/
theorem lowerIntegral_to_integral_coords : ∀ (X U Y : Type) [MeasurableSpace X] [MeasurableSpace U] [MeasurableSpace Y] (G : Type) [MeasurableSpace G] (ν : Measure X) (νU : Measure U) (μ : Measure Y) [SFinite νU] [SFinite μ] (i : X → G) (p : U → Y → G) (Inv : (G → G) → Prop), Measurable i → Measurable (Function.uncurry p) → ∀ (Dom : Set G), (∀ f : G → ENNReal, Measurable f → (∀ t, Inv t → ∀ n ∈ Dom, f (t n) = f n) → ∫⁻ x, f (i x) ∂ν = ∫⁻ u, ∫⁻ y, f (p u y) ∂μ ∂νU) → ∀ f : G → ℂ, Measurable f → (∀ t, Inv t → ∀ n ∈ Dom, f (t n) = f n) → Integrable (fun x => f (i x)) ν → Integrable (fun q : U × Y => f (p q.1 q.2)) (νU.prod μ) ∧ ∫ x, f (i x) ∂ν = ∫ u, ∫ y, f (p u y) ∂μ ∂νU := by
  intro X U Y _ _ _ G _ ν νU μ _ _ i p Inv hi hp Dom H f hf hinv hfi
  have hpm : Measurable (fun q : U × Y => p q.1 q.2) := hp

  have hprod : ∀ g : G → ENNReal, Measurable g → (∀ t, Inv t → ∀ n ∈ Dom, g (t n) = g n) →
      ∫⁻ x, g (i x) ∂ν = ∫⁻ q, g (p q.1 q.2) ∂(νU.prod μ) := by
    intro g hg hgi
    rw [H g hg hgi, lintegral_prod (fun q : U × Y => g (p q.1 q.2)) (hg.comp hpm).aemeasurable]
  have hint : Integrable (fun q : U × Y => f (p q.1 q.2)) (νU.prod μ) := by
    refine ⟨(hf.comp hpm).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have := hprod (fun n => ‖f n‖ₑ) hf.enorm (fun t ht n hn => by simp only [hinv t ht n hn])
    rw [← this]
    exact hfi.2
  refine ⟨hint, ?_⟩
  rw [← integral_prod _ hint]

  have hreal : ∀ g : G → ℝ, Measurable g → (∀ t, Inv t → ∀ n ∈ Dom, g (t n) = g n) →
      Integrable (fun x => g (i x)) ν → Integrable (fun q : U × Y => g (p q.1 q.2)) (νU.prod μ) →
      ∫ x, g (i x) ∂ν = ∫ q, g (p q.1 q.2) ∂(νU.prod μ) := by
    intro g hg hgi h1 h2
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part h1,
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part h2]
    have e1 := hprod (fun n => ENNReal.ofReal (g n)) (ENNReal.measurable_ofReal.comp hg)
      (fun t ht n hn => by simp only [hgi t ht n hn])
    have e2 := hprod (fun n => ENNReal.ofReal (- g n)) (ENNReal.measurable_ofReal.comp hg.neg)
      (fun t ht n hn => by simp only [hgi t ht n hn])
    rw [e1, e2]
  apply Complex.ext
  · have a := integral_re hfi; have b := integral_re hint
    simp only [RCLike.re_to_complex] at a b
    rw [← a, ← b]
    exact hreal (fun n => (f n).re) (Complex.measurable_re.comp hf)
      (fun t ht n hn => by simp only [hinv t ht n hn]) hfi.re hint.re
  · have a := integral_im hfi; have b := integral_im hint
    simp only [RCLike.im_to_complex] at a b
    rw [← a, ← b]
    exact hreal (fun n => (f n).im) (Complex.measurable_im.comp hf)
      (fun t ht n hn => by simp only [hinv t ht n hn]) hfi.im hint.im

end GlobalTheory
