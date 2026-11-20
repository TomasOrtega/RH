import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PerCEmb
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilInner

/- English proof (translation)
Establish `e : ∀ w, f w * conj (f w) = ((‖f w‖ ^ 2 : ℝ) : ℂ)` using `fun w => by`. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Repeatedly rewrite using `[e]`. Rewrite using `[integral_complex_ofReal, integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun w => by positivity) (hf.norm.pow_const 2).aestronglyMeasurable]`. Use `congr 2`.

Use `lintegral_congr fun w => ?_` and prove the remaining obligations. Rewrite using `[ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]`.
-/
theorem integral_mul_conj_self {G : Type} [MeasurableSpace G] (ν : Measure G) {f : G → ℂ} (hf : Measurable f) :
    ∫ w, f w * conj (f w) ∂ν = ((∫⁻ w, ‖f w‖ₑ ^ 2 ∂ν).toReal : ℂ) := by
  have e : ∀ w, f w * conj (f w) = ((‖f w‖ ^ 2 : ℝ) : ℂ) := fun w => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp_rw [e]
  rw [integral_complex_ofReal, integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun w => by positivity)
    (hf.norm.pow_const 2).aestronglyMeasurable]
  congr 2
  refine lintegral_congr fun w => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]

/- English proof (translation)
Take `⟨C, hC⟩` from `bf`. Take `⟨C', hC'⟩` from `bg`. Use `Integrable.of_bound (hf.mul (Complex.continuous_conj.measurable.comp hg)).aestronglyMeasurable (C * C') (Filter.Eventually.of_forall fun w => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul, Complex.norm_conj]`. Conclude with `mul_le_mul (hC w) (hC' w) (norm_nonneg _) ((norm_nonneg _).trans (hC w))`.
-/
theorem integrable_mul_conj {G : Type} [MeasurableSpace G] (ν : Measure G) [IsFiniteMeasure ν] {f g : G → ℂ}
    (hf : Measurable f) (hg : Measurable g) (bf : ∃ C : ℝ, ∀ w, ‖f w‖ ≤ C) (bg : ∃ C : ℝ, ∀ w, ‖g w‖ ≤ C) :
    Integrable (fun w => f w * conj (g w)) ν := by
  obtain ⟨C, hC⟩ := bf
  obtain ⟨C', hC'⟩ := bg
  refine Integrable.of_bound (hf.mul (Complex.continuous_conj.measurable.comp hg)).aestronglyMeasurable (C * C')
    (Filter.Eventually.of_forall fun w => ?_)
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_mul (hC w) (hC' w) (norm_nonneg _) ((norm_nonneg _).trans (hC w))

/- English proof (translation)
Establish `hI : ∀ f g, P f → P g → Integrable (fun w => f w * conj (g w)) ν` using `fun f g hf hg => integrable_mul_conj ν (hm f hf) (hm g hg) (hb f hf) (hb g hg)`. Establish `hN : ∀ f, P f → ∫ w, A f w * conj (A f w) ∂ν = ∫ w, f w * conj (f w) ∂ν` using `fun f hf => by`. Rewrite using `[integral_mul_conj_self ν (hm _ (hA f hf)), integral_mul_conj_self ν (hm f hf), hu f hf]`. Establish `ex : ∀ (c : ℂ) f g, P f → P g → ∫ w, (f + c • g) w * conj ((f + c • g) w) ∂ν = ∫ w, f w * conj (f w) ∂ν + conj c * ∫ w, f w * conj (g w) ∂ν + c * ∫ w, g w * conj (f w) ∂ν + c * conj c * ∫ w, g w * conj (g w) ∂ν`. Introduce `c f g hf hg`.

Establish `i1` using `hI f f hf hf`. Establish `i2` using `(hI f g hf hg).const_mul (conj c)`. Establish `i3` using `(hI g f hg hf).const_mul c`. Establish `i4` using `(hI g g hg hg).const_mul (c * conj c)`. Establish `i12 : Integrable (fun w => f w * conj (f w) + conj c * (f w * conj (g w))) ν` using `i1.add i2`.

Establish `i13 : Integrable (fun w => f w * conj (f w) + conj c * (f w * conj (g w)) + c * (g w * conj (f w))) ν` using `i12.add i3`. Rewrite using `[← integral_const_mul, ← integral_const_mul, ← integral_const_mul, ← integral_add i1 i2, ← integral_add i12 i3, ← integral_add i13 i4]`. Use `congr 1`. Use function extensionality and compare the values at `w`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `key : ∀ c : ℂ, conj c * ∫ w, A f w * conj (A g w) ∂ν + c * ∫ w, A g w * conj (A f w) ∂ν = conj c * ∫ w, f w * conj (g w) ∂ν + c * ∫ w, g w * conj (f w) ∂ν`. Introduce `c`. Establish `h` using `hN _ (hadd f _ hf (hsmul c g hg))`. Rewrite `h` using `[map_add, map_smul, ex c _ _ (hA f hf) (hA g hg), ex c f g hf hg, hN f hf, hN g hg]`.

Take the linear combination `h`. Establish `h1` using `key 1`. Establish `h2` using `key I`. Rewrite `h1` using `[map_one]`. Rewrite `h2` using `[Complex.conj_I]`.

Take the linear combination `(1 / 2 : ℂ) * h1 + (I / 2) * h2 + (1 / 2 : ℂ) * (∫ w, A f w * conj (A g w) ∂ν - ∫ w, A g w * conj (A f w) ∂ν - ∫ w, f w * conj (g w) ∂ν + ∫ w, g w * conj (f w) ∂ν) * Complex.I_mul_I`.
-/
theorem inner_eq_of_meanSquare {G : Type} [MeasurableSpace G] (ν : Measure G) [IsFiniteMeasure ν]
    (P : (G → ℂ) → Prop) (hadd : ∀ f g, P f → P g → P (f + g)) (hsmul : ∀ (c : ℂ) f, P f → P (c • f))
    (hm : ∀ f, P f → Measurable f) (hb : ∀ f, P f → ∃ C : ℝ, ∀ w, ‖f w‖ ≤ C)
    (A : Module.End ℂ (G → ℂ)) (hA : ∀ f, P f → P (A f))
    (hu : ∀ f, P f → ∫⁻ w, ‖A f w‖ₑ ^ 2 ∂ν = ∫⁻ w, ‖f w‖ₑ ^ 2 ∂ν) {f g : G → ℂ} (hf : P f) (hg : P g) :
    ∫ w, A f w * conj (A g w) ∂ν = ∫ w, f w * conj (g w) ∂ν := by
  have hI : ∀ f g, P f → P g → Integrable (fun w => f w * conj (g w)) ν := fun f g hf hg =>
    integrable_mul_conj ν (hm f hf) (hm g hg) (hb f hf) (hb g hg)
  have hN : ∀ f, P f → ∫ w, A f w * conj (A f w) ∂ν = ∫ w, f w * conj (f w) ∂ν := fun f hf => by
    rw [integral_mul_conj_self ν (hm _ (hA f hf)), integral_mul_conj_self ν (hm f hf), hu f hf]
  have ex : ∀ (c : ℂ) f g, P f → P g → ∫ w, (f + c • g) w * conj ((f + c • g) w) ∂ν =
      ∫ w, f w * conj (f w) ∂ν + conj c * ∫ w, f w * conj (g w) ∂ν + c * ∫ w, g w * conj (f w) ∂ν +
        c * conj c * ∫ w, g w * conj (g w) ∂ν := by
    intro c f g hf hg
    have i1 := hI f f hf hf
    have i2 := (hI f g hf hg).const_mul (conj c)
    have i3 := (hI g f hg hf).const_mul c
    have i4 := (hI g g hg hg).const_mul (c * conj c)
    have i12 : Integrable (fun w => f w * conj (f w) + conj c * (f w * conj (g w))) ν := i1.add i2
    have i13 : Integrable (fun w => f w * conj (f w) + conj c * (f w * conj (g w)) + c * (g w * conj (f w))) ν :=
      i12.add i3
    rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul, ← integral_add i1 i2,
      ← integral_add i12 i3, ← integral_add i13 i4]
    congr 1
    funext w
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]
    ring
  have key : ∀ c : ℂ, conj c * ∫ w, A f w * conj (A g w) ∂ν + c * ∫ w, A g w * conj (A f w) ∂ν =
      conj c * ∫ w, f w * conj (g w) ∂ν + c * ∫ w, g w * conj (f w) ∂ν := by
    intro c
    have h := hN _ (hadd f _ hf (hsmul c g hg))
    rw [map_add, map_smul, ex c _ _ (hA f hf) (hA g hg), ex c f g hf hg, hN f hf, hN g hg] at h
    linear_combination h
  have h1 := key 1
  have h2 := key I
  rw [map_one] at h1
  rw [Complex.conj_I] at h2
  linear_combination (1 / 2 : ℂ) * h1 + (I / 2) * h2 + (1 / 2 : ℂ) *
    (∫ w, A f w * conj (A g w) ∂ν - ∫ w, A g w * conj (A f w) ∂ν - ∫ w, f w * conj (g w) ∂ν +
      ∫ w, g w * conj (f w) ∂ν) * Complex.I_mul_I

/- English proof (translation)
Introduce `D ψ V W χV χW om hom μ 𝓕 hc p f f' hf hf'`. Establish `: BorelSpace (WO V W)` using `⟨rfl⟩`. Establish `: IsFiniteMeasure (μ.restrict 𝓕)` using `⟨by rw [Measure.restrict_apply_univ, hc.2.2]; exact ENNReal.one_lt_top⟩`. Conclude with `inner_eq_of_meanSquare (μ.restrict 𝓕) (IsThetaFunO ψ V W) (fun _ _ => GlobalTheory.OrientedHeis.theta_add) (fun c _ => GlobalTheory.OrientedHeis.theta_smul c) (fun _ h => h.cont.measurable) (fun _ h => GlobalTheory.OrientedHeis.theta_bounded hom.std h) (om p) (hom.om_pres p) (hom …`.
-/
theorem om_inner : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χV χW om → ∀ (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsCovolOne (ratL W V) μ 𝓕 → ∀ p f f', IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' → ∫ w in 𝓕, om p f w * conj (om p f' w) ∂μ = ∫ w in 𝓕, f w * conj (f' w) ∂μ := by
  intro D ψ V W χV χW om hom μ 𝓕 hc p f f' hf hf'
  have : BorelSpace (WO V W) := ⟨rfl⟩
  have : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, hc.2.2]; exact ENNReal.one_lt_top⟩
  exact inner_eq_of_meanSquare (μ.restrict 𝓕) (IsThetaFunO ψ V W) (fun _ _ => GlobalTheory.OrientedHeis.theta_add)
    (fun c _ => GlobalTheory.OrientedHeis.theta_smul c) (fun _ h => h.cont.measurable)
    (fun _ h => GlobalTheory.OrientedHeis.theta_bounded hom.std h) (om p) (hom.om_pres p)
    (hom.om_unit μ 𝓕 hc.1 hc.2.1 p) hf hf'

end GlobalTheory.WeilInner
