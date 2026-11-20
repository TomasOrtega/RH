import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsCovolOne
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsUnitScalingSelfdualAdelicMeasures
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SelfdualMeasureTwistBySymmetricAuto
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SelfdualMeasureTransportEquiv
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsTraceFormGramMatrixInBasis
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsUnipotentInvariantCompactlySupportedWeight
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.ExistsEqAdelicCharMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TamePartRight
import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.SdExist

open MeasureTheory Topology

section Abstract

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] {μ : Measure V} [SFinite μ]

/- English proof (translation)
Establish `h0 : Integrable (fun p : V × V => g p.1 * f p.2) (μ.prod μ)` using `hg.mul_prod hf`. Establish `hm : AEStronglyMeasurable (fun p : V × V => χ p.2 p.1) (μ.prod μ)` using `(hχ.comp continuous_swap).aestronglyMeasurable`. Establish `hint : Integrable (Function.uncurry fun y x => g y * f x * χ x y) (μ.prod μ)`. Use `h0.mono (h0.1.mul hm) (ae_of_all _ fun p => ?_)` and prove the remaining obligations. Simplify using `[Function.uncurry, hn]`.

Combine the equalities or inequalities in the displayed calculation. Use `integral_congr_ae (ae_of_all _ fun y => ?_)` and prove the remaining obligations. Simplify using `only`. Rewrite using `[← integral_mul_const]`. Conclude with `integral_congr_ae (ae_of_all _ fun x => by simp only; ring)`.

Use `_ = ∫ x, ∫ y, g y * f x * χ x y ∂μ ∂μ := integral_integral_swap hint`. Use `_ = ∫ x, f x * ∫ y, g y * χ x y ∂μ ∂μ := by`. Use `integral_congr_ae (ae_of_all _ fun x => ?_)` and prove the remaining obligations. Simplify using `only`. Rewrite using `[← integral_const_mul]`.

Conclude with `integral_congr_ae (ae_of_all _ fun y => by simp only; ring)`.
-/
theorem integral_mul_swap (χ : V → V → ℂ) (hχ : Continuous fun p : V × V => χ p.1 p.2)
    (hn : ∀ x y, ‖χ x y‖ = 1) {f g : V → ℂ} (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ y, (∫ x, f x * χ x y ∂μ) * g y ∂μ = ∫ x, f x * ∫ y, g y * χ x y ∂μ ∂μ := by
  have h0 : Integrable (fun p : V × V => g p.1 * f p.2) (μ.prod μ) := hg.mul_prod hf
  have hm : AEStronglyMeasurable (fun p : V × V => χ p.2 p.1) (μ.prod μ) :=
    (hχ.comp continuous_swap).aestronglyMeasurable
  have hint : Integrable (Function.uncurry fun y x => g y * f x * χ x y) (μ.prod μ) := by
    refine h0.mono (h0.1.mul hm) (ae_of_all _ fun p => ?_)
    simp [Function.uncurry, hn]
  calc ∫ y, (∫ x, f x * χ x y ∂μ) * g y ∂μ = ∫ y, ∫ x, g y * f x * χ x y ∂μ ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun y => ?_)
        simp only
        rw [← integral_mul_const]
        exact integral_congr_ae (ae_of_all _ fun x => by simp only; ring)
    _ = ∫ x, ∫ y, g y * f x * χ x y ∂μ ∂μ := integral_integral_swap hint
    _ = ∫ x, f x * ∫ y, g y * χ x y ∂μ ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only
        rw [← integral_const_mul]
        exact integral_congr_ae (ae_of_all _ fun y => by simp only; ring)

/- English proof (translation)
Use `⟨hμ, fun Φ hc hcs hI z => ?_⟩` and prove the remaining obligations. Establish `hΦ : Integrable Φ μ` using `hc.integrable_of_hasCompactSupport hcs`. Use `set Φh : V → ℂ := fun y => ∫ x, Φ x * χ x y ∂μ with hΦh`. Use `set G : V → ℂ := fun z => ∫ y, Φh y * χ y z ∂μ with hG`. Establish `hχ1 : ∀ y, Continuous fun z => χ y z` using `fun y => hχ.comp (Continuous.prodMk_right y)`.

Establish `hχ2 : ∀ z, Continuous fun y => χ y z` using `fun z => hχ.comp (Continuous.prodMk_left z)`. Establish `hGc : Continuous G`. Use `continuous_of_dominated (bound := fun y => ‖Φh y‖) ?_ ?_ hI.norm ?_` and prove the remaining obligations. Conclude with `fun z => hI.1.mul (hχ2 z).aestronglyMeasurable`. Conclude with `fun z => ae_of_all _ fun y => by rw [norm_mul, hn, mul_one]`.

Conclude with `ae_of_all _ fun y => continuous_const.mul (hχ1 y)`. Establish `hGb : ∀ z, ‖G z‖ ≤ ∫ y, ‖Φh y‖ ∂μ` using `fun z => by`. Use `(norm_integral_le_integral_norm _).trans_eq (integral_congr_ae (ae_of_all _ fun y => ?_))` and prove the remaining obligations. Simplify using `only [norm_mul, hn, mul_one]`. Take `⟨C, hC⟩` from `hc.bounded_above_of_compact_support hcs`.

Use `set h : V → ℂ := fun z => G z - Φ (-z) with hh`. Establish `hhc : Continuous h` using `hGc.sub (hc.comp continuous_neg)`. Establish `key : ∀ g ∈ S, ∫ z, h z * g z ∂μ = 0`. Introduce `g hg`. Take `⟨g1, g2, g3⟩` from `hS g hg`.

Establish `e1 : ∫ z, G z * g z ∂μ = ∫ x, Φ x * g (-x) ∂μ`. Establish `s1` using `integral_mul_swap χ hχ hn hI g1`. Establish `s2` using `integral_mul_swap χ hχ hn hΦ g2`. Establish `t1 : ∫ x, Φh x * ∫ y, g y * χ x y ∂μ ∂μ = ∫ y, (∫ x, Φ x * χ x y ∂μ) * ∫ x, g x * χ x y ∂μ ∂μ`. Use `integral_congr_ae (ae_of_all _ fun y => ?_)` and prove the remaining obligations.

Simplify using `only [hΦh]`. Use `congr 1`. Conclude with `integral_congr_ae (ae_of_all _ fun x => by simp only [hs y x])`. Establish `t2 : ∫ x, Φ x * ∫ y, (∫ x, g x * χ x y ∂μ) * χ x y ∂μ ∂μ = ∫ x, Φ x * g (-x) ∂μ`. Use `integral_congr_ae (ae_of_all _ fun x => ?_)` and prove the remaining obligations.

Simplify using `only`. Rewrite using `[← g3 x]`. Use `congr 1`. Conclude with `integral_congr_ae (ae_of_all _ fun y => by simp only [hs x y])`. Combine the equalities or inequalities in the displayed calculation.

Establish `e2 : ∫ z, Φ (-z) * g z ∂μ = ∫ x, Φ x * g (-x) ∂μ`. Rewrite using `[← integral_neg_eq_self (fun x => Φ x * g (-x)) μ]`. Simplify using the standard rewrite rules. Establish `i1 : Integrable (fun z => G z * g z) μ` using `(g1.norm.const_mul (∫ y, ‖Φh y‖ ∂μ)).mono' (hGc.aestronglyMeasurable.mul g1.1) (ae_of_all _ fun z => by`. Rewrite using `[norm_mul]`.

Conclude with `mul_le_mul_of_nonneg_right (hGb z) (norm_nonneg _))`. Establish `i2 : Integrable (fun z => Φ (-z) * g z) μ` using `(g1.norm.const_mul C).mono' ((hc.comp continuous_neg).aestronglyMeasurable.mul g1.1) (ae_of_all _ fun z => by`. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _))`. Simplify using `only [hh, sub_mul]`.

Rewrite using `[integral_sub i1 i2, e1, e2, sub_self]`. Assume the negation of the conclusion as `hne`. Establish `ha : h z ≠ 0` using `sub_ne_zero.mpr hne`. Use `set a := h z with hadef`. Establish `hpos : 0 < ‖a‖` using `norm_pos_iff.mpr ha`.

Establish `hU : {x | ‖h x - a‖ < ‖a‖ / 2} ∈ 𝓝 z`. Use `(isOpen_lt (hhc.sub continuous_const).norm continuous_const).mem_nhds ?_` and prove the remaining obligations. Use `show ‖a - a‖ < ‖a‖ / 2`. Rewrite using `[sub_self, norm_zero]`. Conclude with `half_pos hpos`.

Take `⟨r, rc, r0, rz, rU, rS⟩` from `hR z _ hU`. Establish `hrC : Integrable (fun x => (r x : ℂ)) μ` using `(hS _ rS).1`. Establish `hrI : Integrable r μ` using `by simpa using hrC.re`. Establish `hIpos : 0 < ∫ x, r x ∂μ`. Rewrite using `[integral_pos_iff_support_of_nonneg (fun x => r0 x) hrI]`.

Conclude with `(isOpen_ne_fun rc continuous_const).measure_pos μ ⟨z, rz.ne'⟩`. Establish `e` using `key _ rS`. Establish `i3 : Integrable (fun x => h x * (r x : ℂ)) μ` using `(hrC.norm.const_mul ((∫ y, ‖Φh y‖ ∂μ) + C)).mono' (hhc.aestronglyMeasurable.mul hrC.1) (ae_of_all _ fun x => by`. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul_of_nonneg_right ((norm_sub_le _ _).trans (add_le_add (hGb x) (hC _))) (norm_nonneg _))`.

Establish `e3 : ∫ x, (h x - a) * (r x : ℂ) ∂μ = -(a * ((∫ x, r x ∂μ : ℝ) : ℂ))`. Simplify using `only [sub_mul]`. Rewrite using `[integral_sub i3 (hrC.const_mul a), e, integral_const_mul, integral_complex_ofReal, zero_sub]`. Establish `b` using `norm_integral_le_of_norm_le (f := fun x => (h x - a) * (r x : ℂ)) (hrI.const_mul (‖a‖ / 2)) (ae_of_all _ fun x => by`. Distinguish the cases in `hx : r x = 0`.

Simplify using `[hx]`. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_of_nonneg (r0 x)]`. Conclude with `mul_le_mul_of_nonneg_right (rU x hx).le (r0 x))`. Rewrite `b` using `[e3, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hIpos.le, integral_const_mul]`. Use `mul_pos hpos hIpos` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem selfDual_of_rich (hμ : μ.IsAddHaarMeasure) [μ.IsNegInvariant] (χ : V → V → ℂ)
    (hχ : Continuous fun p : V × V => χ p.1 p.2) (hn : ∀ x y, ‖χ x y‖ = 1)
    (hs : ∀ x y, χ x y = χ y x) (S : Set (V → ℂ))
    (hS : ∀ g ∈ S, Integrable g μ ∧ Integrable (fun y => ∫ x, g x * χ x y ∂μ) μ ∧
      ∀ z, ∫ y, (∫ x, g x * χ x y ∂μ) * χ y z ∂μ = g (-z))
    (hR : ∀ z, ∀ U ∈ 𝓝 z, ∃ r : V → ℝ, Continuous r ∧ (∀ x, 0 ≤ r x) ∧ 0 < r z ∧
      (∀ x, r x ≠ 0 → x ∈ U) ∧ (fun x => (r x : ℂ)) ∈ S) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.SelfDual μ χ := by
  refine ⟨hμ, fun Φ hc hcs hI z => ?_⟩
  have hΦ : Integrable Φ μ := hc.integrable_of_hasCompactSupport hcs
  set Φh : V → ℂ := fun y => ∫ x, Φ x * χ x y ∂μ with hΦh
  set G : V → ℂ := fun z => ∫ y, Φh y * χ y z ∂μ with hG
  have hχ1 : ∀ y, Continuous fun z => χ y z := fun y =>
    hχ.comp (Continuous.prodMk_right y)
  have hχ2 : ∀ z, Continuous fun y => χ y z := fun z =>
    hχ.comp (Continuous.prodMk_left z)
  have hGc : Continuous G := by
    refine continuous_of_dominated (bound := fun y => ‖Φh y‖) ?_ ?_ hI.norm ?_
    · exact fun z => hI.1.mul (hχ2 z).aestronglyMeasurable
    · exact fun z => ae_of_all _ fun y => by rw [norm_mul, hn, mul_one]
    · exact ae_of_all _ fun y => continuous_const.mul (hχ1 y)
  have hGb : ∀ z, ‖G z‖ ≤ ∫ y, ‖Φh y‖ ∂μ := fun z => by
    refine (norm_integral_le_integral_norm _).trans_eq
      (integral_congr_ae (ae_of_all _ fun y => ?_))
    simp only [norm_mul, hn, mul_one]
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hcs
  set h : V → ℂ := fun z => G z - Φ (-z) with hh
  have hhc : Continuous h := hGc.sub (hc.comp continuous_neg)
  have key : ∀ g ∈ S, ∫ z, h z * g z ∂μ = 0 := by
    intro g hg
    obtain ⟨g1, g2, g3⟩ := hS g hg
    have e1 : ∫ z, G z * g z ∂μ = ∫ x, Φ x * g (-x) ∂μ := by
      have s1 := integral_mul_swap χ hχ hn hI g1
      have s2 := integral_mul_swap χ hχ hn hΦ g2
      have t1 : ∫ x, Φh x * ∫ y, g y * χ x y ∂μ ∂μ =
          ∫ y, (∫ x, Φ x * χ x y ∂μ) * ∫ x, g x * χ x y ∂μ ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun y => ?_)
        simp only [hΦh]
        congr 1
        exact integral_congr_ae (ae_of_all _ fun x => by simp only [hs y x])
      have t2 : ∫ x, Φ x * ∫ y, (∫ x, g x * χ x y ∂μ) * χ x y ∂μ ∂μ = ∫ x, Φ x * g (-x) ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only
        rw [← g3 x]
        congr 1
        exact integral_congr_ae (ae_of_all _ fun y => by simp only [hs x y])
      calc ∫ z, G z * g z ∂μ = _ := s1
        _ = _ := t1
        _ = _ := s2
        _ = _ := t2
    have e2 : ∫ z, Φ (-z) * g z ∂μ = ∫ x, Φ x * g (-x) ∂μ := by
      rw [← integral_neg_eq_self (fun x => Φ x * g (-x)) μ]
      simp
    have i1 : Integrable (fun z => G z * g z) μ :=
      (g1.norm.const_mul (∫ y, ‖Φh y‖ ∂μ)).mono' (hGc.aestronglyMeasurable.mul g1.1)
        (ae_of_all _ fun z => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hGb z) (norm_nonneg _))
    have i2 : Integrable (fun z => Φ (-z) * g z) μ :=
      (g1.norm.const_mul C).mono' ((hc.comp continuous_neg).aestronglyMeasurable.mul g1.1)
        (ae_of_all _ fun z => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _))
    simp only [hh, sub_mul]
    rw [integral_sub i1 i2, e1, e2, sub_self]
  by_contra hne
  have ha : h z ≠ 0 := sub_ne_zero.mpr hne
  set a := h z with hadef
  have hpos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hU : {x | ‖h x - a‖ < ‖a‖ / 2} ∈ 𝓝 z := by
    refine (isOpen_lt (hhc.sub continuous_const).norm continuous_const).mem_nhds ?_
    show ‖a - a‖ < ‖a‖ / 2
    rw [sub_self, norm_zero]
    exact half_pos hpos
  obtain ⟨r, rc, r0, rz, rU, rS⟩ := hR z _ hU
  have hrC : Integrable (fun x => (r x : ℂ)) μ := (hS _ rS).1
  have hrI : Integrable r μ := by simpa using hrC.re
  have hIpos : 0 < ∫ x, r x ∂μ := by
    rw [integral_pos_iff_support_of_nonneg (fun x => r0 x) hrI]
    exact (isOpen_ne_fun rc continuous_const).measure_pos μ ⟨z, rz.ne'⟩
  have e := key _ rS
  have i3 : Integrable (fun x => h x * (r x : ℂ)) μ :=
    (hrC.norm.const_mul ((∫ y, ‖Φh y‖ ∂μ) + C)).mono' (hhc.aestronglyMeasurable.mul hrC.1)
      (ae_of_all _ fun x => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right ((norm_sub_le _ _).trans (add_le_add (hGb x) (hC _)))
          (norm_nonneg _))
  have e3 : ∫ x, (h x - a) * (r x : ℂ) ∂μ = -(a * ((∫ x, r x ∂μ : ℝ) : ℂ)) := by
    simp only [sub_mul]
    rw [integral_sub i3 (hrC.const_mul a), e, integral_const_mul, integral_complex_ofReal, zero_sub]
  have b := norm_integral_le_of_norm_le (f := fun x => (h x - a) * (r x : ℂ))
    (hrI.const_mul (‖a‖ / 2)) (ae_of_all _ fun x => by
      by_cases hx : r x = 0
      · simp [hx]
      · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (r0 x)]
        exact mul_le_mul_of_nonneg_right (rU x hx).le (r0 x))
  rw [e3, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hIpos.le,
    integral_const_mul] at b
  have := mul_pos hpos hIpos
  linarith

end Abstract

section Concrete

open GroundTheory.Automorphic.GJMatrix GroundTheory.Global NumberField NumberField.mixedEmbedding
  IsDedekindDomain
open scoped SchwartzMap

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]

/- English proof (translation)
Set `inv : (ι → mixedSpace K) × (ι → FiniteAdeleRing (𝓞 K) K) → (ι → AdeleRing (𝓞 K) K)` to `fun p i => ((homeomorphMixedSpace K).symm (p.1 i), p.2 i)`. Establish `hinv : Continuous inv` using `continuous_pi fun i => ((homeomorphMixedSpace K).symm.continuous.comp ((continuous_apply i).comp continuous_fst)).prodMk ((continuous_apply i).comp continuous_snd)`. Establish `hz : ∀ x, inv (infPartPi x, finPartPi x) = x` using `fun x => by`. Use function extensionality and compare the values at `i`. Simplify using `only [inv, infPartPi, finPartPi, Homeomorph.symm_apply_apply]`.

Both sides reduce to the same expression. Establish `hU' : inv ⁻¹' U ∈ 𝓝 (infPartPi z, finPartPi z)` using `hinv.continuousAt.preimage_mem_nhds (by rwa [hz])`. Take `⟨A, hA, B, hB, hAB⟩` from `mem_nhds_prod_iff.1 hU'`. Take `⟨ε, hε, hball⟩` from `Metric.mem_nhds_iff.1 hA`. Set `b : ContDiffBump (infPartPi z)` to `⟨ε / 2, ε, half_pos hε, half_lt_self hε⟩`.

Establish `h1 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ))` using `b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)`. Set `φ : 𝓢(ι → mixedSpace K, ℂ)` to `h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)`. Establish `hφ : ∀ u, φ u = ((b u : ℝ) : ℂ)` using `fun u => rfl`. Use `haveI : TotallyDisconnectedSpace (FiniteAdeleRing (𝓞 K) K) := GlobalTheory.TamePartR.totallyDisconnected_finiteAdele K`. Take `⟨Kc, hKn, hKs, hKc⟩` from `local_compact_nhds hB`.

Take `⟨C, hCo, hv, hCs⟩` from `(loc_compact_Haus_tot_disc_of_zero_dim (H := ι → FiniteAdeleRing (𝓞 K) K)).mem_nhds_iff.1 hKn`. Establish `hCo' : IsClopen C` using `hCo`. Establish `hCc : IsCompact C` using `hKc.of_isClosed_subset hCo'.1 hCs`. Establish `hlc : ∀ {Y : Type} [Zero Y] (c : Y), IsLocallyConstant (C.indicator fun _ => c)`. Introduce `Y _ c`.

Use `(IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_` and prove the remaining obligations. Distinguish the cases in `hx : x ∈ C`. Use `filter_upwards [hCo'.isOpen.mem_nhds hx] with y hy`. Simplify using `[hx, hy]`. Use `filter_upwards [hCo'.compl.isOpen.mem_nhds hx] with y hy`.

Establish `hy' : y ∉ C` using `hy`. Simplify using `[hx, hy']`. Set `g : (ι → FiniteAdeleRing (𝓞 K) K) → ℂ` to `C.indicator fun _ => 1`. Set `gR : (ι → FiniteAdeleRing (𝓞 K) K) → ℝ` to `C.indicator fun _ => 1`. Establish `hg : g ∈ finiteSchwartzBruhatPi K` using `(mem_finiteSchwartzBruhatPi K).2 ⟨hlc 1, HasCompactSupport.intro hCc fun x hx => Set.indicator_of_notMem hx _⟩`.

Use `⟨fun x => b (infPartPi x) * gR (finPartPi x), ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(b.continuous.comp continuous_infPartPi).mul ((hlc (1 : ℝ)).continuous.comp continuous_finPartPi)`. Introduce `x`. Conclude with `mul_nonneg b.nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _)`. Establish `e1 : b (infPartPi z) = 1` using `b.one_of_mem_closedBall (Metric.mem_closedBall_self (half_pos hε).le)`.

Establish `e2 : gR (finPartPi z) = 1` using `Set.indicator_of_mem hv _`. Simplify using `[e1, e2]`. Introduce `x hx`. Establish `hb : b (infPartPi x) ≠ 0` using `left_ne_zero_of_mul hx`. Establish `hgx : gR (finPartPi x) ≠ 0` using `right_ne_zero_of_mul hx`.

Establish `hu : infPartPi x ∈ A` using `hball (by`. Establish `: infPartPi x ∈ Function.support b` using `hb`. Rewrite using `[b.support_eq] at this)` and apply the resulting hypothesis. Establish `hvx : finPartPi x ∈ B` using `hKs (hCs (by`. Assume the negation of the conclusion as `hc`.

Conclude with `hgx (Set.indicator_of_notMem hc _)))`. Use `hAB (Set.mk_mem_prod hu hvx)` as an intermediate fact. Rewrite `this` using `[Set.mem_preimage, hz]`. Then use the resulting hypothesis. Establish `: (fun x => (((b (infPartPi x) * gR (finPartPi x) : ℝ)) : ℂ)) = schwartzBruhatTensorPi φ g`. Use function extensionality and compare the values at `x`.

Simplify using `only [schwartzBruhatTensorPi, hφ, g, gR]`. Apply the tactic sequence `by_cases hx : finPartPi x ∈ C <;> simp [hx]`. Rewrite using `[this]`. Conclude with `schwartzBruhatTensorPi_mem φ hg`.
-/
theorem exists_bump (z : ι → AdeleRing (𝓞 K) K) (U : Set (ι → AdeleRing (𝓞 K) K)) (hU : U ∈ 𝓝 z) :
    ∃ r : (ι → AdeleRing (𝓞 K) K) → ℝ, Continuous r ∧ (∀ x, 0 ≤ r x) ∧ 0 < r z ∧
      (∀ x, r x ≠ 0 → x ∈ U) ∧ (fun x => (r x : ℂ)) ∈ schwartzBruhatPi K ι := by
  classical
  let inv : (ι → mixedSpace K) × (ι → FiniteAdeleRing (𝓞 K) K) → (ι → AdeleRing (𝓞 K) K) :=
    fun p i => ((homeomorphMixedSpace K).symm (p.1 i), p.2 i)
  have hinv : Continuous inv := continuous_pi fun i =>
    ((homeomorphMixedSpace K).symm.continuous.comp
      ((continuous_apply i).comp continuous_fst)).prodMk
      ((continuous_apply i).comp continuous_snd)
  have hz : ∀ x, inv (infPartPi x, finPartPi x) = x := fun x => by
    funext i
    simp only [inv, infPartPi, finPartPi, Homeomorph.symm_apply_apply]
    rfl
  have hU' : inv ⁻¹' U ∈ 𝓝 (infPartPi z, finPartPi z) :=
    hinv.continuousAt.preimage_mem_nhds (by rwa [hz])
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.1 hU'
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hA
  let b : ContDiffBump (infPartPi z) := ⟨ε / 2, ε, half_pos hε, half_lt_self hε⟩
  have h1 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  let φ : 𝓢(ι → mixedSpace K, ℂ) := h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
  have hφ : ∀ u, φ u = ((b u : ℝ) : ℂ) := fun u => rfl
  haveI : TotallyDisconnectedSpace (FiniteAdeleRing (𝓞 K) K) :=
    GlobalTheory.TamePartR.totallyDisconnected_finiteAdele K
  obtain ⟨Kc, hKn, hKs, hKc⟩ := local_compact_nhds hB
  obtain ⟨C, hCo, hv, hCs⟩ :=
    (loc_compact_Haus_tot_disc_of_zero_dim (H := ι → FiniteAdeleRing (𝓞 K) K)).mem_nhds_iff.1 hKn
  have hCo' : IsClopen C := hCo
  have hCc : IsCompact C := hKc.of_isClosed_subset hCo'.1 hCs
  have hlc : ∀ {Y : Type} [Zero Y] (c : Y), IsLocallyConstant (C.indicator fun _ => c) := by
    intro Y _ c
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
    by_cases hx : x ∈ C
    · filter_upwards [hCo'.isOpen.mem_nhds hx] with y hy
      simp [hx, hy]
    · filter_upwards [hCo'.compl.isOpen.mem_nhds hx] with y hy
      have hy' : y ∉ C := hy
      simp [hx, hy']
  let g : (ι → FiniteAdeleRing (𝓞 K) K) → ℂ := C.indicator fun _ => 1
  let gR : (ι → FiniteAdeleRing (𝓞 K) K) → ℝ := C.indicator fun _ => 1
  have hg : g ∈ finiteSchwartzBruhatPi K := (mem_finiteSchwartzBruhatPi K).2
    ⟨hlc 1, HasCompactSupport.intro hCc fun x hx => Set.indicator_of_notMem hx _⟩
  refine ⟨fun x => b (infPartPi x) * gR (finPartPi x), ?_, ?_, ?_, ?_, ?_⟩
  · exact (b.continuous.comp continuous_infPartPi).mul
      ((hlc (1 : ℝ)).continuous.comp continuous_finPartPi)
  · intro x
    exact mul_nonneg b.nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  · have e1 : b (infPartPi z) = 1 :=
      b.one_of_mem_closedBall (Metric.mem_closedBall_self (half_pos hε).le)
    have e2 : gR (finPartPi z) = 1 := Set.indicator_of_mem hv _
    simp [e1, e2]
  · intro x hx
    have hb : b (infPartPi x) ≠ 0 := left_ne_zero_of_mul hx
    have hgx : gR (finPartPi x) ≠ 0 := right_ne_zero_of_mul hx
    have hu : infPartPi x ∈ A := hball (by
      have : infPartPi x ∈ Function.support b := hb
      rwa [b.support_eq] at this)
    have hvx : finPartPi x ∈ B := hKs (hCs (by
      by_contra hc
      exact hgx (Set.indicator_of_notMem hc _)))
    have := hAB (Set.mk_mem_prod hu hvx)
    rwa [Set.mem_preimage, hz] at this
  · have : (fun x => (((b (infPartPi x) * gR (finPartPi x) : ℝ)) : ℂ)) =
        schwartzBruhatTensorPi φ g := by
      funext x
      simp only [schwartzBruhatTensorPi, hφ, g, gR]
      by_cases hx : finPartPi x ∈ C <;> simp [hx]
    rw [this]
    exact schwartzBruhatTensorPi_mem φ hg

/- English proof (translation)
Use `selfDual_of_rich inferInstance _ ?_ (fun _ _ => Circle.norm_coe _) ?_ (schwartzBruhatPi K ι : Set _) ?_ exists_bump` and prove the remaining obligations. Conclude with `continuous_subtype_val.comp ((continuous_adelicChar (K := K)).comp (continuous_finsetSum _ fun i _ => ((continuous_apply i).comp continuous_fst).mul ((continuous_apply i).comp continuous_snd)))`. Introduce `x y`. Simplify using `only [mul_comm]`. Introduce `g hg`.

Use `⟨integrable_of_mem_schwartzBruhatPi hg, integrable_of_mem_schwartzBruhatPi (adelicFourierPi_mem_schwartzBruhatPi hg), fun z => ?_⟩` and prove the remaining obligations. Conclude with `congrFun (adelicFourierPi_adelicFourierPi hg) z`.
-/
theorem selfDual_std : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.SelfDual (adeleMeasurePi K (ι := ι))
    (fun x y => ((adelicChar K (∑ i, x i * y i) : Circle) : ℂ)) := by
  refine selfDual_of_rich inferInstance _ ?_ (fun _ _ => Circle.norm_coe _) ?_
    (schwartzBruhatPi K ι : Set _) ?_ exists_bump
  · exact continuous_subtype_val.comp ((continuous_adelicChar (K := K)).comp
      (continuous_finsetSum _ fun i _ =>
        ((continuous_apply i).comp continuous_fst).mul ((continuous_apply i).comp continuous_snd)))
  · intro x y
    simp only [mul_comm]
  · intro g hg
    refine ⟨integrable_of_mem_schwartzBruhatPi hg,
      integrable_of_mem_schwartzBruhatPi (adelicFourierPi_mem_schwartzBruhatPi hg), fun z => ?_⟩
    exact congrFun (adelicFourierPi_adelicFourierPi hg) z

end Concrete

section Form

open NumberField IsDedekindDomain

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Take `⟨ξ, hξ⟩` from `GlobalTheory.CompanionTheory.AdeleDual.exists_eq_adelicChar_mul ψ hψ.1 hψ.2.2.1`. Establish `hξ0 : ξ ≠ 0`. Introduce and unpack `rfl`. Take `⟨x, hx⟩` from `hψ.2.2.2`. Apply `hx` to reduce the goal to its premises.

Rewrite using `[hξ x]`. Simplify using the standard rewrite rules. Establish `hAd : (ξ • B).det ≠ 0`. Rewrite using `[Matrix.det_smul]`. Conclude with `mul_ne_zero (pow_ne_zero _ hξ0) hd`.

Establish `hAs : (ξ • B).IsSymm`. Rewrite using `[Matrix.IsSymm, Matrix.transpose_smul, hB.eq]`. Use `set ψ₀ : AdeleRing (𝓞 K) K → ℂ := fun a => ((GroundTheory.Global.adelicChar K a : Circle) : ℂ) with hψ₀`. Use `set μ₀ := GroundTheory.Automorphic.GJMatrix.adeleMeasurePi K (ι := ι) with hμ₀`. Establish `h0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.SelfDual μ₀ (fun x y => ψ₀ (dotProduct x y))` using `selfDual_std`.

Use `set A := (ξ • B).map (algebraMap K (AdeleRing (𝓞 K) K)) with hA`. Establish `hu : IsUnit A.det` using `GlobalTheory.CompanionTheory.SW.SdCoord.isUnit_det_map _ hAd`. Establish `hHaar : (μ₀.map (GlobalTheory.CompanionTheory.SW.SdCoord.matE A hu)).IsAddHaarMeasure` using `(GlobalTheory.CompanionTheory.SW.SdCoord.matE A hu).isAddHaarMeasure_map μ₀`. Establish `hc : μ₀.map (fun x => Matrix.mulVec A x) = Measure.addHaarScalarFactor (μ₀.map (GlobalTheory.CompanionTheory.SW.SdCoord.matE A hu)) μ₀ • μ₀` using `Measure.isAddLeftInvariant_eq_smul (μ₀.map (GlobalTheory.CompanionTheory.SW.SdCoord.matE A hu)) μ₀`. Establish `h1` using `GlobalTheory.CompanionTheory.SW.SdCoord.selfDual_mat ψ₀ A (hAs.map _) hu μ₀ h0 _ hc`.

Establish `hform : (fun x y : ι → AdeleRing (𝓞 K) K => ψ₀ (dotProduct x (Matrix.mulVec A y))) = fun x y => ψ (dotProduct x (Matrix.mulVec (B.map (algebraMap K (AdeleRing (𝓞 K) K))) y))`. Use function extensionality and compare the values at `x y`. Rewrite using `[hξ, hA, GlobalTheory.CompanionTheory.SW.SdCoord.dot_smul]`. Rewrite `h1` using `[hform]`. Take `⟨μ₁, h2⟩ : ∃ μ₁ : Measure (ι → AdeleRing (𝓞 K) K), HeckeCharacterZeroLocus.SiegelWeilU.SelfDual μ₁ (fun x y => ψ (dotProduct x (Matrix.mulVec (B.map (algebraMap K (AdeleRing (𝓞 K) K))) y)))` from `⟨_, h1⟩`.

Use `⟨μ₁.map e.symm, ?_⟩` and prove the remaining obligations. Use `(GlobalTheory.CompanionTheory.SW.selfDual_transport W _ e _ (fun x y => ψ (dotProduct x (Matrix.mulVec (B.map (algebraMap K (AdeleRing (𝓞 K) K))) y)))).2 ?_` and prove the remaining obligations. Rewrite using `[Measure.map_map (map_continuous e).measurable (map_continuous e.symm).measurable]`. Establish `: (e ∘ e.symm) = id`. Use function extensionality and compare the values at `X`.

Conclude with `e.apply_symm_apply X`. Rewrite using `[this, Measure.map_id]`. Conclude with `h2`.
-/
theorem exists_selfDual_form (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ)
    (hψ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF K ψ) (B : Matrix ι ι K) (hB : B.IsSymm) (hd : B.det ≠ 0)
    {W : Type} [AddCommGroup W] [TopologicalSpace W] [IsTopologicalAddGroup W] [MeasurableSpace W]
    [BorelSpace W] (e : W ≃ₜ+ (ι → AdeleRing (𝓞 K) K)) :
    ∃ μ : Measure W, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.SelfDual μ (fun X Y =>
      ψ (dotProduct (e X) (Matrix.mulVec (B.map (algebraMap K (AdeleRing (𝓞 K) K))) (e Y)))) := by
  obtain ⟨ξ, hξ⟩ := GlobalTheory.CompanionTheory.AdeleDual.exists_eq_adelicChar_mul ψ hψ.1 hψ.2.2.1
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    obtain ⟨x, hx⟩ := hψ.2.2.2
    apply hx
    rw [hξ x]
    simp
  have hAd : (ξ • B).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hξ0) hd
  have hAs : (ξ • B).IsSymm := by
    rw [Matrix.IsSymm, Matrix.transpose_smul, hB.eq]
  set ψ₀ : AdeleRing (𝓞 K) K → ℂ := fun a => ((GroundTheory.Global.adelicChar K a : Circle) : ℂ) with hψ₀
  set μ₀ := GroundTheory.Automorphic.GJMatrix.adeleMeasurePi K (ι := ι) with hμ₀
  have h0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.SelfDual μ₀ (fun x y => ψ₀ (dotProduct x y)) := selfDual_std
  set A := (ξ • B).map (algebraMap K (AdeleRing (𝓞 K) K)) with hA
  have hu : IsUnit A.det := GlobalTheory.CompanionTheory.SW.SdCoord.isUnit_det_map _ hAd
  have hHaar : (μ₀.map (GlobalTheory.CompanionTheory.SW.SdCoord.matE A hu)).IsAddHaarMeasure :=
    (GlobalTheory.CompanionTheory.SW.SdCoord.matE A hu).isAddHaarMeasure_map μ₀
  have hc : μ₀.map (fun x => Matrix.mulVec A x) =
      Measure.addHaarScalarFactor (μ₀.map (GlobalTheory.CompanionTheory.SW.SdCoord.matE A hu)) μ₀ • μ₀ :=
    Measure.isAddLeftInvariant_eq_smul (μ₀.map (GlobalTheory.CompanionTheory.SW.SdCoord.matE A hu)) μ₀
  have h1 := GlobalTheory.CompanionTheory.SW.SdCoord.selfDual_mat ψ₀ A (hAs.map _) hu μ₀ h0 _ hc
  have hform : (fun x y : ι → AdeleRing (𝓞 K) K => ψ₀ (dotProduct x (Matrix.mulVec A y))) =
      fun x y => ψ (dotProduct x (Matrix.mulVec (B.map (algebraMap K (AdeleRing (𝓞 K) K))) y)) := by
    funext x y
    rw [hξ, hA, GlobalTheory.CompanionTheory.SW.SdCoord.dot_smul]
  rw [hform] at h1
  obtain ⟨μ₁, h2⟩ : ∃ μ₁ : Measure (ι → AdeleRing (𝓞 K) K), HeckeCharacterZeroLocus.SiegelWeilU.SelfDual μ₁ (fun x y =>
      ψ (dotProduct x (Matrix.mulVec (B.map (algebraMap K (AdeleRing (𝓞 K) K))) y))) := ⟨_, h1⟩
  refine ⟨μ₁.map e.symm, ?_⟩
  refine (GlobalTheory.CompanionTheory.SW.selfDual_transport W _ e _ (fun x y =>
    ψ (dotProduct x (Matrix.mulVec (B.map (algebraMap K (AdeleRing (𝓞 K) K))) y)))).2 ?_
  rw [Measure.map_map (map_continuous e).measurable (map_continuous e.symm).measurable]
  have : (e ∘ e.symm) = id := by
    funext X
    exact e.apply_symm_apply X
  rw [this, Measure.map_id]
  exact h2

end Form

end GlobalTheory.CompanionTheory.Hypotheses₂.SdExist

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.Hypotheses₂.SdExist

end GlobalTheory.CompanionTheory.Hypotheses₂.SdExist
