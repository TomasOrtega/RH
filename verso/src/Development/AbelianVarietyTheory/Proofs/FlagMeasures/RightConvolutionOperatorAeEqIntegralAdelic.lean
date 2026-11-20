import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicUnitaryHaarBiInvariantStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightRegularRepUnitaryStronglyContinuousStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.ConvKernel

section General

variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {ν : Measure X} {μ : Measure Y}

/- English proof (translation)
Establish `hK' : AEStronglyMeasurable (fun p : X × Y => K p.1 p.2) ((ν.restrict s).prod μ)` using `hK.mono_ac (Measure.AbsolutelyContinuous.prod (Measure.absolutelyContinuous_of_le Measure.restrict_le_self) Measure.AbsolutelyContinuous.rfl)`. Establish `hm : AEStronglyMeasurable (fun p : X × Y => φ p.2 * K p.1 p.2) ((ν.restrict s).prod μ)` using `(hφ.1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd).mul hK'`. Use `⟨hm, ?_⟩` and prove the remaining obligations. Use `set M : ENNReal := ENNReal.ofReal C * (ν s) ^ (1 / (1 : ENNReal).toReal - 1 / (2 : ENNReal).toReal) with hM`. Establish `hMfin : M ≠ ⊤`.

Use `ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_` and prove the remaining obligations. Use `ENNReal.rpow_ne_top_of_nonneg ?_ hs.ne` and prove the remaining obligations. Evaluate the numerical expressions. Establish `hb : ∀ g, ∫⁻ x, ‖K x g‖ₑ ∂(ν.restrict s) ≤ M`. Introduce `g`.

Establish `e1 : ∫⁻ x, ‖K x g‖ₑ ∂(ν.restrict s) = eLpNorm (r g : X → ℂ) 1 (ν.restrict s)`. Rewrite using `[eLpNorm_one_eq_lintegral_enorm]`. Use `lintegral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [ae_restrict_of_ae (s := s) (hr g)] with x hx`. Rewrite using `[hx]`.

Establish `e2` using `eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := ν.restrict s) (p := 1) (q := 2) (f := (r g : X → ℂ)) (by norm_num) (Lp.aestronglyMeasurable (r g)).restrict`. Rewrite `e2` using `[Measure.restrict_apply_univ]`. Rewrite using `[e1]`. Use `e2.trans ?_` and prove the remaining obligations. Use `mul_le_mul' ?_ le_rfl` and prove the remaining obligations.

Use `(eLpNorm_mono_measure _ Measure.restrict_le_self).trans ?_` and prove the remaining obligations. Establish `h3` using `hC g`. Rewrite `h3` using `[Lp.norm_def]`. Rewrite using `[← ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top (r g))]`. Conclude with `ENNReal.ofReal_le_ofReal h3`.

Rewrite using `[hasFiniteIntegral_iff_enorm, lintegral_prod_symm _ hm.enorm]`. Combine the equalities or inequalities in the displayed calculation. Use `lintegral_mono fun g => ?_` and prove the remaining obligations. Simplify using `only [enorm_mul]`. Rewrite using `[lintegral_const_mul' _ _ enorm_ne_top]`.

Conclude with `mul_le_mul' le_rfl (hb g)`. Use `_ = (∫⁻ g, ‖φ g‖ₑ ∂μ) * M := lintegral_mul_const' _ _ hMfin`. Use `_ < ⊤ := ENNReal.mul_lt_top hφ.2 hMfin.lt_top`.
-/
theorem integrable_prod_restrict [SFinite ν] [SFinite μ] (K : X → Y → ℂ)
    (hK : AEStronglyMeasurable (fun p : X × Y => K p.1 p.2) (ν.prod μ))
    (r : Y → Lp ℂ 2 ν) (hr : ∀ g, (r g : X → ℂ) =ᵐ[ν] fun x => K x g) (C : ℝ)
    (hC : ∀ g, ‖r g‖ ≤ C) (φ : Y → ℂ) (hφ : Integrable φ μ) (s : Set X) (hs : ν s < ⊤) :
    Integrable (fun p : X × Y => φ p.2 * K p.1 p.2) ((ν.restrict s).prod μ) := by
  have hK' : AEStronglyMeasurable (fun p : X × Y => K p.1 p.2) ((ν.restrict s).prod μ) :=
    hK.mono_ac (Measure.AbsolutelyContinuous.prod
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self) Measure.AbsolutelyContinuous.rfl)
  have hm : AEStronglyMeasurable (fun p : X × Y => φ p.2 * K p.1 p.2) ((ν.restrict s).prod μ) :=
    (hφ.1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd).mul hK'
  refine ⟨hm, ?_⟩
  set M : ENNReal := ENNReal.ofReal C * (ν s) ^ (1 / (1 : ENNReal).toReal - 1 / (2 : ENNReal).toReal)
    with hM
  have hMfin : M ≠ ⊤ := by
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
    refine ENNReal.rpow_ne_top_of_nonneg ?_ hs.ne
    norm_num
  have hb : ∀ g, ∫⁻ x, ‖K x g‖ₑ ∂(ν.restrict s) ≤ M := by
    intro g
    have e1 : ∫⁻ x, ‖K x g‖ₑ ∂(ν.restrict s) = eLpNorm (r g : X → ℂ) 1 (ν.restrict s) := by
      rw [eLpNorm_one_eq_lintegral_enorm]
      refine lintegral_congr_ae ?_
      filter_upwards [ae_restrict_of_ae (s := s) (hr g)] with x hx
      rw [hx]
    have e2 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := ν.restrict s) (p := 1) (q := 2)
      (f := (r g : X → ℂ)) (by norm_num) (Lp.aestronglyMeasurable (r g)).restrict
    rw [Measure.restrict_apply_univ] at e2
    rw [e1]
    refine e2.trans ?_
    refine mul_le_mul' ?_ le_rfl
    refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans ?_
    have h3 := hC g
    rw [Lp.norm_def] at h3
    rw [← ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top (r g))]
    exact ENNReal.ofReal_le_ofReal h3
  rw [hasFiniteIntegral_iff_enorm, lintegral_prod_symm _ hm.enorm]
  calc ∫⁻ g, ∫⁻ x, ‖φ g * K x g‖ₑ ∂(ν.restrict s) ∂μ ≤ ∫⁻ g, ‖φ g‖ₑ * M ∂μ := by
        refine lintegral_mono fun g => ?_
        simp only [enorm_mul]
        rw [lintegral_const_mul' _ _ enorm_ne_top]
        exact mul_le_mul' le_rfl (hb g)
    _ = (∫⁻ g, ‖φ g‖ₑ ∂μ) * M := lintegral_mul_const' _ _ hMfin
    _ < ⊤ := ENNReal.mul_lt_top hφ.2 hMfin.lt_top

/- English proof (translation)
Establish `hI` using `integrable_prod_restrict K hK r hr C hC φ hφ`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `ae_of_forall_measure_lt_top_ae_restrict _ fun s _ hs => ?_` and prove the remaining obligations. Conclude with `(hI s hs).prod_right_ae`. Use `ae_eq_of_forall_setIntegral_eq_of_sigmaFinite (fun s _ hs => ?_) (fun s _ hs => ?_) (fun s hsm hs => ?_)` and prove the remaining obligations.

Conclude with `integrableOn_Lp_of_measure_ne_top t (by norm_num) hs.ne`. Conclude with `(hI s hs).integral_prod_left`. Establish `h` using `ht (indicatorConstLp 2 hsm hs.ne (1 : ℂ))`. Simplify using `only [L2.inner_indicatorConstLp_one] at h`. Rewrite using `[h, integral_integral_swap (f := fun x g => φ g * K x g) (hI s hs)]`.

Use `integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)` and prove the remaining obligations. Simplify using `only`. Rewrite using `[integral_const_mul]`. Use `congr 1`. Conclude with `integral_congr_ae (ae_restrict_of_ae (hr g))`.
-/
theorem weak_integral_ae_eq [SigmaFinite ν] [SFinite μ] (K : X → Y → ℂ)
    (hK : AEStronglyMeasurable (fun p : X × Y => K p.1 p.2) (ν.prod μ))
    (r : Y → Lp ℂ 2 ν) (hr : ∀ g, (r g : X → ℂ) =ᵐ[ν] fun x => K x g) (C : ℝ)
    (hC : ∀ g, ‖r g‖ ≤ C) (φ : Y → ℂ) (hφ : Integrable φ μ) (t : Lp ℂ 2 ν)
    (ht : ∀ u : Lp ℂ 2 ν, ⟪u, t⟫_ℂ = ∫ g, φ g * ⟪u, r g⟫_ℂ ∂μ) :
    (∀ᵐ x ∂ν, Integrable (fun g => φ g * K x g) μ) ∧
      (t : X → ℂ) =ᵐ[ν] fun x => ∫ g, φ g * K x g ∂μ := by
  have hI := integrable_prod_restrict K hK r hr C hC φ hφ
  refine ⟨?_, ?_⟩
  · refine ae_of_forall_measure_lt_top_ae_restrict _ fun s _ hs => ?_
    exact (hI s hs).prod_right_ae
  · refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite (fun s _ hs => ?_) (fun s _ hs => ?_)
      (fun s hsm hs => ?_)
    · exact integrableOn_Lp_of_measure_ne_top t (by norm_num) hs.ne
    · exact (hI s hs).integral_prod_left
    · have h := ht (indicatorConstLp 2 hsm hs.ne (1 : ℂ))
      simp only [L2.inner_indicatorConstLp_one] at h
      rw [h, integral_integral_swap (f := fun x g => φ g * K x g) (hI s hs)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      simp only
      rw [integral_const_mul]
      congr 1
      exact integral_congr_ae (ae_restrict_of_ae (hr g))

end General

/- English proof (translation)
Introduce `B φ T hT y`. Take `⟨hT2, hL, hS, -⟩` from `GlobalTheory.CongTop.adelic_topology B.I`. Take `⟨hl, -⟩` from `GlobalTheory.T.adelicUnitaryHaar_bi_invariant B.I B.μf`. Take `⟨-, -, hn, -, hext⟩` from `GlobalTheory.T.rightRegularRep_unitary_stronglyContinuous B`. Establish `: BorelSpace B.I.GA` using `inferInstance`.

Establish `: (B.I.muA B.μf).IsMulLeftInvariant` using `⟨hl⟩`. Establish `: SigmaFinite (B.I.muA B.μf)`. Unfold `AutInst.muA`. Use `infer_instance`. Establish `hq : Measure.QuasiMeasurePreserving (fun p : B.I.GA × B.I.GA => p.1 * p.2) (((B.I.muA B.μf).restrict B.fund).prod (B.I.muA B.μf)) (B.I.muA B.μf)` using `Measure.quasiMeasurePreserving_snd.comp (measurePreserving_prod_mul ((B.I.muA B.μf).restrict B.fund) (B.I.muA B.μf)).quasiMeasurePreserving`.

Conclude with `weak_integral_ae_eq (fun x g => B.I.ext y (x * g)) ((hext y).2.comp_quasiMeasurePreserving hq) (fun g => B.R g y) (fun g => B.R_spec g y) ‖y‖ (fun g => (hn g y).le) φ hT.1 (T y) (fun u => hT.2 u y)`.
-/
theorem rconv_eq_integral : ∀ (B : RowsAut) (φ : B.I.GA → ℂ) (T : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund), B.I.IsRConv B.μf B.fund B.R φ T → ∀ y : B.I.L2 B.μf B.fund, (∀ᵐ x ∂((B.I.muA B.μf).restrict B.fund), Integrable (fun g => φ g * B.I.ext y (x * g)) (B.I.muA B.μf)) ∧ (T y : B.I.GA → ℂ) =ᵐ[(B.I.muA B.μf).restrict B.fund] fun x => ∫ g, φ g * B.I.ext y (x * g) ∂(B.I.muA B.μf) := by
  intro B φ T hT y
  obtain ⟨hT2, hL, hS, -⟩ := GlobalTheory.CongTop.adelic_topology B.I
  obtain ⟨hl, -⟩ := GlobalTheory.T.adelicUnitaryHaar_bi_invariant B.I B.μf
  obtain ⟨-, -, hn, -, hext⟩ := GlobalTheory.T.rightRegularRep_unitary_stronglyContinuous B
  have : BorelSpace B.I.GA := inferInstance
  have : (B.I.muA B.μf).IsMulLeftInvariant := ⟨hl⟩
  have : SigmaFinite (B.I.muA B.μf) := by
    unfold AutInst.muA; infer_instance
  have hq : Measure.QuasiMeasurePreserving (fun p : B.I.GA × B.I.GA => p.1 * p.2)
      (((B.I.muA B.μf).restrict B.fund).prod (B.I.muA B.μf)) (B.I.muA B.μf) :=
    Measure.quasiMeasurePreserving_snd.comp
      (measurePreserving_prod_mul ((B.I.muA B.μf).restrict B.fund)
        (B.I.muA B.μf)).quasiMeasurePreserving
  exact weak_integral_ae_eq (fun x g => B.I.ext y (x * g))
    ((hext y).2.comp_quasiMeasurePreserving hq) (fun g => B.R g y) (fun g => B.R_spec g y) ‖y‖
    (fun g => (hn g y).le) φ hT.1 (T y) (fun u => hT.2 u y)

end GlobalTheory.ConvKernel
