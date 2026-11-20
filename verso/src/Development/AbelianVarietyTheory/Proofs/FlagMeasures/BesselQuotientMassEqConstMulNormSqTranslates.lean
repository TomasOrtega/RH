import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SobolevContinuousFormGardingVector
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothVectorWordActionContinuous
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerOfNormEq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFrameTranslatedPerpOfIsFrame
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HcTypeWContinuousUnitaryIrreducible
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DerivedActionDiscreteSeriesProperties
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrechetContinuousContinuousOnOrbitHasDerivAt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuotientMeasureRightInvariant
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryGroupMatGroupUnimodularStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSubgroupProductMeasureIsHaarStatement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet

noncomputable section

namespace GlobalTheory.BesselIsometry

section L2

open MeasureTheory Filter
open scoped InnerProductSpace Topology ENNReal

variable {X V : Type} [MeasurableSpace X] {ν : Measure X} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/- English proof (translation)
Use `continuous_iff_continuousAt.2 fun j => Metric.tendsto_nhds.2 fun δ hδ => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Establish `hfr : ∃ᶠ i in 𝓝 j, δ ≤ ‖F i - F j‖`. Simplify `hne` using `only [not_eventually, not_lt, dist_eq_norm]`. Use `haveI : NeBot (𝓝 j ⊓ 𝓟 {i | δ ≤ ‖F i - F j‖}) := frequently_iff_neBot.1 hfr`.

Establish `hb : ∀ i, δ ≤ ‖F i - F j‖ → ‖F i + F j‖ ^ 2 ≤ 4 * ‖F j‖ ^ 2 - δ ^ 2` using `fun i hi => by`. Establish `h1` using `parallelogram_law_with_norm ℂ (F i) (F j)`. Rewrite `h1` using `[hn i j]`. Use the polynomial consequences of the given equalities and inequalities. Establish `he : ∀ i, (F i + F j : Lp V 2 ν) =ᵐ[ν] fun x => f i x + f j x` using `fun i => by filter_upwards [Lp.coeFn_add (F i) (F j), hF i, hF j] with x h1 h2 h3`.

Rewrite using `[h1, Pi.add_apply, h2, h3]`. Establish `hE : ∀ i, eLpNorm (fun x => f i x + f j x) 2 ν = ENNReal.ofReal ‖F i + F j‖` using `fun i => by`. Rewrite using `[← eLpNorm_congr_ae (he i), Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]`. Establish `h1` using `Lp.eLpNorm_le_of_ae_tendsto (u := 𝓝 j ⊓ 𝓟 {i | δ ≤ ‖F i - F j‖}) (f := fun i x => f i x + f j x) (g := fun x => f j x + f j x) (p := 2) (μ := ν) (C := ENNReal.ofReal √(4 * ‖F j‖ ^ 2 - δ ^ 2)) (by filter_upwards [mem_inf_of_right (mem_principal_self _)] with i hi`. Rewrite using `[hE]`.

Conclude with `ENNReal.ofReal_le_ofReal (Real.le_sqrt_of_sq_le (hb i hi)))`. Use the proof step `(fun i => (Lp.aestronglyMeasurable _).congr (he i))`. Use the proof step `(hc.mono fun x hx => ((hx.tendsto j).add_const _).mono_left inf_le_left)`. Rewrite `h1` using `[hE, ENNReal.ofReal_le_ofReal_iff (Real.sqrt_nonneg _), ← two_smul ℂ, norm_smul]`. Take `⟨i, hi⟩` from `hfr.exists`.

Establish `h2` using `(sq_nonneg _).trans (hb i hi)`. Establish `h3` using `pow_le_pow_left₀ (by positivity) h1 2`. Rewrite `h3` using `[Real.sq_sqrt h2]`. Simplify using `only [Complex.norm_ofNat] at h3`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem continuous_Lp_two_of_const_norm_pointwise_continuous {ι : Type} [TopologicalSpace ι] [FirstCountableTopology ι] (F : ι → Lp V 2 ν) (f : ι → X → V)
    (hF : ∀ i, (F i : X → V) =ᵐ[ν] f i) (hn : ∀ i j, ‖F i‖ = ‖F j‖) (hc : ∀ᵐ x ∂ν, Continuous fun i => f i x) :
    Continuous F := by
  refine continuous_iff_continuousAt.2 fun j => Metric.tendsto_nhds.2 fun δ hδ => ?_
  by_contra hne
  have hfr : ∃ᶠ i in 𝓝 j, δ ≤ ‖F i - F j‖ := by
    simpa only [not_eventually, not_lt, dist_eq_norm] using hne
  haveI : NeBot (𝓝 j ⊓ 𝓟 {i | δ ≤ ‖F i - F j‖}) := frequently_iff_neBot.1 hfr
  have hb : ∀ i, δ ≤ ‖F i - F j‖ → ‖F i + F j‖ ^ 2 ≤ 4 * ‖F j‖ ^ 2 - δ ^ 2 := fun i hi => by
    have h1 := parallelogram_law_with_norm ℂ (F i) (F j)
    rw [hn i j] at h1
    nlinarith
  have he : ∀ i, (F i + F j : Lp V 2 ν) =ᵐ[ν] fun x => f i x + f j x := fun i => by
    filter_upwards [Lp.coeFn_add (F i) (F j), hF i, hF j] with x h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3]
  have hE : ∀ i, eLpNorm (fun x => f i x + f j x) 2 ν = ENNReal.ofReal ‖F i + F j‖ := fun i => by
    rw [← eLpNorm_congr_ae (he i), Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
  have h1 := Lp.eLpNorm_le_of_ae_tendsto (u := 𝓝 j ⊓ 𝓟 {i | δ ≤ ‖F i - F j‖}) (f := fun i x => f i x + f j x)
    (g := fun x => f j x + f j x) (p := 2) (μ := ν) (C := ENNReal.ofReal √(4 * ‖F j‖ ^ 2 - δ ^ 2))
    (by
      filter_upwards [mem_inf_of_right (mem_principal_self _)] with i hi
      rw [hE]
      exact ENNReal.ofReal_le_ofReal (Real.le_sqrt_of_sq_le (hb i hi)))
    (fun i => (Lp.aestronglyMeasurable _).congr (he i))
    (hc.mono fun x hx => ((hx.tendsto j).add_const _).mono_left inf_le_left)
  rw [hE, ENNReal.ofReal_le_ofReal_iff (Real.sqrt_nonneg _), ← two_smul ℂ, norm_smul] at h1
  obtain ⟨i, hi⟩ := hfr.exists
  have h2 := (sq_nonneg _).trans (hb i hi)
  have h3 := pow_le_pow_left₀ (by positivity) h1 2
  rw [Real.sq_sqrt h2] at h3
  simp only [Complex.norm_ofNat] at h3
  nlinarith

/- English proof (translation)
Establish `hf` using `(Lp.memLp f).norm`. Establish `hg` using `(Lp.memLp g).norm`. Establish `e : ⟪hf.toLp _, hg.toLp _⟫_ℝ = ∫ x, ‖f x‖ * ‖g x‖ ∂ν`. Rewrite using `[L2.inner_def]`. Use `integral_congr_ae ?_` and prove the remaining obligations.

Use `filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2`. Rewrite using `[h1, h2]`. Simplify using `[mul_comm]`. Establish `h1` using `real_inner_le_norm (hf.toLp _) (hg.toLp _)`. Rewrite `h1` using `[e, Lp.norm_toLp, Lp.norm_toLp, eLpNorm_norm, eLpNorm_norm, ← Lp.norm_def, ← Lp.norm_def]`.

Use `le_trans (integral_mono (L2.integrable_inner (𝕜 := ℂ) f g).norm (hf.integrable_mul hg) fun x => norm_inner_le_norm _ _) h1` and prove the remaining obligations.
-/
theorem integral_norm_inner_le (f g : Lp V 2 ν) : ∫ x, ‖⟪f x, g x⟫_ℂ‖ ∂ν ≤ ‖f‖ * ‖g‖ := by
  have hf := (Lp.memLp f).norm
  have hg := (Lp.memLp g).norm
  have e : ⟪hf.toLp _, hg.toLp _⟫_ℝ = ∫ x, ‖f x‖ * ‖g x‖ ∂ν := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
    rw [h1, h2]
    simp [mul_comm]
  have h1 := real_inner_le_norm (hf.toLp _) (hg.toLp _)
  rw [e, Lp.norm_toLp, Lp.norm_toLp, eLpNorm_norm, eLpNorm_norm, ← Lp.norm_def, ← Lp.norm_def] at h1
  refine le_trans (integral_mono (L2.integrable_inner (𝕜 := ℂ) f g).norm (hf.integrable_mul hg)
    fun x => norm_inner_le_norm _ _) h1

end L2

section Closable

open Formalism.MainNotions.S GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped InnerProductSpace Topology ENNReal

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {X V : Type} [MeasurableSpace X] {ν : Measure X} [SigmaFinite ν]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/- English proof (translation)
Establish `hemb` using `(Formalism.REAL.isClosedEmbeddingMatrix n ε).1`. Use `haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) := inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))`. Use `haveI : SecondCountableTopology (Formalism.REAL.UJ ε) := hemb.isEmbedding.secondCountableTopology`. Use `haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))`. Use `haveI : LocallyCompactSpace (Formalism.REAL.UJ ε) := hemb.locallyCompactSpace`.

Use `haveI : SigmaFinite (Formalism.REAL.muG ε) := inferInstance`. Establish `hmul : ∀ (g : Formalism.REAL.UJ ε) (v : H), σ (umat g) (σ (umat g⁻¹) v) = v`. Introduce `g v`. Establish `e : σ (umat g * umat g⁻¹) = _` using `hσ.1.2 _ g.2 _ (g⁻¹).2`. Establish `e1 : umat g * umat g⁻¹ = 1` using `Units.mul_inv g.1`.

Rewrite `e` using `[e1, hσ.1.1]`. Conclude with `(congrArg (fun T : H →L[ℂ] H => T v) e).symm`. Establish `h1 : ∀ g : Formalism.REAL.UJ ε, ∀ v ∈ D, ∀ w ∈ D, ⟪A (σ (umat g) v), A (σ (umat g) w)⟫_ℂ = ⟪A v, A w⟫_ℂ`. Introduce `g v hv w hw`. Rewrite using `[inner_eq_sum_norm_sq_div_four, inner_eq_sum_norm_sq_div_four]`.

Simplify using `only [← map_smul, ← map_add, ← map_sub]`. Rewrite using `[hn g _ (D.add_mem hv hw), hn g _ (D.sub_mem hv hw), hn g _ (D.sub_mem hv (D.smul_mem _ hw)), hn g _ (D.add_mem hv (D.smul_mem _ hw))]`. Establish `key : ∀ v ∈ D, ⟪A v, f⟫_ℂ = 0`. Introduce `v hv`. Establish `hcA : Continuous fun g : Formalism.REAL.UJ ε => A (σ (umat g) v)` using `continuous_Lp_two_of_const_norm_pointwise_continuous _ (fun g => a (σ (umat g) v)) (fun g => hA _ (hD g v hv)) (fun g g' => by rw [hn g v hv, hn g' v hv]) (hp.mono fun x hx => hx.1 v hv)`.

Establish `hc : ∀ y : Lp V 2 ν, Continuous fun g : Formalism.REAL.UJ ε => ⟪A (σ (umat g⁻¹) v), y⟫_ℂ` using `fun y => (hcA.comp continuous_inv).inner continuous_const`. Establish `h0` using `eq_zero_of_forall_test (F := fun g : Formalism.REAL.UJ ε => ⟪A (σ (umat g⁻¹) v), f⟫_ℂ) (hc f) (by`. Introduce `φ hφ`. Establish `hψi : Integrable (fun g : Formalism.REAL.UJ ε => φ (umat g)) (Formalism.REAL.muG ε)`. Simplify using `using hφ.integrable (F := fun _ : Formalism.REAL.UJ ε => (1 : ℝ)) continuous_const`.

Use `set c : ℝ := (∫ g : Formalism.REAL.UJ ε, ‖φ (umat g)‖ ∂(Formalism.REAL.muG ε)) * ‖A v‖ with hcdef`. Set `p : H → X → ℂ` to `fun w x => ⟪A v x, a (gard ε σ φ w) x⟫_ℂ`. Establish `hP : ∀ w ∈ D, Integrable (p w) ν ∧ ∫ x, ‖p w x‖ ∂ν ≤ c * ‖A w‖ ∧ ∫ x, p w x ∂ν = ∫ g : Formalism.REAL.UJ ε, φ (umat g) • ⟪A (σ (umat g⁻¹) v), A w⟫_ℂ ∂(Formalism.REAL.muG ε)`. Introduce `w hw`. Set `K : Formalism.REAL.UJ ε × X → ℂ` to `fun q => φ (umat q.1) • ⟪A v q.2, a (σ (umat q.1) w) q.2⟫_ℂ`.

Establish `hKm : AEStronglyMeasurable K ((Formalism.REAL.muG ε).prod ν)` using `hψi.aestronglyMeasurable.comp_fst.smul ((Lp.aestronglyMeasurable (A v)).comp_snd.inner (hm w hw))`. Establish `hae : ∀ g : Formalism.REAL.UJ ε, (fun x => ⟪A v x, A (σ (umat g) w) x⟫_ℂ) =ᵐ[ν] fun x => ⟪A v x, a (σ (umat g) w) x⟫_ℂ` using `fun g => (hA _ (hD g w hw)).mono fun x hx => by simp only [hx]`. Establish `hKb : ∀ g : Formalism.REAL.UJ ε, ∫ x, ‖K (g, x)‖ ∂ν ≤ ‖φ (umat g)‖ * (‖A v‖ * ‖A w‖)` using `fun g => by`. Simplify using `only [K, norm_smul, integral_const_mul]`. Use `mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)` and prove the remaining obligations.

Rewrite using `[← hn g w hw]`. Use `le_trans (le_of_eq (integral_congr_ae ?_)) (integral_norm_inner_le _ _)` and prove the remaining obligations. Conclude with `(hae g).mono fun x hx => congrArg norm hx.symm`. Establish `hK : Integrable K ((Formalism.REAL.muG ε).prod ν)`. Rewrite using `[integrable_prod_iff hKm]`.

Use `⟨Eventually.of_forall fun g => ((L2.integrable_inner (𝕜 := ℂ) _ _).congr (hae g)).smul (φ (umat g)), Integrable.mono' (hψi.norm.mul_const (‖A v‖ * ‖A w‖)) hKm.norm.integral_prod_right' (Eventually.of_forall fun g => ?_)⟩` and prove the remaining obligations. Rewrite using `[Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg _)]`. Conclude with `hKb g`. Establish `e : p w =ᵐ[ν] fun x => ∫ g, K (g, x) ∂(Formalism.REAL.muG ε)` using `hp.mono fun x hx => (hx.2 _ φ hφ).2 w hw`. Use `⟨hK.integral_prod_right.congr e.symm, ?_, ?_⟩` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[integral_congr_ae e, ← integral_integral_swap (f := fun g x => K (g, x)) hK]`. Use `congr 1`. Use function extensionality and compare the values at `g`. Simplify using `only [K]`.

Rewrite using `[integral_smul, ← integral_congr_ae (hae g), ← L2.inner_def, ← h1 g _ (hD g⁻¹ v hv) w hw, hmul]`. Establish `hsub : ∀ w w' x, p (w - w') x = p w x - p w' x` using `fun w w' x => by`. Simplify using `only [p, gard_eq hσ hφ, map_sub, Pi.sub_apply, inner_sub_right]`. Establish `hlim : ∀ᵐ x ∂ν, Tendsto (fun i => p (u i) x) atTop (𝓝 0)` using `hp.mono fun x hx => by`. Take `⟨C, hC⟩` from `(hx.2 (A v x) φ hφ).1`.

Use `squeeze_zero_norm (fun i => hC (u i)) ?_` and prove the remaining obligations. Simplify using `using hu0.norm.const_mul C`. Establish `hfat : ∀ i, ∫ x, ‖p (u i) x‖ ∂ν ≤ c * ‖A (u i) - f‖` using `fun i => by`. Establish `h2` using `Lp.eLpNorm_lim_le_liminf_eLpNorm (μ := ν) (p := 1) (f := fun j => p (u i - u j)) (fun j => (hP _ (D.sub_mem (hu i) (hu j))).1.aestronglyMeasurable) (p (u i)) (hlim.mono fun x hx => by simpa only [hsub, sub_zero] using hx.const_sub (p (u i) x))`. Simplify using `only [eLpNorm_one_eq_lintegral_enorm] at h2`.

Establish `h3 : Tendsto (fun j => ENNReal.ofReal (c * ‖A (u i - u j)‖)) atTop (𝓝 (ENNReal.ofReal (c * ‖A (u i) - f‖)))`. Simplify using `only [map_sub]`. Conclude with `ENNReal.tendsto_ofReal ((hf.const_sub _).norm.const_mul c)`. Establish `h4` using `h2.trans ((liminf_le_liminf (Eventually.of_forall fun j => by`. Rewrite using `[← ofReal_integral_norm_eq_lintegral_enorm (hP _ (D.sub_mem (hu i) (hu j))).1]`.

Conclude with `ENNReal.ofReal_le_ofReal (hP _ (D.sub_mem (hu i) (hu j))).2.1)).trans h3.liminf_eq.le)`. Rewrite `h4` using `[← ofReal_integral_norm_eq_lintegral_enorm (hP _ (hu i)).1, ENNReal.ofReal_le_ofReal_iff (mul_nonneg (mul_nonneg (integral_nonneg fun _ => norm_nonneg _) (norm_nonneg _)) (norm_nonneg _))]`. Then use the resulting hypothesis. Establish `t3 : Tendsto (fun i => c * ‖A (u i) - f‖) atTop (𝓝 0)`. Simplify using `using (tendsto_iff_norm_sub_tendsto_zero.1 hf).const_mul c`. Establish `t1 : Tendsto (fun i => ∫ x, p (u i) x ∂ν) atTop (𝓝 0)` using `squeeze_zero_norm (fun i => (norm_integral_le_integral_norm _).trans (hfat i)) t3`.

Establish `t2 : Tendsto (fun i => ∫ x, p (u i) x ∂ν) atTop (𝓝 (∫ g : Formalism.REAL.UJ ε, φ (umat g) • ⟪A (σ (umat g⁻¹) v), f⟫_ℂ ∂(Formalism.REAL.muG ε)))`. Rewrite using `[tendsto_iff_norm_sub_tendsto_zero]`. Use `squeeze_zero (fun _ => norm_nonneg _) (fun i => ?_) t3` and prove the remaining obligations. Rewrite using `[(hP _ (hu i)).2.2, ← integral_sub (hφ.integrable (hc _)) (hφ.integrable (hc _)), hcdef, mul_assoc, ← integral_mul_const]`. Use `norm_integral_le_of_norm_le (hψi.norm.mul_const _) (Eventually.of_forall fun g => ?_)` and prove the remaining obligations.

Rewrite using `[← smul_sub, norm_smul, ← inner_sub_right, ← hn g⁻¹ v hv]`. Conclude with `mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (norm_nonneg _)`. Conclude with `tendsto_nhds_unique t2 t1)`. Establish `e : σ (umat (1 : Formalism.REAL.UJ ε)⁻¹) v = v`. Rewrite using `[inv_one]`.

Use `show σ 1 v = v`. Rewrite using `[hσ.1.1]`. Both sides reduce to the same expression. Simplify `h0` using `only [e]`. Establish `t` using `hf.inner (𝕜 := ℂ) (tendsto_const_nhds (x := f))`.

Simplify using `only [key _ (hu _)] at t`. Conclude with `inner_self_eq_zero.1 (tendsto_nhds_unique t tendsto_const_nhds)`.
-/
theorem closable (hσ : IsURepOn (UJset ε) σ) (D : Submodule ℂ H) (a : H →ₗ[ℂ] (X → V)) (A : H →ₗ[ℂ] Lp V 2 ν)
    (hD : ∀ g : Formalism.REAL.UJ ε, ∀ v ∈ D, σ (umat g) v ∈ D) (hA : ∀ v ∈ D, (A v : X → V) =ᵐ[ν] a v)
    (hn : ∀ g : Formalism.REAL.UJ ε, ∀ v ∈ D, ‖A (σ (umat g) v)‖ = ‖A v‖)
    (hm : ∀ v ∈ D, AEStronglyMeasurable (fun p : Formalism.REAL.UJ ε × X => a (σ (umat p.1) v) p.2)
      ((Formalism.REAL.muG ε).prod ν))
    (hp : ∀ᵐ x ∂ν, (∀ v ∈ D, Continuous fun g : Formalism.REAL.UJ ε => a (σ (umat g) v) x) ∧
      ∀ (ξ : V) φ, IsTest φ → (∃ C : ℝ, ∀ w, ‖⟪ξ, a (gard ε σ φ w) x⟫_ℂ‖ ≤ C * ‖w‖) ∧
        ∀ v ∈ D, ⟪ξ, a (gard ε σ φ v) x⟫_ℂ =
          ∫ g : Formalism.REAL.UJ ε, φ (umat g) • ⟪ξ, a (σ (umat g) v) x⟫_ℂ ∂(Formalism.REAL.muG ε))
    (u : ℕ → H) (f : Lp V 2 ν) (hu : ∀ i, u i ∈ D) (hu0 : Tendsto u atTop (𝓝 0))
    (hf : Tendsto (fun i => A (u i)) atTop (𝓝 f)) : f = 0 := by
  have hemb := (Formalism.REAL.isClosedEmbeddingMatrix n ε).1
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Formalism.REAL.UJ ε) := hemb.isEmbedding.secondCountableTopology
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  haveI : LocallyCompactSpace (Formalism.REAL.UJ ε) := hemb.locallyCompactSpace
  haveI : SigmaFinite (Formalism.REAL.muG ε) := inferInstance
  have hmul : ∀ (g : Formalism.REAL.UJ ε) (v : H), σ (umat g) (σ (umat g⁻¹) v) = v := by
    intro g v
    have e : σ (umat g * umat g⁻¹) = _ := hσ.1.2 _ g.2 _ (g⁻¹).2
    have e1 : umat g * umat g⁻¹ = 1 := Units.mul_inv g.1
    rw [e1, hσ.1.1] at e
    exact (congrArg (fun T : H →L[ℂ] H => T v) e).symm
  have h1 : ∀ g : Formalism.REAL.UJ ε, ∀ v ∈ D, ∀ w ∈ D, ⟪A (σ (umat g) v), A (σ (umat g) w)⟫_ℂ = ⟪A v, A w⟫_ℂ := by
    intro g v hv w hw
    rw [inner_eq_sum_norm_sq_div_four, inner_eq_sum_norm_sq_div_four]
    simp only [← map_smul, ← map_add, ← map_sub]
    rw [hn g _ (D.add_mem hv hw), hn g _ (D.sub_mem hv hw), hn g _ (D.sub_mem hv (D.smul_mem _ hw)),
      hn g _ (D.add_mem hv (D.smul_mem _ hw))]
  have key : ∀ v ∈ D, ⟪A v, f⟫_ℂ = 0 := by
    intro v hv
    have hcA : Continuous fun g : Formalism.REAL.UJ ε => A (σ (umat g) v) :=
      continuous_Lp_two_of_const_norm_pointwise_continuous _ (fun g => a (σ (umat g) v)) (fun g => hA _ (hD g v hv))
        (fun g g' => by rw [hn g v hv, hn g' v hv]) (hp.mono fun x hx => hx.1 v hv)
    have hc : ∀ y : Lp V 2 ν, Continuous fun g : Formalism.REAL.UJ ε => ⟪A (σ (umat g⁻¹) v), y⟫_ℂ := fun y =>
      (hcA.comp continuous_inv).inner continuous_const
    have h0 := eq_zero_of_forall_test (F := fun g : Formalism.REAL.UJ ε => ⟪A (σ (umat g⁻¹) v), f⟫_ℂ) (hc f) (by
      intro φ hφ
      have hψi : Integrable (fun g : Formalism.REAL.UJ ε => φ (umat g)) (Formalism.REAL.muG ε) := by
        simpa using hφ.integrable (F := fun _ : Formalism.REAL.UJ ε => (1 : ℝ)) continuous_const
      set c : ℝ := (∫ g : Formalism.REAL.UJ ε, ‖φ (umat g)‖ ∂(Formalism.REAL.muG ε)) * ‖A v‖ with hcdef
      let p : H → X → ℂ := fun w x => ⟪A v x, a (gard ε σ φ w) x⟫_ℂ
      have hP : ∀ w ∈ D, Integrable (p w) ν ∧ ∫ x, ‖p w x‖ ∂ν ≤ c * ‖A w‖ ∧
          ∫ x, p w x ∂ν = ∫ g : Formalism.REAL.UJ ε, φ (umat g) • ⟪A (σ (umat g⁻¹) v), A w⟫_ℂ ∂(Formalism.REAL.muG ε) := by
        intro w hw
        let K : Formalism.REAL.UJ ε × X → ℂ := fun q => φ (umat q.1) • ⟪A v q.2, a (σ (umat q.1) w) q.2⟫_ℂ
        have hKm : AEStronglyMeasurable K ((Formalism.REAL.muG ε).prod ν) :=
          hψi.aestronglyMeasurable.comp_fst.smul ((Lp.aestronglyMeasurable (A v)).comp_snd.inner (hm w hw))
        have hae : ∀ g : Formalism.REAL.UJ ε, (fun x => ⟪A v x, A (σ (umat g) w) x⟫_ℂ) =ᵐ[ν]
            fun x => ⟪A v x, a (σ (umat g) w) x⟫_ℂ := fun g => (hA _ (hD g w hw)).mono fun x hx => by simp only [hx]
        have hKb : ∀ g : Formalism.REAL.UJ ε, ∫ x, ‖K (g, x)‖ ∂ν ≤ ‖φ (umat g)‖ * (‖A v‖ * ‖A w‖) := fun g => by
          simp only [K, norm_smul, integral_const_mul]
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          rw [← hn g w hw]
          refine le_trans (le_of_eq (integral_congr_ae ?_)) (integral_norm_inner_le _ _)
          exact (hae g).mono fun x hx => congrArg norm hx.symm
        have hK : Integrable K ((Formalism.REAL.muG ε).prod ν) := by
          rw [integrable_prod_iff hKm]
          refine ⟨Eventually.of_forall fun g => ((L2.integrable_inner (𝕜 := ℂ) _ _).congr (hae g)).smul (φ (umat g)),
            Integrable.mono' (hψi.norm.mul_const (‖A v‖ * ‖A w‖)) hKm.norm.integral_prod_right'
              (Eventually.of_forall fun g => ?_)⟩
          rw [Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg _)]
          exact hKb g
        have e : p w =ᵐ[ν] fun x => ∫ g, K (g, x) ∂(Formalism.REAL.muG ε) := hp.mono fun x hx => (hx.2 _ φ hφ).2 w hw
        refine ⟨hK.integral_prod_right.congr e.symm, ?_, ?_⟩
        · calc ∫ x, ‖p w x‖ ∂ν = ∫ x, ‖∫ g, K (g, x) ∂(Formalism.REAL.muG ε)‖ ∂ν :=
                integral_congr_ae (e.mono fun x hx => congrArg norm hx)
            _ ≤ ∫ x, ∫ g, ‖K (g, x)‖ ∂(Formalism.REAL.muG ε) ∂ν :=
                integral_mono hK.integral_prod_right.norm hK.integral_norm_prod_right
                  fun x => norm_integral_le_integral_norm _
            _ = ∫ g, ∫ x, ‖K (g, x)‖ ∂ν ∂(Formalism.REAL.muG ε) :=
                (integral_integral_swap (f := fun g x => ‖K (g, x)‖) hK.norm).symm
            _ ≤ ∫ g : Formalism.REAL.UJ ε, ‖φ (umat g)‖ * (‖A v‖ * ‖A w‖) ∂(Formalism.REAL.muG ε) :=
                integral_mono hK.integral_norm_prod_left (hψi.norm.mul_const _) hKb
            _ = c * ‖A w‖ := by rw [integral_mul_const, hcdef, mul_assoc]
        · rw [integral_congr_ae e, ← integral_integral_swap (f := fun g x => K (g, x)) hK]
          congr 1
          funext g
          simp only [K]
          rw [integral_smul, ← integral_congr_ae (hae g), ← L2.inner_def, ← h1 g _ (hD g⁻¹ v hv) w hw, hmul]
      have hsub : ∀ w w' x, p (w - w') x = p w x - p w' x := fun w w' x => by
        simp only [p, gard_eq hσ hφ, map_sub, Pi.sub_apply, inner_sub_right]
      have hlim : ∀ᵐ x ∂ν, Tendsto (fun i => p (u i) x) atTop (𝓝 0) := hp.mono fun x hx => by
        obtain ⟨C, hC⟩ := (hx.2 (A v x) φ hφ).1
        refine squeeze_zero_norm (fun i => hC (u i)) ?_
        simpa using hu0.norm.const_mul C
      have hfat : ∀ i, ∫ x, ‖p (u i) x‖ ∂ν ≤ c * ‖A (u i) - f‖ := fun i => by
        have h2 := Lp.eLpNorm_lim_le_liminf_eLpNorm (μ := ν) (p := 1) (f := fun j => p (u i - u j))
          (fun j => (hP _ (D.sub_mem (hu i) (hu j))).1.aestronglyMeasurable) (p (u i))
          (hlim.mono fun x hx => by simpa only [hsub, sub_zero] using hx.const_sub (p (u i) x))
        simp only [eLpNorm_one_eq_lintegral_enorm] at h2
        have h3 : Tendsto (fun j => ENNReal.ofReal (c * ‖A (u i - u j)‖)) atTop
            (𝓝 (ENNReal.ofReal (c * ‖A (u i) - f‖))) := by
          simp only [map_sub]
          exact ENNReal.tendsto_ofReal ((hf.const_sub _).norm.const_mul c)
        have h4 := h2.trans ((liminf_le_liminf (Eventually.of_forall fun j => by
          rw [← ofReal_integral_norm_eq_lintegral_enorm (hP _ (D.sub_mem (hu i) (hu j))).1]
          exact ENNReal.ofReal_le_ofReal (hP _ (D.sub_mem (hu i) (hu j))).2.1)).trans h3.liminf_eq.le)
        rwa [← ofReal_integral_norm_eq_lintegral_enorm (hP _ (hu i)).1, ENNReal.ofReal_le_ofReal_iff
          (mul_nonneg (mul_nonneg (integral_nonneg fun _ => norm_nonneg _) (norm_nonneg _)) (norm_nonneg _))] at h4
      have t3 : Tendsto (fun i => c * ‖A (u i) - f‖) atTop (𝓝 0) := by
        simpa using (tendsto_iff_norm_sub_tendsto_zero.1 hf).const_mul c
      have t1 : Tendsto (fun i => ∫ x, p (u i) x ∂ν) atTop (𝓝 0) :=
        squeeze_zero_norm (fun i => (norm_integral_le_integral_norm _).trans (hfat i)) t3
      have t2 : Tendsto (fun i => ∫ x, p (u i) x ∂ν) atTop
          (𝓝 (∫ g : Formalism.REAL.UJ ε, φ (umat g) • ⟪A (σ (umat g⁻¹) v), f⟫_ℂ ∂(Formalism.REAL.muG ε))) := by
        rw [tendsto_iff_norm_sub_tendsto_zero]
        refine squeeze_zero (fun _ => norm_nonneg _) (fun i => ?_) t3
        rw [(hP _ (hu i)).2.2, ← integral_sub (hφ.integrable (hc _)) (hφ.integrable (hc _)), hcdef, mul_assoc,
          ← integral_mul_const]
        refine norm_integral_le_of_norm_le (hψi.norm.mul_const _) (Eventually.of_forall fun g => ?_)
        rw [← smul_sub, norm_smul, ← inner_sub_right, ← hn g⁻¹ v hv]
        exact mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (norm_nonneg _)
      exact tendsto_nhds_unique t2 t1)
    have e : σ (umat (1 : Formalism.REAL.UJ ε)⁻¹) v = v := by
      rw [inv_one]
      show σ 1 v = v
      rw [hσ.1.1]; rfl
    simpa only [e] using h0
  have t := hf.inner (𝕜 := ℂ) (tendsto_const_nhds (x := f))
  simp only [key _ (hu _)] at t
  exact inner_self_eq_zero.1 (tendsto_nhds_unique t tendsto_const_nhds)

end Closable

section Quot

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Filter
open scoped InnerProductSpace ENNReal Topology

variable {k r : ℕ}

/- English proof (translation)
Take `⟨f, hpos, hf, hlt⟩` from `exists_pos_lintegral_lt_of_sigmaFinite μG (ε := 1) one_ne_zero`. Establish `hc : Continuous fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (fun i j => (Matrix.of p.2 * Matrix.of p.1) i j : Formalism.QuantumDeterminants.Mt k r)` using `Continuous.matrix_mul (X := Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) (A := fun p => (Matrix.of p.2 : Mx k r)) (B := fun p => (Matrix.of p.1 : Mx k r)) continuous_snd continuous_fst`. Establish `hm` using `hf.coe_nnreal_ennreal.comp hc.measurable`. Use `set F : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞ := fun x => ∫⁻ s, (f (fun i j => (Matrix.of s * Matrix.of x) i j) : ℝ≥0∞) ∂μS with hF`. Establish `hFm : Measurable F` using `hm.lintegral_prod_right'`.

Establish `hFi : ∫⁻ x, F x ∂ν ≠ ⊤`. Rewrite using `[← hq _ hf.coe_nnreal_ennreal]`. Conclude with `(hlt.trans ENNReal.one_lt_top).ne`. Establish `hFp : ∀ x, F x ≠ 0` using `fun x h0 => by`. Establish `h1` using `(lintegral_eq_zero_iff (hm.comp (measurable_prodMk_left (x := x)))).1 h0`.

Use `haveI : NeZero μS := ⟨hS⟩`. Take `⟨s, hs⟩` from `h1.exists`. Conclude with `(hpos _).ne' (ENNReal.coe_eq_zero.1 hs)`. Use `⟨⟨⟨fun m => {x | ((m + 1 : ℕ) : ℝ≥0∞)⁻¹ ≤ F x}, fun _ => trivial, fun m => ?_, ?_⟩⟩⟩` and prove the remaining obligations. Conclude with `(meas_ge_le_lintegral_div hFm.aemeasurable (by simp) (by simp)).trans_lt (ENNReal.div_lt_top hFi (by simp))`.

Use `Set.eq_univ_of_forall fun x => ?_` and prove the remaining obligations. Take `⟨m, hm⟩` from `ENNReal.exists_inv_nat_lt (hFp x)`. Conclude with `Set.mem_iUnion.2 ⟨m, le_trans (ENNReal.inv_le_inv.2 (by simp)) hm.le⟩`.
-/
theorem sigmaFinite_of_quot {μG μS ν : Measure (Formalism.QuantumDeterminants.Mt k r)} [SigmaFinite μG] [SFinite μS] (hS : μS ≠ 0)
    (hq : PI.BesselPeriodGGP.IsQuotMeas μG μS ν) : SigmaFinite ν := by
  obtain ⟨f, hpos, hf, hlt⟩ := exists_pos_lintegral_lt_of_sigmaFinite μG (ε := 1) one_ne_zero
  have hc : Continuous fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (fun i j => (Matrix.of p.2 * Matrix.of p.1) i j : Formalism.QuantumDeterminants.Mt k r) :=
    Continuous.matrix_mul (X := Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) (A := fun p => (Matrix.of p.2 : Mx k r))
      (B := fun p => (Matrix.of p.1 : Mx k r)) continuous_snd continuous_fst
  have hm := hf.coe_nnreal_ennreal.comp hc.measurable
  set F : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞ :=
    fun x => ∫⁻ s, (f (fun i j => (Matrix.of s * Matrix.of x) i j) : ℝ≥0∞) ∂μS with hF
  have hFm : Measurable F := hm.lintegral_prod_right'
  have hFi : ∫⁻ x, F x ∂ν ≠ ⊤ := by
    rw [← hq _ hf.coe_nnreal_ennreal]
    exact (hlt.trans ENNReal.one_lt_top).ne
  have hFp : ∀ x, F x ≠ 0 := fun x h0 => by
    have h1 := (lintegral_eq_zero_iff (hm.comp (measurable_prodMk_left (x := x)))).1 h0
    haveI : NeZero μS := ⟨hS⟩
    obtain ⟨s, hs⟩ := h1.exists
    exact (hpos _).ne' (ENNReal.coe_eq_zero.1 hs)
  refine ⟨⟨⟨fun m => {x | ((m + 1 : ℕ) : ℝ≥0∞)⁻¹ ≤ F x}, fun _ => trivial, fun m => ?_, ?_⟩⟩⟩
  · exact (meas_ge_le_lintegral_div hFm.aemeasurable (by simp) (by simp)).trans_lt
      (ENNReal.div_lt_top hFi (by simp))
  · refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨m, hm⟩ := ENNReal.exists_inv_nat_lt (hFp x)
    exact Set.mem_iUnion.2 ⟨m, le_trans (ENNReal.inv_le_inv.2 (by simp)) hm.le⟩

/- English proof (translation)
Take `⟨hz, hT, -, -, hW, hN, hG, hq⟩` from `hS`. Take `⟨hGG, hGH⟩` from `GlobalTheory.T.isMatGroup_GG_and_haar_right_invariant k r`. Take `⟨hGH1, hGH2⟩` from `hGH μG hG`. Take `⟨hSG, hsub, hS1, hS2⟩` from `GlobalTheory.T.besselSubgroup_product_measure_isHaar k r z μW μN hz hT hW hN`. Establish `hset : PI.QuotientSetting (GG k r) (Formalism.QuantumDeterminants.Sset k r z) μG (muSof μW μN) νq` using `⟨hGG, hSG, hsub, hGH1, hS1, hGH2, hS2, hq⟩`.

Establish `hae` using `GlobalTheory.QuotRightInv.ae_mem_of_quot hset`. Use `set A : Set (Formalism.QuantumDeterminants.Mt k r) := {x | Matrix.of x ∈ GG k r} with hA`. Establish `hAm : MeasurableSet A` using `IsClosed.measurableSet (α := Formalism.QuantumDeterminants.Mt k r) hGG.1`. Establish `hc : ContinuousOn (fun x : Formalism.QuantumDeterminants.Mt k r => ‖Φ (Matrix.of x)‖₊) A` using `hΦ.nnnorm`. Establish `hm : Measurable (A.piecewise (fun x : Formalism.QuantumDeterminants.Mt k r => ‖Φ (Matrix.of x)‖₊) (fun _ => 0))` using `hc.measurable_piecewise continuousOn_const hAm`.

Establish `hval : ∀ x : Formalism.QuantumDeterminants.Mt k r, Matrix.of x ∈ GG k r → A.piecewise (fun x : Formalism.QuantumDeterminants.Mt k r => ‖Φ (Matrix.of x)‖₊) (fun _ => 0) x = ‖Φ (Matrix.of x)‖₊` using `fun x hx => Set.piecewise_eq_of_mem _ _ _ hx`. Establish `key` using `GlobalTheory.QuotRightInv.quotInv _ _ _ _ _ _ hset _ (hm.coe_nnreal_ennreal.pow_const 2) (fun s hs x hx => by`. Rewrite using `[hval x hx, hval (fun i j => (s * Matrix.of x) i j) (hGG.2.2.1 s (hsub hs) _ hx)]`. Use `congr 2`. Conclude with `NNReal.eq (hinv s hs _ hx)) g hg`.

Unfold `PI.BesselPeriodGGP.l2SG`. Use `Eq.trans (lintegral_congr_ae (hae.mono fun x hx => ?_)) (key.trans (lintegral_congr_ae (hae.mono fun x hx => ?_)))` and prove the remaining obligations. Simplify using `only`. Rewrite using `[hval (fun i j => (Matrix.of x * g) i j) (hGG.2.2.1 _ hx g hg)]`. Both sides reduce to the same expression.

Simplify using `only`. Rewrite using `[hval x hx]`.
-/
theorem quotientMass_right_translation_invariant {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {u : ℕ → ℝ}
    {μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)} (hS : SideG k r z π u μW μN μG νq) {Φ : Mx k r → Wp}
    (hΦ : ContinuousOn Φ (GG k r)) (hinv : ∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, ∀ x ∈ GG k r, ‖Φ (s * x)‖ = ‖Φ x‖)
    {g : Mx k r} (hg : g ∈ GG k r) :
    PI.BesselPeriodGGP.l2SG νq (fun x => Φ (x * g)) = PI.BesselPeriodGGP.l2SG νq Φ := by
  classical
  obtain ⟨hz, hT, -, -, hW, hN, hG, hq⟩ := hS
  obtain ⟨hGG, hGH⟩ := GlobalTheory.T.isMatGroup_GG_and_haar_right_invariant k r
  obtain ⟨hGH1, hGH2⟩ := hGH μG hG
  obtain ⟨hSG, hsub, hS1, hS2⟩ := GlobalTheory.T.besselSubgroup_product_measure_isHaar k r z μW μN hz hT hW hN
  have hset : PI.QuotientSetting (GG k r) (Formalism.QuantumDeterminants.Sset k r z) μG (muSof μW μN) νq :=
    ⟨hGG, hSG, hsub, hGH1, hS1, hGH2, hS2, hq⟩
  have hae := GlobalTheory.QuotRightInv.ae_mem_of_quot hset
  set A : Set (Formalism.QuantumDeterminants.Mt k r) := {x | Matrix.of x ∈ GG k r} with hA
  have hAm : MeasurableSet A := IsClosed.measurableSet (α := Formalism.QuantumDeterminants.Mt k r) hGG.1
  have hc : ContinuousOn (fun x : Formalism.QuantumDeterminants.Mt k r => ‖Φ (Matrix.of x)‖₊) A := hΦ.nnnorm
  have hm : Measurable (A.piecewise (fun x : Formalism.QuantumDeterminants.Mt k r => ‖Φ (Matrix.of x)‖₊) (fun _ => 0)) :=
    hc.measurable_piecewise continuousOn_const hAm
  have hval : ∀ x : Formalism.QuantumDeterminants.Mt k r, Matrix.of x ∈ GG k r →
      A.piecewise (fun x : Formalism.QuantumDeterminants.Mt k r => ‖Φ (Matrix.of x)‖₊) (fun _ => 0) x = ‖Φ (Matrix.of x)‖₊ :=
    fun x hx => Set.piecewise_eq_of_mem _ _ _ hx
  have key := GlobalTheory.QuotRightInv.quotInv _ _ _ _ _ _ hset _ (hm.coe_nnreal_ennreal.pow_const 2) (fun s hs x hx => by
    rw [hval x hx, hval (fun i j => (s * Matrix.of x) i j) (hGG.2.2.1 s (hsub hs) _ hx)]
    congr 2
    exact NNReal.eq (hinv s hs _ hx)) g hg
  unfold PI.BesselPeriodGGP.l2SG
  refine Eq.trans (lintegral_congr_ae (hae.mono fun x hx => ?_))
    (key.trans (lintegral_congr_ae (hae.mono fun x hx => ?_)))
  · simp only
    rw [hval (fun i j => (Matrix.of x * g) i j) (hGG.2.2.1 _ hx g hg)]
    rfl
  · simp only
    rw [hval x hx]

open GlobalTheory.CWDeriv in

/- English proof (translation)
Establish `hD : DerFacts R` using `fun X hX => ⟨fun _ hv => ⟨GlobalTheory.DerivedAction.dsig_smooth hR.2 hX hv, GlobalTheory.DerivedAction.hasDerivAt_dsig hX hv⟩, fun _ hv _ hw => GlobalTheory.DerivedAction.dsig_skew hR.2 hX hv hw⟩`. Establish `hsm` using `PI.UnitaryGroupMassFormula.CapelliEig.smooth_right_action k r ε mu R.H R.σ hR.2 v hv`. Establish `h0 : (0 : R.H) ∈ R.sm` using `R.smSub.zero_mem`. Establish `hB0 : Bm 0 = 0` using `by simpa using hs 0 0 h0`. Introduce `g hg`.

Establish `h1` using `cw_tendsto hB (l := 𝓝[GG k r] g) (u := fun x => (1 : ℂ) • (R.σ x v - R.σ g v) - 0) (by filter_upwards [self_mem_nhdsWithin] with x hx`. Conclude with `sm_comb 1 (hsm x hx) (hsm g hg) h0)`. Use the proof step `(by`. Introduce `W hW`. Establish `h2` using `(smoothOnH_continuousOn (dsigW_orbit_smooth hR hD hv W hW) g hg).tendsto`.

Establish `hW0 : PI.UpqRep.dsigW (k` using `k) (r := r) R.σ W 0 = 0 := by`. Establish `h` using `dsigW_comb hD W hW 0 h0 h0 h0`. Simplify using `only [zero_smul, zero_sub, neg_zero] at h`. Rewrite `h` using `[eq_neg_iff_add_eq_zero, ← two_smul ℂ]`. Simplify using `using h`.

Rewrite `h2` using `[← tendsto_sub_nhds_zero_iff]`. Use `h2.congr' ?_` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with x hx`. Rewrite using `[dsigW_comb hD W hW 1 (hsm x hx) (hsm g hg) h0, hW0, one_smul, sub_zero])`. Use `tendsto_sub_nhds_zero_iff.mp (h1.congr' ?_)` and prove the remaining obligations.

Use `filter_upwards [self_mem_nhdsWithin] with x hx`. Rewrite using `[lin_comb ha hs 1 (hsm x hx) (hsm g hg) h0, hB0, one_smul, sub_zero]`.
-/
theorem continuousOn_orbit {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} {R : Rep k r}
    (hR : R.IsDS ε mu) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {Bm : R.H → V}
    (ha : ∀ v ∈ R.sm, ∀ w ∈ R.sm, Bm (v + w) = Bm v + Bm w) (hs : ∀ (a : ℂ), ∀ v ∈ R.sm, Bm (a • v) = a • Bm v)
    (hB : PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ Bm) {v : R.H} (hv : v ∈ R.sm) :
    ContinuousOn (fun g => Bm (R.σ g v)) (GG k r) := by
  have hD : DerFacts R := fun X hX =>
    ⟨fun _ hv => ⟨GlobalTheory.DerivedAction.dsig_smooth hR.2 hX hv, GlobalTheory.DerivedAction.hasDerivAt_dsig hX hv⟩,
      fun _ hv _ hw => GlobalTheory.DerivedAction.dsig_skew hR.2 hX hv hw⟩
  have hsm := PI.UnitaryGroupMassFormula.CapelliEig.smooth_right_action k r ε mu R.H R.σ hR.2 v hv
  have h0 : (0 : R.H) ∈ R.sm := R.smSub.zero_mem
  have hB0 : Bm 0 = 0 := by simpa using hs 0 0 h0
  intro g hg
  have h1 := cw_tendsto hB (l := 𝓝[GG k r] g) (u := fun x => (1 : ℂ) • (R.σ x v - R.σ g v) - 0)
    (by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact sm_comb 1 (hsm x hx) (hsm g hg) h0)
    (by
      intro W hW
      have h2 := (smoothOnH_continuousOn (dsigW_orbit_smooth hR hD hv W hW) g hg).tendsto
      have hW0 : PI.UpqRep.dsigW (k := k) (r := r) R.σ W 0 = 0 := by
        have h := dsigW_comb hD W hW 0 h0 h0 h0
        simp only [zero_smul, zero_sub, neg_zero] at h
        rw [eq_neg_iff_add_eq_zero, ← two_smul ℂ] at h
        simpa using h
      rw [← tendsto_sub_nhds_zero_iff] at h2
      refine h2.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      rw [dsigW_comb hD W hW 1 (hsm x hx) (hsm g hg) h0, hW0, one_smul, sub_zero])
  refine tendsto_sub_nhds_zero_iff.mp (h1.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [lin_comb ha hs 1 (hsm x hx) (hsm g hg) h0, hB0, one_smul, sub_zero]

end Quot

/- English proof (translation)
Establish `h` using `MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral (μ := ν) (p := 2) (f := fun x : Formalism.QuantumDeterminants.Mt k r => Φ (Matrix.of x)) two_ne_zero`. Simplify using `only [NNReal.coe_ofNat, ENNReal.rpow_ofNat, ENNReal.coe_ofNat] at h`. Conclude with `h.symm`.
-/
theorem quotientMass_eq_eLpNorm_sq {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] (ν : MeasureTheory.Measure (Formalism.QuantumDeterminants.Mt k r))
    (Φ : Formalism.FourierDecayAlt.ThreeDimData.Mx k r → Wp) :
    PI.BesselPeriodGGP.l2SG ν Φ = MeasureTheory.eLpNorm (fun x : Formalism.QuantumDeterminants.Mt k r => Φ (Matrix.of x)) 2 ν ^ 2 := by
  have h := MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral (μ := ν) (p := 2)
    (f := fun x : Formalism.QuantumDeterminants.Mt k r => Φ (Matrix.of x)) two_ne_zero
  simp only [NNReal.coe_ofNat, ENNReal.rpow_ofNat, ENNReal.coe_ofNat] at h
  exact h.symm

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

/- English proof (translation)
Introduce `k r ε mu R Wp _ _ _ _ z π u μW μN μG νq B w hR hS hB hw hfin`. Take `⟨-, hσ, -⟩` from `GlobalTheory.BesselMapOne.rep_of_isDSHpk hR.2`. Take `⟨P, ⟨⟨hP, hG⟩, -⟩, -, -, hU, hI, -⟩` from `hR.2`. Use `set σ' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (R.H →L[ℂ] R.H) := fun g => R.σ (P⁻¹ * g * P) with hσ'`. Establish `hd` using `(Matrix.isUnit_iff_isUnit_det P).1 hP`.

Establish `e : GlobalTheory.SmVec.trRep σ' P = R.σ` using `funext fun g => by`. Unfold `GlobalTheory.SmVec.trRep`. Simplify using `only [hσ']`. Use `congr 1`. Simplify using `only [← Matrix.mul_assoc, nonsing_inv_mul _ hd, Matrix.one_mul]`.

Rewrite using `[Matrix.mul_assoc, nonsing_inv_mul _ hd, Matrix.mul_one]`. Establish `hs : ∀ v, v ∈ R.sm ↔ v ∈ GlobalTheory.SmVec.smSub (Hpk k r) R.σ` using `GlobalTheory.BesselMapOne.smoothOnH_iff_mem (Formalism.QuantumDeterminants.GBasic.Hpk_herm k r) (Formalism.QuantumDeterminants.GBasic.Hpk_sq k r) hσ`. Establish `hGu : IsUnit (Hpk k r)` using `GlobalTheory.SmVec.gram_unit hP hG`. Establish `hsm` using `PI.UnitaryGroupMassFormula.CapelliEig.smooth_right_action k r ε mu R.H R.σ hR.2`. Take `⟨hGG, -⟩` from `GlobalTheory.T.isMatGroup_GG_and_haar_right_invariant k r`.

Establish `hconj : ∀ g : Formalism.REAL.UJ ε, P⁻¹ * umat g * P ∈ BranchingSupport.GG k r` using `fun g => GlobalTheory.SmVec.conj_mem_UH hP hG g.2`. Establish `hmul : ∀ g ∈ BranchingSupport.GG k r, ∀ h ∈ BranchingSupport.GG k r, ∀ v, R.σ g (R.σ h v) = R.σ (g * h) v` using `fun g hg h hh v => (GlobalTheory.SmVec.rep_mul hσ hg hh v).symm`. Establish `hS'` using `hS`. Take `⟨hz, hT, ⟨u₀, hπ⟩, -, hW, hN, hHG, hq⟩` from `hS'`. Take `⟨h0, h1⟩` from `Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hW hN`.

Establish `hae : ∀ᵐ x ∂νq, Matrix.of x ∈ BranchingSupport.GG k r` using `Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hHG.2.2.1 h0 h1 hq`. Use `haveI := hHG.1`. Use `haveI := (GlobalTheory.T.besselSubgroup_product_measure_isHaar k r z μW μN hz hT hW hN).2.2.1.1`. Use `haveI : SigmaFinite νq := sigmaFinite_of_quot h0 hq`. Use `haveI : SecondCountableTopology Wp := by haveI : ProperSpace Wp := FiniteDimensional.proper ℂ Wp infer_instance`.

Establish `hπu` using `(GlobalTheory.ThA.hcType_rep k r z u₀ Wp π hz hT hπ).2.2.2.1`. Set `L : R.smSub →ₗ[ℂ] Wp` to `{ toFun := fun x => B x map_add' := fun x y => hB.1 _ x.2 _ y.2 map_smul' := fun c x => hB.2.1 c _ x.2 }`. Take `⟨Bl, hBl⟩` from `L.exists_extend`. Establish `hBl' : ∀ v ∈ R.sm, Bl v = B v` using `fun v hv => LinearMap.congr_fun hBl ⟨v, hv⟩`. Set `a : R.H →ₗ[ℂ] (Mt k r → Wp)` to `LinearMap.pi fun x => Bl ∘ₗ (R.σ (Matrix.of x) : R.H →ₗ[ℂ] R.H)`.

Establish `ha : ∀ v ∈ R.sm, ∀ x : Mt k r, Matrix.of x ∈ BranchingSupport.GG k r → a v x = B (R.σ (Matrix.of x) v)` using `fun v hv x hx => hBl' _ (hsm v hv _ hx)`. Establish `hcont : ∀ v ∈ R.sm, ContinuousOn (fun g => B (R.σ g v)) (BranchingSupport.GG k r)` using `fun v hv => continuousOn_orbit hR hB.1 hB.2.1 hB.2.2.2 hv`. Establish `hl2 : ∀ v ∈ R.sm, PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g v)) = eLpNorm (a v) 2 νq ^ 2` using `fun v hv => by`. Rewrite using `[quotientMass_eq_eLpNorm_sq, eLpNorm_congr_ae (hae.mono fun x hx => ha v hv x hx)]`. Establish `hinv : ∀ v ∈ R.sm, ∀ g ∈ BranchingSupport.GG k r, eLpNorm (a (R.σ g v)) 2 νq = eLpNorm (a v) 2 νq` using `fun v hv g hg => by`.

Establish `h2` using `quotientMass_right_translation_invariant hS (hcont v hv) (by`. Introduce and unpack `_ ⟨h, hh, m, hm, rfl⟩ x hx`. Rewrite using `[← hmul _ (hGG.2.2.1 _ hh.1 _ hm.1) _ hx, hB.2.2.1 h hh m hm _ (hsm v hv x hx), norm_smul, hπu h hh]`. Simplify using `[Formalism.QuantumDeterminants.psi, Complex.norm_exp]) hg`. Establish `h3 : PI.BesselPeriodGGP.l2SG νq (fun x => B (R.σ x (R.σ g v))) = PI.BesselPeriodGGP.l2SG νq (fun x => B (R.σ (x * g) v))` using `lintegral_congr_ae (hae.mono fun x hx => by simp only [hmul _ hx _ hg])`.

Rewrite `h2` using `[← h3, hl2 _ (hsm v hv g hg), hl2 v hv]`. Conclude with `(ENNReal.pow_right_strictMono two_ne_zero).injective h2`. Establish `hAm : MeasurableSet {x : Mt k r | Matrix.of x ∈ BranchingSupport.GG k r}` using `IsClosed.measurableSet (α := Mt k r) hGG.1`. Establish `hmeas : ∀ v ∈ R.sm, AEStronglyMeasurable (a v) νq` using `fun v hv => by`. Establish `hc : ContinuousOn (fun x : Mt k r => B (R.σ (Matrix.of x) v)) {x : Mt k r | Matrix.of x ∈ BranchingSupport.GG k r}` using `hcont v hv`.

Establish `h2` using `hc.aestronglyMeasurable (μ := νq) hAm`. Rewrite `h2` using `[Measure.restrict_eq_self_of_ae_mem (s := {x : Mt k r | Matrix.of x ∈ BranchingSupport.GG k r}) hae]`. Conclude with `h2.congr (hae.mono fun x hx => (ha v hv x hx).symm)`. Use `set D := Formalism.FourierDecayAlt.ThreeDimData.DDsp (k := k) (r := r) R.σ w with hDdef`. Establish `hDs : ∀ v ∈ D, v ∈ R.sm` using `fun v hv => (Submodule.span_le (p := R.smSub)).2 (by rintro _ ⟨g, hg, rfl⟩; exact hsm w hw g hg) hv`.

Establish `hDst : ∀ g ∈ BranchingSupport.GG k r, ∀ v ∈ D, R.σ g v ∈ D` using `fun g hg v hv => (Submodule.span_le (p := D.comap (R.σ g : R.H →ₗ[ℂ] R.H))).2 (by`. Introduce and unpack `_ ⟨h, hh, rfl⟩`. Conclude with `Submodule.subset_span ⟨g * h, hGG.2.2.1 _ hg _ hh, (hmul g hg h hh w).symm⟩) hv`. Establish `hmem : ∀ v ∈ D, MemLp (a v) 2 νq` using `fun v hv => by`. Proceed by induction on `hv using Submodule.span_induction with`.

Consider the case `mem y hy`. Take `⟨g, hg, rfl⟩` from `hy`. Use `⟨hmeas _ (hsm w hw g hg), ?_⟩` and prove the remaining obligations. Rewrite using `[hinv w hw g hg]`. Rewrite `hfin` using `[hl2 w hw]`.

Conclude with `lt_top_iff_ne_top.2 fun h => hfin (by rw [h]; simp)`. Consider the case `zero => rw [map_zero]`. Conclude with `MemLp.zero`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `hx.add hy`.

Consider the case `smul c x _ hx => rw [map_smul]`. Conclude with `hx.const_smul c`. Set `A₀ : D →ₗ[ℂ] Lp Wp 2 νq` to `{ toFun := fun v => (hmem v v.2).toLp _ map_add' := fun v w => by`. Rewrite using `[← MemLp.toLp_add]`. Use `congr 1`.

Simplify using the standard rewrite rules. Use the proof step `map_smul' := fun c w => by`. Rewrite using `[RingHom.id_apply, ← MemLp.toLp_const_smul]`. Use `congr 1`. Simplify using `}`.

Take `⟨A, hA⟩` from `A₀.exists_extend`. Establish `hA' : ∀ v (hv : v ∈ D), A v = (hmem v hv).toLp _` using `fun v hv => LinearMap.congr_fun hA ⟨v, hv⟩`. Establish `hAn : ∀ v ∈ D, ‖A v‖ = (eLpNorm (a v) 2 νq).toReal` using `fun v hv => by rw [hA' v hv, Lp.norm_toLp]`. Establish `hD' : ∀ g : Formalism.REAL.UJ ε, ∀ v ∈ D, σ' (umat g) v ∈ D` using `fun g => hDst _ (hconj g)`. Establish `hn' : ∀ g : Formalism.REAL.UJ ε, ∀ v ∈ D, ‖A (σ' (umat g) v)‖ = ‖A v‖` using `fun g v hv => by`.

Rewrite using `[hAn _ (hD' g v hv), hAn v hv]`. Conclude with `congrArg _ (hinv v (hDs v hv) _ (hconj g))`. Establish `c1 : Continuous fun g : Formalism.REAL.UJ ε => P⁻¹ * umat g * P` using `(continuous_const.matrix_mul GlobalTheory.SmVec.continuous_umat).matrix_mul continuous_const`. Establish `hval : ∀ v ∈ D, ∀ (g : Formalism.REAL.UJ ε) (x : Mt k r), Matrix.of x ∈ BranchingSupport.GG k r → a (σ' (umat g) v) x = B (R.σ (Matrix.of x * (P⁻¹ * umat g * P)) v)` using `fun v hv g x hx => by`. Rewrite using `[ha _ (hDs _ (hD' g v hv)) x hx, ← hmul _ hx _ (hconj g)]`.

Establish `hcl` using `closable (ν := νq) hU D a A hD' (fun v hv => by rw [hA' v hv]; exact (hmem v hv).coeFn_toLp) hn' (fun v hv => by`. Establish `hemb` using `(Formalism.REAL.isClosedEmbeddingMatrix (2 * r + k + 1) ε).1`. Use `haveI : SecondCountableTopology (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := inferInstanceAs (SecondCountableTopology (Mt k r))`. Use `haveI : SecondCountableTopology (Formalism.REAL.UJ ε) := hemb.isEmbedding.secondCountableTopology`. Establish `hae2 : ∀ᵐ p ∂((Formalism.REAL.muG ε).prod νq), p ∈ Prod.snd ⁻¹' {x : Mt k r | Matrix.of x ∈ BranchingSupport.GG k r}` using `Measure.quasiMeasurePreserving_snd.ae hae`.

Establish `c2 : Continuous fun p : Formalism.REAL.UJ ε × Mt k r => Matrix.of p.2 * (P⁻¹ * umat p.1 * P)` using `Continuous.matrix_mul (A := fun p : Formalism.REAL.UJ ε × Mt k r => Matrix.of p.2) continuous_snd (c1.comp continuous_fst)`. Establish `hc` using `(hcont v (hDs v hv)).comp (s := Prod.snd ⁻¹' {x : Mt k r | Matrix.of x ∈ BranchingSupport.GG k r}) c2.continuousOn (fun p hp => hGG.2.2.1 _ hp _ (hconj p.1))`. Establish `h2` using `hc.aestronglyMeasurable (μ := (Formalism.REAL.muG ε).prod νq) (measurable_snd hAm)`. Rewrite `h2` using `[Measure.restrict_eq_self_of_ae_mem hae2]`. Conclude with `h2.congr (hae2.mono fun p hp => (hval v hv p.1 p.2 hp).symm))`.

Use the proof step `(hae.mono fun x hx => ⟨fun v hv => by`. Simplify using `only [hval v hv _ x hx]`. Conclude with `(hcont v (hDs v hv)).comp_continuous (continuous_const.matrix_mul c1) fun g => hGG.2.2.1 _ hx _ (hconj g), fun ξ φ hφ => by`. Take `⟨C, Ws, hWs, hC⟩` from `hB.2.2.2`. Establish `hsob : Formalism.L2.Theta.Sobolev₂ (GlobalTheory.SmVec.lieG (Hpk k r)) (GlobalTheory.SmVec.trRep σ' P) ((innerSL ℂ ξ : Wp →ₗ[ℂ] ℂ) ∘ₗ (LinearMap.proj x) ∘ₗ a)`.

Rewrite using `[e]`. Use `⟨Ws.map fun l => l.map fun X => (Matrix.of x)⁻¹ * X * Matrix.of x, ‖ξ‖ * C, ?_, fun v hv => ?_⟩` and prove the remaining obligations. Introduce `l hl X hX`. Take `⟨l', hl', rfl⟩` from `List.mem_map.1 hl`. Take `⟨Y, hY, rfl⟩` from `List.mem_map.1 hX`.

Conclude with `GlobalTheory.SmVec.conj_mem_lieG hGu hx (hWs l' hl' Y hY)`. Establish `hv'` using `(hs v).2 hv show ‖⟪ξ, a v x⟫_ℂ‖ ≤ _`. Rewrite using `[ha v hv' x hx, mul_assoc]`. Use `(norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))` and prove the remaining obligations. Use `(hC _ (hsm v hv' _ hx)).trans (le_of_eq ?_)` and prove the remaining obligations.

Rewrite using `[List.map_map]`. Use `congr 2`. Use `List.map_congr_left fun l hl => ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.BesselMapOne.dsigW_eq]`. Conclude with `(congrArg norm (GlobalTheory.SmVec.WordCont.word_rep hGu hσ hv hx (hWs l hl))).trans (hσ.2.1 _ hx _)`.

Take `⟨q1, q2⟩` from `GlobalTheory.SobGarding.sobCont_gard _ ε R.H σ' P _ hP hG hU _ hsob`. Conclude with `⟨q1 φ hφ, fun v hv => (q2 v (by rw [e]; exact (hs v).1 (hDs v hv))).2 φ hφ⟩⟩)`. Take `⟨c, hc⟩` from `GlobalTheory.ClosableSchur.norm_sq_eq (Formalism.REAL.UJ ε) R.H (Lp Wp 2 νq) (fun g => σ' (umat g)) D (fun g v => hU.2.1 _ g.2 v) (fun g => by`. Establish `hm : ∀ (g : Formalism.REAL.UJ ε) (v : R.H), σ' (umat g) (σ' (umat g⁻¹) v) = v`. Introduce `g v`.

Establish `e : σ' (umat g * umat g⁻¹) = _` using `hU.1.2 _ g.2 _ (g⁻¹).2`. Establish `e1 : umat g * umat g⁻¹ = 1` using `Units.mul_inv g.1`. Establish `e2 : σ' 1 = 1` using `hU.1.1`. Rewrite `e` using `[e1, e2]`. Conclude with `(congrArg (fun T : R.H →L[ℂ] R.H => T v) e).symm`.

Conclude with `⟨g⁻¹, fun v => by simpa only [inv_inv] using hm g⁻¹ v, hm g⟩)`. Use the proof step `(fun S hS h => hI S hS fun g hg v hv => by`. Establish `hu : IsUnit g` using `GlobalTheory.SmVec.isUnit_of_mem_UH (G := Formalism.REAL.Jm ε) (IsUnit.of_mul_eq_one _ (Formalism.REAL.Jm_mul_self ε)) hg`. Conclude with `h ⟨hu.unit, hg⟩ v hv)`. Use the proof step `hD' A hn' hcl`.

Use `⟨max c 0, le_max_right _ _, fun v hv => ?_⟩` and prove the remaining obligations. Establish `h2 : max c 0 * ‖v‖ ^ 2 = ‖A v‖ ^ 2`. Establish `h3` using `hc v hv`. Break down `le_total 0 c with h | h` into its components or cases. Rewrite using `[max_eq_left h, h3]`.

Rewrite using `[max_eq_right h, zero_mul]`. Conclude with `le_antisymm (sq_nonneg _) (h3 ▸ mul_nonpos_of_nonpos_of_nonneg h (sq_nonneg _))`. Rewrite using `[h2, hl2 v (hDs v hv), hAn v hv, ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hmem v hv).2.ne]`.
-/
theorem besselQuotientMass_eq_const_mul_norm_sq_translates : ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Mt k r)) (B : R.H → Wp) (w : R.H), R.IsDS ε mu → SideG k r z π u μW μN μG νq → IsBes R z π B → w ∈ R.sm → PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g w)) ≠ ⊤ → ∃ c : ℝ, 0 ≤ c ∧ ∀ v ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp R.σ w, PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g v)) = ENNReal.ofReal (c * ‖v‖ ^ 2) := by
  intro k r ε mu R Wp _ _ _ _ z π u μW μN μG νq B w hR hS hB hw hfin
  obtain ⟨-, hσ, -⟩ := GlobalTheory.BesselMapOne.rep_of_isDSHpk hR.2
  obtain ⟨P, ⟨⟨hP, hG⟩, -⟩, -, -, hU, hI, -⟩ := hR.2
  set σ' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (R.H →L[ℂ] R.H) := fun g => R.σ (P⁻¹ * g * P)
    with hσ'
  have hd := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have e : GlobalTheory.SmVec.trRep σ' P = R.σ := funext fun g => by
    unfold GlobalTheory.SmVec.trRep
    simp only [hσ']
    congr 1
    simp only [← Matrix.mul_assoc, nonsing_inv_mul _ hd, Matrix.one_mul]
    rw [Matrix.mul_assoc, nonsing_inv_mul _ hd, Matrix.mul_one]
  have hs : ∀ v, v ∈ R.sm ↔ v ∈ GlobalTheory.SmVec.smSub (Hpk k r) R.σ :=
    GlobalTheory.BesselMapOne.smoothOnH_iff_mem (Formalism.QuantumDeterminants.GBasic.Hpk_herm k r) (Formalism.QuantumDeterminants.GBasic.Hpk_sq k r) hσ
  have hGu : IsUnit (Hpk k r) := GlobalTheory.SmVec.gram_unit hP hG
  have hsm := PI.UnitaryGroupMassFormula.CapelliEig.smooth_right_action k r ε mu R.H R.σ hR.2
  obtain ⟨hGG, -⟩ := GlobalTheory.T.isMatGroup_GG_and_haar_right_invariant k r
  have hconj : ∀ g : Formalism.REAL.UJ ε, P⁻¹ * umat g * P ∈ BranchingSupport.GG k r := fun g => GlobalTheory.SmVec.conj_mem_UH hP hG g.2
  have hmul : ∀ g ∈ BranchingSupport.GG k r, ∀ h ∈ BranchingSupport.GG k r, ∀ v, R.σ g (R.σ h v) = R.σ (g * h) v := fun g hg h hh v =>
    (GlobalTheory.SmVec.rep_mul hσ hg hh v).symm
  have hS' := hS
  obtain ⟨hz, hT, ⟨u₀, hπ⟩, -, hW, hN, hHG, hq⟩ := hS'
  obtain ⟨h0, h1⟩ := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hW hN
  have hae : ∀ᵐ x ∂νq, Matrix.of x ∈ BranchingSupport.GG k r := Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hHG.2.2.1 h0 h1 hq
  haveI := hHG.1
  haveI := (GlobalTheory.T.besselSubgroup_product_measure_isHaar k r z μW μN hz hT hW hN).2.2.1.1
  haveI : SigmaFinite νq := sigmaFinite_of_quot h0 hq
  haveI : SecondCountableTopology Wp := by
    haveI : ProperSpace Wp := FiniteDimensional.proper ℂ Wp
    infer_instance
  have hπu := (GlobalTheory.ThA.hcType_rep k r z u₀ Wp π hz hT hπ).2.2.2.1
  let L : R.smSub →ₗ[ℂ] Wp :=
    { toFun := fun x => B x
      map_add' := fun x y => hB.1 _ x.2 _ y.2
      map_smul' := fun c x => hB.2.1 c _ x.2 }
  obtain ⟨Bl, hBl⟩ := L.exists_extend
  have hBl' : ∀ v ∈ R.sm, Bl v = B v := fun v hv => LinearMap.congr_fun hBl ⟨v, hv⟩
  let a : R.H →ₗ[ℂ] (Mt k r → Wp) := LinearMap.pi fun x => Bl ∘ₗ (R.σ (Matrix.of x) : R.H →ₗ[ℂ] R.H)
  have ha : ∀ v ∈ R.sm, ∀ x : Mt k r, Matrix.of x ∈ BranchingSupport.GG k r → a v x = B (R.σ (Matrix.of x) v) :=
    fun v hv x hx => hBl' _ (hsm v hv _ hx)
  have hcont : ∀ v ∈ R.sm, ContinuousOn (fun g => B (R.σ g v)) (BranchingSupport.GG k r) := fun v hv =>
    continuousOn_orbit hR hB.1 hB.2.1 hB.2.2.2 hv
  have hl2 : ∀ v ∈ R.sm, PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g v)) = eLpNorm (a v) 2 νq ^ 2 := fun v hv => by
    rw [quotientMass_eq_eLpNorm_sq, eLpNorm_congr_ae (hae.mono fun x hx => ha v hv x hx)]
  have hinv : ∀ v ∈ R.sm, ∀ g ∈ BranchingSupport.GG k r, eLpNorm (a (R.σ g v)) 2 νq = eLpNorm (a v) 2 νq := fun v hv g hg => by
    have h2 := quotientMass_right_translation_invariant hS (hcont v hv) (by
      rintro _ ⟨h, hh, m, hm, rfl⟩ x hx
      rw [← hmul _ (hGG.2.2.1 _ hh.1 _ hm.1) _ hx, hB.2.2.1 h hh m hm _ (hsm v hv x hx), norm_smul, hπu h hh]
      simp [Formalism.QuantumDeterminants.psi, Complex.norm_exp]) hg
    have h3 : PI.BesselPeriodGGP.l2SG νq (fun x => B (R.σ x (R.σ g v))) =
        PI.BesselPeriodGGP.l2SG νq (fun x => B (R.σ (x * g) v)) :=
      lintegral_congr_ae (hae.mono fun x hx => by simp only [hmul _ hx _ hg])
    rw [← h3, hl2 _ (hsm v hv g hg), hl2 v hv] at h2
    exact (ENNReal.pow_right_strictMono two_ne_zero).injective h2
  have hAm : MeasurableSet {x : Mt k r | Matrix.of x ∈ BranchingSupport.GG k r} := IsClosed.measurableSet (α := Mt k r) hGG.1
  have hmeas : ∀ v ∈ R.sm, AEStronglyMeasurable (a v) νq := fun v hv => by
    have hc : ContinuousOn (fun x : Mt k r => B (R.σ (Matrix.of x) v)) {x : Mt k r | Matrix.of x ∈ BranchingSupport.GG k r} :=
      hcont v hv
    have h2 := hc.aestronglyMeasurable (μ := νq) hAm
    rw [Measure.restrict_eq_self_of_ae_mem (s := {x : Mt k r | Matrix.of x ∈ BranchingSupport.GG k r}) hae] at h2
    exact h2.congr (hae.mono fun x hx => (ha v hv x hx).symm)
  set D := Formalism.FourierDecayAlt.ThreeDimData.DDsp (k := k) (r := r) R.σ w with hDdef
  have hDs : ∀ v ∈ D, v ∈ R.sm := fun v hv =>
    (Submodule.span_le (p := R.smSub)).2 (by rintro _ ⟨g, hg, rfl⟩; exact hsm w hw g hg) hv
  have hDst : ∀ g ∈ BranchingSupport.GG k r, ∀ v ∈ D, R.σ g v ∈ D := fun g hg v hv =>
    (Submodule.span_le (p := D.comap (R.σ g : R.H →ₗ[ℂ] R.H))).2 (by
      rintro _ ⟨h, hh, rfl⟩
      exact Submodule.subset_span ⟨g * h, hGG.2.2.1 _ hg _ hh, (hmul g hg h hh w).symm⟩) hv
  have hmem : ∀ v ∈ D, MemLp (a v) 2 νq := fun v hv => by
    induction hv using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨g, hg, rfl⟩ := hy
      refine ⟨hmeas _ (hsm w hw g hg), ?_⟩
      rw [hinv w hw g hg]
      rw [hl2 w hw] at hfin
      exact lt_top_iff_ne_top.2 fun h => hfin (by rw [h]; simp)
    | zero => rw [map_zero]; exact MemLp.zero
    | add x y _ _ hx hy => rw [map_add]; exact hx.add hy
    | smul c x _ hx => rw [map_smul]; exact hx.const_smul c
  let A₀ : D →ₗ[ℂ] Lp Wp 2 νq :=
    { toFun := fun v => (hmem v v.2).toLp _
      map_add' := fun v w => by
        rw [← MemLp.toLp_add]
        congr 1
        simp
      map_smul' := fun c w => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        congr 1
        simp }
  obtain ⟨A, hA⟩ := A₀.exists_extend
  have hA' : ∀ v (hv : v ∈ D), A v = (hmem v hv).toLp _ := fun v hv => LinearMap.congr_fun hA ⟨v, hv⟩
  have hAn : ∀ v ∈ D, ‖A v‖ = (eLpNorm (a v) 2 νq).toReal := fun v hv => by rw [hA' v hv, Lp.norm_toLp]
  have hD' : ∀ g : Formalism.REAL.UJ ε, ∀ v ∈ D, σ' (umat g) v ∈ D := fun g => hDst _ (hconj g)
  have hn' : ∀ g : Formalism.REAL.UJ ε, ∀ v ∈ D, ‖A (σ' (umat g) v)‖ = ‖A v‖ := fun g v hv => by
    rw [hAn _ (hD' g v hv), hAn v hv]
    exact congrArg _ (hinv v (hDs v hv) _ (hconj g))
  have c1 : Continuous fun g : Formalism.REAL.UJ ε => P⁻¹ * umat g * P :=
    (continuous_const.matrix_mul GlobalTheory.SmVec.continuous_umat).matrix_mul continuous_const
  have hval : ∀ v ∈ D, ∀ (g : Formalism.REAL.UJ ε) (x : Mt k r), Matrix.of x ∈ BranchingSupport.GG k r →
      a (σ' (umat g) v) x = B (R.σ (Matrix.of x * (P⁻¹ * umat g * P)) v) := fun v hv g x hx => by
    rw [ha _ (hDs _ (hD' g v hv)) x hx, ← hmul _ hx _ (hconj g)]
  have hcl := closable (ν := νq) hU D a A hD' (fun v hv => by rw [hA' v hv]; exact (hmem v hv).coeFn_toLp) hn'
    (fun v hv => by
      have hemb := (Formalism.REAL.isClosedEmbeddingMatrix (2 * r + k + 1) ε).1
      haveI : SecondCountableTopology (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
        inferInstanceAs (SecondCountableTopology (Mt k r))
      haveI : SecondCountableTopology (Formalism.REAL.UJ ε) := hemb.isEmbedding.secondCountableTopology
      have hae2 : ∀ᵐ p ∂((Formalism.REAL.muG ε).prod νq), p ∈ Prod.snd ⁻¹' {x : Mt k r | Matrix.of x ∈ BranchingSupport.GG k r} :=
        Measure.quasiMeasurePreserving_snd.ae hae
      have c2 : Continuous fun p : Formalism.REAL.UJ ε × Mt k r => Matrix.of p.2 * (P⁻¹ * umat p.1 * P) :=
        Continuous.matrix_mul (A := fun p : Formalism.REAL.UJ ε × Mt k r => Matrix.of p.2) continuous_snd
          (c1.comp continuous_fst)
      have hc := (hcont v (hDs v hv)).comp (s := Prod.snd ⁻¹' {x : Mt k r | Matrix.of x ∈ BranchingSupport.GG k r})
        c2.continuousOn (fun p hp => hGG.2.2.1 _ hp _ (hconj p.1))
      have h2 := hc.aestronglyMeasurable (μ := (Formalism.REAL.muG ε).prod νq) (measurable_snd hAm)
      rw [Measure.restrict_eq_self_of_ae_mem hae2] at h2
      exact h2.congr (hae2.mono fun p hp => (hval v hv p.1 p.2 hp).symm))
    (hae.mono fun x hx => ⟨fun v hv => by
        simp only [hval v hv _ x hx]
        exact (hcont v (hDs v hv)).comp_continuous (continuous_const.matrix_mul c1)
          fun g => hGG.2.2.1 _ hx _ (hconj g), fun ξ φ hφ => by
      obtain ⟨C, Ws, hWs, hC⟩ := hB.2.2.2
      have hsob : Formalism.L2.Theta.Sobolev₂ (GlobalTheory.SmVec.lieG (Hpk k r)) (GlobalTheory.SmVec.trRep σ' P)
          ((innerSL ℂ ξ : Wp →ₗ[ℂ] ℂ) ∘ₗ (LinearMap.proj x) ∘ₗ a) := by
        rw [e]
        refine ⟨Ws.map fun l => l.map fun X => (Matrix.of x)⁻¹ * X * Matrix.of x, ‖ξ‖ * C, ?_, fun v hv => ?_⟩
        · intro l hl X hX
          obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
          obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
          exact GlobalTheory.SmVec.conj_mem_lieG hGu hx (hWs l' hl' Y hY)
        · have hv' := (hs v).2 hv
          show ‖⟪ξ, a v x⟫_ℂ‖ ≤ _
          rw [ha v hv' x hx, mul_assoc]
          refine (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
          refine (hC _ (hsm v hv' _ hx)).trans (le_of_eq ?_)
          rw [List.map_map]
          congr 2
          refine List.map_congr_left fun l hl => ?_
          rw [GlobalTheory.BesselMapOne.dsigW_eq]
          exact (congrArg norm (GlobalTheory.SmVec.WordCont.word_rep hGu hσ hv hx (hWs l hl))).trans (hσ.2.1 _ hx _)
      obtain ⟨q1, q2⟩ := GlobalTheory.SobGarding.sobCont_gard _ ε R.H σ' P _ hP hG hU _ hsob
      exact ⟨q1 φ hφ, fun v hv => (q2 v (by rw [e]; exact (hs v).1 (hDs v hv))).2 φ hφ⟩⟩)
  obtain ⟨c, hc⟩ := GlobalTheory.ClosableSchur.norm_sq_eq (Formalism.REAL.UJ ε) R.H (Lp Wp 2 νq) (fun g => σ' (umat g)) D
    (fun g v => hU.2.1 _ g.2 v)
    (fun g => by
      have hm : ∀ (g : Formalism.REAL.UJ ε) (v : R.H), σ' (umat g) (σ' (umat g⁻¹) v) = v := by
        intro g v
        have e : σ' (umat g * umat g⁻¹) = _ := hU.1.2 _ g.2 _ (g⁻¹).2
        have e1 : umat g * umat g⁻¹ = 1 := Units.mul_inv g.1
        have e2 : σ' 1 = 1 := hU.1.1
        rw [e1, e2] at e
        exact (congrArg (fun T : R.H →L[ℂ] R.H => T v) e).symm
      exact ⟨g⁻¹, fun v => by simpa only [inv_inv] using hm g⁻¹ v, hm g⟩)
    (fun S hS h => hI S hS fun g hg v hv => by
      have hu : IsUnit g := GlobalTheory.SmVec.isUnit_of_mem_UH (G := Formalism.REAL.Jm ε)
        (IsUnit.of_mul_eq_one _ (Formalism.REAL.Jm_mul_self ε)) hg
      exact h ⟨hu.unit, hg⟩ v hv)
    hD' A hn' hcl
  refine ⟨max c 0, le_max_right _ _, fun v hv => ?_⟩
  have h2 : max c 0 * ‖v‖ ^ 2 = ‖A v‖ ^ 2 := by
    have h3 := hc v hv
    rcases le_total 0 c with h | h
    · rw [max_eq_left h, h3]
    · rw [max_eq_right h, zero_mul]
      exact le_antisymm (sq_nonneg _) (h3 ▸ mul_nonpos_of_nonpos_of_nonneg h (sq_nonneg _))
  rw [h2, hl2 v (hDs v hv), hAn v hv, ENNReal.ofReal_pow ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (hmem v hv).2.ne]

end GlobalTheory.BesselIsometry

end
