import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesUnitarySmoothBasic
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HaarEqSmul
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeilFormulaIntegrableComplexStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselGrowthStabilizerUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselCharacterUnipotentRadicalPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSubgroupParameterMeasurePreservingStatement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ReproducingFormulaReduction
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumNonneg
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GrowthUnitaryGroupRpowNegIntegrableStatement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.ZhatNormLinearBound

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselNorm.BesselConvolution

open Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity

section

variable {k r : ℕ} {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]

/- English proof (translation)
Use `hW.1` as an intermediate fact. Use `hN.1` as an intermediate fact. Establish `hWae : ∀ᵐ p1 ∂μW, Matrix.of p1 ∈ Formalism.QuantumDeterminants.UWset k r z` using `ae_iff.mpr hW.2.2.1`. Establish `hNae : ∀ᵐ p2 ∂μN, Matrix.of p2 ∈ Formalism.QuantumDeterminants.Nset k r` using `ae_iff.mpr hN.2.2.1`. Conclude with `(Measure.quasiMeasurePreserving_fst.ae hWae).and (Measure.quasiMeasurePreserving_snd.ae hNae)`.
-/
private theorem ae_mem_prod {z : Fin (2 * r + k + 1) → ℂ} {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) :
    ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r := by
  have := hW.1; have := hN.1
  have hWae : ∀ᵐ p1 ∂μW, Matrix.of p1 ∈ Formalism.QuantumDeterminants.UWset k r z := ae_iff.mpr hW.2.2.1
  have hNae : ∀ᵐ p2 ∂μN, Matrix.of p2 ∈ Formalism.QuantumDeterminants.Nset k r := ae_iff.mpr hN.2.2.1
  exact (Measure.quasiMeasurePreserving_fst.ae hWae).and (Measure.quasiMeasurePreserving_snd.ae hNae)

/- English proof (translation)
Rewrite using `[continuousOn_clm_apply]`. Introduce `ξ`. Establish `hm : Continuous (fun p1 : Formalism.QuantumDeterminants.Mt k r => Formalism.QuantumDeterminants.Hpk k r * (Matrix.of p1 : Mx k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r)` using `(continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const`. Establish `hmaps : Set.MapsTo (fun p1 : Formalism.QuantumDeterminants.Mt k r => Formalism.QuantumDeterminants.Hpk k r * (Matrix.of p1 : Mx k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r) {p1 : Formalism.QuantumDeterminants.Mt k r | Matrix.of p1 ∈ Formalism.QuantumDeterminants.UWset k r z} (F …`. Introduce `p1 hp1`.

Establish `e : (Matrix.of p1 : Mx k r)⁻¹ = Formalism.QuantumDeterminants.Hpk k r * (Matrix.of p1 : Mx k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r` using `PI.HwUniqW.inv_eq_UH hp1.1`. Use `show Formalism.QuantumDeterminants.Hpk k r * (Matrix.of p1 : Mx k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r ∈ Formalism.QuantumDeterminants.UWset k r z`. Rewrite using `[← e]`. Conclude with `(uw_inv hp1).1`. Use `((piW_cont hT hπ ξ).comp hm.continuousOn hmaps).congr ?_` and prove the remaining obligations.

Introduce `p1 hp1`. Establish `e : (Matrix.of p1 : Mx k r)⁻¹ = Formalism.QuantumDeterminants.Hpk k r * (Matrix.of p1 : Mx k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r` using `PI.HwUniqW.inv_eq_UH hp1.1`. Simplify using `only [Function.comp]`. Rewrite using `[e]`.
-/
private theorem pi_inv_contOn [FiniteDimensional ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ}
    {π : Mx k r → (Wp →L[ℂ] Wp)} (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π) :
    ContinuousOn (fun p1 : Formalism.QuantumDeterminants.Mt k r => π (Matrix.of p1)⁻¹)
      {p1 : Formalism.QuantumDeterminants.Mt k r | Matrix.of p1 ∈ Formalism.QuantumDeterminants.UWset k r z} := by
  rw [continuousOn_clm_apply]
  intro ξ
  have hm : Continuous (fun p1 : Formalism.QuantumDeterminants.Mt k r =>
      Formalism.QuantumDeterminants.Hpk k r * (Matrix.of p1 : Mx k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r) :=
    (continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const
  have hmaps : Set.MapsTo (fun p1 : Formalism.QuantumDeterminants.Mt k r =>
      Formalism.QuantumDeterminants.Hpk k r * (Matrix.of p1 : Mx k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r)
      {p1 : Formalism.QuantumDeterminants.Mt k r | Matrix.of p1 ∈ Formalism.QuantumDeterminants.UWset k r z} (Formalism.QuantumDeterminants.UWset k r z) := by
    intro p1 hp1
    have e : (Matrix.of p1 : Mx k r)⁻¹ = Formalism.QuantumDeterminants.Hpk k r * (Matrix.of p1 : Mx k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r :=
      PI.HwUniqW.inv_eq_UH hp1.1
    show Formalism.QuantumDeterminants.Hpk k r * (Matrix.of p1 : Mx k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r ∈ Formalism.QuantumDeterminants.UWset k r z
    rw [← e]; exact (uw_inv hp1).1
  refine ((piW_cont hT hπ ξ).comp hm.continuousOn hmaps).congr ?_
  intro p1 hp1
  have e : (Matrix.of p1 : Mx k r)⁻¹ = Formalism.QuantumDeterminants.Hpk k r * (Matrix.of p1 : Mx k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r :=
    PI.HwUniqW.inv_eq_UH hp1.1
  simp only [Function.comp]
  rw [e]

/- English proof (translation)
Use `hW.1` as an intermediate fact. Use `hN.1` as an intermediate fact. Establish `hWae : ∀ᵐ p1 ∂μW, Matrix.of p1 ∈ Formalism.QuantumDeterminants.UWset k r z` using `ae_iff.mpr hW.2.2.1`. Establish `hof : Continuous (fun y : Formalism.QuantumDeterminants.Mt k r => (Matrix.of y : Mx k r))` using `continuous_id`. Establish `h1 : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of q.1 : Mx k r))` using `continuous_fst`.

Establish `h2 : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of q.2 : Mx k r))` using `continuous_snd`. Establish `hφ : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of q.1 : Mx k r) * Matrix.of q.2)` using `h1.matrix_mul h2`. Establish `hTm : MeasurableSet ((fun q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of q.1 : Mx k r) * Matrix.of q.2) ⁻¹' Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))` using `(isClosed_UH.preimage hφ).measurableSet`. Establish `hTae : ∀ᵐ q ∂(μW.prod μN), q ∈ ((fun q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of q.1 : Mx k r) * Matrix.of q.2) ⁻¹' Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))` using `by filter_upwards [ae_mem_prod hW hN] with q hq`. Conclude with `Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hq.1.1 hq.2.1`.

Establish `hcs` using `Formalism.FourierDecayAlt.P.S3dx4.sigma_contOn hσ w`. Establish `hc2 : AEStronglyMeasurable (fun q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => ⟪v, σ (Matrix.of q.1 * Matrix.of q.2) w⟫_ℂ) (μW.prod μN)` using `aesm_of_contOn (α := Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) (μ := μW.prod μN) (continuousOn_const.inner (hcs.comp hφ.continuousOn (fun q hq => hq))) hTm hTae`. Establish `hc3 : AEStronglyMeasurable (fun q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => star (Formalism.QuantumDeterminants.psi k r z c (Matrix.of q.2))) (μW.prod μN)` using `(continuous_star.comp ((psi_cont z c).comp h2)).aestronglyMeasurable`. Establish `hV : AEStronglyMeasurable (fun p1 : Formalism.QuantumDeterminants.Mt k r => π (Matrix.of p1)⁻¹) μW`. Use `(pi_inv_contOn hT hπ).aestronglyMeasurable (μ := μW) ((isClosed_UW z).preimage hof).measurableSet` as an intermediate fact.

Rewrite `this` using `[Measure.restrict_eq_self_of_ae_mem (s := {p1 : Formalism.QuantumDeterminants.Mt k r | Matrix.of p1 ∈ Formalism.QuantumDeterminants.UWset k r z}) hWae]`. Then use the resulting hypothesis. Establish `hV1 : AEStronglyMeasurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => π (Matrix.of p.1)⁻¹) (μW.prod μN)` using `AEStronglyMeasurable.comp_fst (μ := μW) (ν := μN) hV`. Conclude with `(hc2.mul hc3).smul hV1`.
-/
private theorem beInt_aesm [FiniteDimensional ℂ Wp] {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {σ : Mx k r → (H →L[ℂ] H)} (hσ : PI.UpqRep.IsDSHpk k r ε lam σ)
    {z : Fin (2 * r + k + 1) → ℂ} (c : ℂ) {u : Fin k → ℝ}
    {π : Mx k r → (Wp →L[ℂ] Wp)} (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π)
    {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) (w v : H) :
    AEStronglyMeasurable (beInt z c π σ w v) (μW.prod μN) := by
  have := hW.1; have := hN.1
  have hWae : ∀ᵐ p1 ∂μW, Matrix.of p1 ∈ Formalism.QuantumDeterminants.UWset k r z := ae_iff.mpr hW.2.2.1
  have hof : Continuous (fun y : Formalism.QuantumDeterminants.Mt k r => (Matrix.of y : Mx k r)) := continuous_id
  have h1 : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of q.1 : Mx k r)) := continuous_fst
  have h2 : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of q.2 : Mx k r)) := continuous_snd
  have hφ : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (Matrix.of q.1 : Mx k r) * Matrix.of q.2) := h1.matrix_mul h2
  have hTm : MeasurableSet ((fun q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (Matrix.of q.1 : Mx k r) * Matrix.of q.2) ⁻¹' Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :=
    (isClosed_UH.preimage hφ).measurableSet
  have hTae : ∀ᵐ q ∂(μW.prod μN), q ∈ ((fun q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (Matrix.of q.1 : Mx k r) * Matrix.of q.2) ⁻¹' Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) := by
    filter_upwards [ae_mem_prod hW hN] with q hq
    exact Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hq.1.1 hq.2.1
  have hcs := Formalism.FourierDecayAlt.P.S3dx4.sigma_contOn hσ w
  have hc2 : AEStronglyMeasurable (fun q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      ⟪v, σ (Matrix.of q.1 * Matrix.of q.2) w⟫_ℂ) (μW.prod μN) :=
    aesm_of_contOn (α := Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) (μ := μW.prod μN)
      (continuousOn_const.inner (hcs.comp hφ.continuousOn (fun q hq => hq))) hTm hTae
  have hc3 : AEStronglyMeasurable (fun q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      star (Formalism.QuantumDeterminants.psi k r z c (Matrix.of q.2))) (μW.prod μN) :=
    (continuous_star.comp ((psi_cont z c).comp h2)).aestronglyMeasurable
  have hV : AEStronglyMeasurable (fun p1 : Formalism.QuantumDeterminants.Mt k r => π (Matrix.of p1)⁻¹) μW := by
    have := (pi_inv_contOn hT hπ).aestronglyMeasurable (μ := μW) ((isClosed_UW z).preimage hof).measurableSet
    rwa [Measure.restrict_eq_self_of_ae_mem
      (s := {p1 : Formalism.QuantumDeterminants.Mt k r | Matrix.of p1 ∈ Formalism.QuantumDeterminants.UWset k r z}) hWae] at this
  have hV1 : AEStronglyMeasurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => π (Matrix.of p.1)⁻¹)
      (μW.prod μN) := AEStronglyMeasurable.comp_fst (μ := μW) (ν := μN) hV
  exact (hc2.mul hc3).smul hV1

/- English proof (translation)
Establish `h1 : ‖π (Matrix.of p.1)⁻¹‖ ≤ 1` using `ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun ξ => by`. Rewrite using `[piW_unitary hT hπ _ (uw_inv hp).1 ξ, one_mul]`. Unfold `beInt`. Rewrite using `[norm_smul, norm_mul, norm_star, psi_norm, mul_one]`. Conclude with `mul_le_of_le_one_right (norm_nonneg _) h1`.
-/
private theorem norm_beInt_le (σ : Mx k r → (H →L[ℂ] H)) {z : Fin (2 * r + k + 1) → ℂ} (c : ℂ) {u : Fin k → ℝ}
    {π : Mx k r → (Wp →L[ℂ] Wp)} (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π)
    (w v : H) (p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) (hp : Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z) :
    ‖beInt z c π σ w v p‖ ≤ ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ‖ := by
  have h1 : ‖π (Matrix.of p.1)⁻¹‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun ξ => by
      rw [piW_unitary hT hπ _ (uw_inv hp).1 ξ, one_mul]
  unfold beInt
  rw [norm_smul, norm_mul, norm_star, psi_norm, mul_one]
  exact mul_le_of_le_one_right (norm_nonneg _) h1

end

/- English proof (translation)
Introduce `Hy k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq hR hgap hok hS v hv`. Take `⟨hz, hT, ⟨u₀, hπ⟩, -, hW, hN, hGh, hq⟩` from `hS`. Take `⟨C, Ws, hWs, hb⟩` from `GlobalTheory.BesselDecay.decay_TK Hy k r ε mu h R hR hgap hok v hv`. Establish `hA : AG k r < aOf r h - 1`. Establish `h4` using `hok.2.2.2`.

Establish `: 0 ≤ AG k r` using `by unfold AG; positivity`. Establish `: 0 ≤ 9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hI` using `hG k r z μW μN μG νq _ hz hT hW hN hGh hq hA`. Rewrite `hI` using `[neg_sub]`.

Establish `hbd : ∀ w ∈ R.sm, ∀ᵐ p ∂(μW.prod μN), ‖beInt z Formalism.QuantumDeterminants.cStd π R.σ w v p‖ ≤ C * (Ws.map fun W => ‖PI.UpqRep.dsigW (k` using `k) (r := r) R.σ W w‖).sum * B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (1 - aOf r h) := by`. Introduce `w hw`. Use `filter_upwards [ae_mem_prod hW hN] with p hp`. Conclude with `(norm_beInt_le R.σ _ hT hπ w v p hp.1).trans (hb w hw _ (Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hp.1.1 hp.2.1))`. Use `⟨fun w hw => ?_, C * ∫ p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r, B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (1 - aOf r h) ∂(μW.prod μN), Ws, hWs, fun w hw => ?_⟩` and prove the remaining obligations.

Conclude with `Integrable.mono' (hI.const_mul _) (beInt_aesm hR.2 _ hT hπ hW hN w v) (hbd w hw)`. Use `(norm_integral_le_of_norm_le (hI.const_mul _) (hbd w hw)).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[integral_const_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem be_conv_of_growth (hG : GrowthS) : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∀ v ∈ R.TK, (∀ w ∈ R.sm, Integrable (beInt z Formalism.QuantumDeterminants.cStd π R.σ w v) (μW.prod μN)) ∧ PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ (fun w => be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v) := by
  intro Hy k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq hR hgap hok hS v hv
  obtain ⟨hz, hT, ⟨u₀, hπ⟩, -, hW, hN, hGh, hq⟩ := hS
  obtain ⟨C, Ws, hWs, hb⟩ := GlobalTheory.BesselDecay.decay_TK Hy k r ε mu h R hR hgap hok v hv
  have hA : AG k r < aOf r h - 1 := by
    have h4 := hok.2.2.2
    have : 0 ≤ AG k r := by unfold AG; positivity
    have : 0 ≤ 9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by positivity
    linarith
  have hI := hG k r z μW μN μG νq _ hz hT hW hN hGh hq hA
  rw [neg_sub] at hI
  have hbd : ∀ w ∈ R.sm, ∀ᵐ p ∂(μW.prod μN), ‖beInt z Formalism.QuantumDeterminants.cStd π R.σ w v p‖ ≤
      C * (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W w‖).sum *
        B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (1 - aOf r h) := by
    intro w hw
    filter_upwards [ae_mem_prod hW hN] with p hp
    exact (norm_beInt_le R.σ _ hT hπ w v p hp.1).trans
      (hb w hw _ (Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hp.1.1 hp.2.1))
  refine ⟨fun w hw => ?_, C * ∫ p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r,
    B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (1 - aOf r h) ∂(μW.prod μN), Ws, hWs, fun w hw => ?_⟩
  · exact Integrable.mono' (hI.const_mul _) (beInt_aesm hR.2 _ hT hπ hW hN w v) (hbd w hw)
  · refine (norm_integral_le_of_norm_le (hI.const_mul _) (hbd w hw)).trans (le_of_eq ?_)
    rw [integral_const_mul]; ring

/- English proof (translation)
The claim follows from `be_conv_of_growth GlobalTheory.T.besselGrowth_stabilizer_unipotent`.
-/
private theorem be_conv : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∀ v ∈ R.TK, (∀ w ∈ R.sm, Integrable (beInt z Formalism.QuantumDeterminants.cStd π R.σ w v) (μW.prod μN)) ∧ PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ (fun w => be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v) :=
  be_conv_of_growth GlobalTheory.T.besselGrowth_stabilizer_unipotent

end GlobalTheory.BesselNorm.BesselConvolution

namespace GlobalTheory.BesselNorm.InnerIntegralSquares

/- English proof (translation)
Establish `h1 : AEStronglyMeasurable F (μ.map f)` using `by rw [hf.map_eq]; exact hF.1`. Rewrite using `[← integral_map hf.measurable.aemeasurable h1, hf.map_eq]`.
-/
private theorem integral_comp_mp {X : Type} [MeasurableSpace X] {μ : Measure X} {f : X → X}
    (hf : MeasurePreserving f μ μ) {F : X → ℂ} (hF : Integrable F μ) :
    ∫ x, F x ∂μ = ∫ x, F (f x) ∂μ := by
  have h1 : AEStronglyMeasurable F (μ.map f) := by rw [hf.map_eq]; exact hF.1
  rw [← integral_map hf.measurable.aemeasurable h1, hf.map_eq]

/- English proof (translation)
Establish `h1 : Integrable (fun x => F x ξ) μ` using `hF.apply_continuousLinearMap ξ`. Establish `h2 : ⟪η, (∫ x, F x ∂μ) ξ⟫_ℂ = ∫ x, ⟪η, F x ξ⟫_ℂ ∂μ`. Rewrite using `[ContinuousLinearMap.integral_apply hF, integral_inner h1]`. Use `⟨h2, ?_, h1.inner_const η⟩` and prove the remaining obligations. Rewrite using `[← inner_conj_symm, h2, ← integral_conj]`.

Simplify using `only [inner_conj_symm]`.
-/
private theorem inner_integral_apply {X Wp : Type} [MeasurableSpace X] {μ : Measure X}
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    {F : X → (Wp →L[ℂ] Wp)} (hF : Integrable F μ) (ξ η : Wp) :
    ⟪η, (∫ x, F x ∂μ) ξ⟫_ℂ = ∫ x, ⟪η, F x ξ⟫_ℂ ∂μ ∧
    ⟪(∫ x, F x ∂μ) ξ, η⟫_ℂ = ∫ x, ⟪F x ξ, η⟫_ℂ ∂μ ∧ Integrable (fun x => ⟪F x ξ, η⟫_ℂ) μ := by
  have h1 : Integrable (fun x => F x ξ) μ := hF.apply_continuousLinearMap ξ
  have h2 : ⟪η, (∫ x, F x ∂μ) ξ⟫_ℂ = ∫ x, ⟪η, F x ξ⟫_ℂ ∂μ := by
    rw [ContinuousLinearMap.integral_apply hF, integral_inner h1]
  refine ⟨h2, ?_, h1.inner_const η⟩
  rw [← inner_conj_symm, h2, ← integral_conj]
  simp only [inner_conj_symm]

end GlobalTheory.BesselNorm.InnerIntegralSquares

open GlobalTheory.BesselNorm.InnerIntegralSquares in
set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `hH k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq hDS hgap hok hS v hv w hw ξ`. Establish `hint` using `(GlobalTheory.BesselNorm.BesselConvolution.be_conv hH k r ε mu h R Wp z π u μW μN μG νq hDS hgap hok hS v hv).1 w hw`. Take `⟨hz, hT, ⟨u₀, hπ⟩, -, hW, hN, -, -⟩` from `hS`. Take `⟨hψ1, hψm, -, hψc, hUW, -⟩` from `GlobalTheory.T.besselCharacter_unipotentRadical_properties k r z Formalism.QuantumDeterminants.cStd hz`. Take `⟨hmp, -, -, -, -, hae⟩` from `GlobalTheory.T.besselSubgroup_parameter_measurePreserving k r z μW μN hok.1 hz hT hW hN`.

Take `⟨-, hmul, hunit, -⟩` from `Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_facts hT hπ`. Establish `e0 : ((‖be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v ξ‖ ^ 2 : ℝ) : ℂ) = ⟪be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v ξ, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v ξ⟫_ℂ`. Rewrite using `[inner_self_eq_norm_sq_to_K]`. Simplify using the standard rewrite rules. Rewrite using `[e0]`.

Use `((inner_integral_apply hint ξ _).1).trans (integral_congr_ae ?_)` and prove the remaining obligations. Use `filter_upwards [hae] with p hp`. Take `⟨-, h2, h3⟩` from `inner_integral_apply hint ξ (beInt z Formalism.QuantumDeterminants.cStd π R.σ w v p ξ)`. Use `h2.trans ((integral_comp_mp (hmp _ hp.1 _ hp.2).1 h3).trans (integral_congr_ae ?_))` and prove the remaining obligations. Use `filter_upwards [hae] with q hq`.

Take `⟨⟨p1, p2⟩, hp1, hp2⟩ : ∃ p' : Mx k r × Mx k r, p'.1 = Matrix.of p.1 ∧ p'.2 = Matrix.of p.2` from `⟨(_, _), rfl, rfl⟩`. Take `⟨⟨q1, q2⟩, hq1, hq2⟩ : ∃ p' : Mx k r × Mx k r, p'.1 = Matrix.of q.1 ∧ p'.2 = Matrix.of q.2` from `⟨(_, _), rfl, rfl⟩`. Simplify using `only at hp1 hp2 hq1 hq2`. Establish `key : ∀ A : Mx k r, Matrix.of (fun i j => A i j) = A` using `fun A => rfl`. Unfold `beInt`.

Simplify using `only [key]`. Rewrite `hp` using `[← hp1, ← hp2]`. Rewrite `hq` using `[← hq1, ← hq2]`. Rewrite using `[← hp1, ← hp2, ← hq1, ← hq2]`. Take `⟨hpi, hpp, hpp'⟩` from `Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uw_inv hp.1`.

Take `⟨hqi, -, -⟩` from `Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uw_inv hq.1`. Establish `e1 : q1 * p1 * (p1⁻¹ * q2 * p1 * p2) = q1 * q2 * (p1 * p2)`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by rw [hpp, Matrix.mul_one]`.

Establish `e2 : Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (p1⁻¹ * q2 * p1 * p2) = Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd q2 * Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd p2`. Take `⟨-, a2, -, a4⟩` from `hψc p1 hp.1 q2 hq.2`. Rewrite using `[(hψm _ a2 _ hp.2).2, a4]`. Establish `e3 : π (q1 * p1)⁻¹ = (π p1⁻¹).comp (π q1⁻¹)`. Rewrite using `[Matrix.mul_inv_rev, hmul _ hpi _ hqi]`.

Establish `hiso : ∀ a b, ⟪π p1⁻¹ a, π p1⁻¹ b⟫_ℂ = ⟪a, b⟫_ℂ` using `(LinearMap.norm_map_iff_inner_map_map ((π p1⁻¹ : Wp →L[ℂ] Wp) : Wp →ₗ[ℂ] Wp)).1 (hunit _ hpi)`. Establish `e4 : Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd p2 * star (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd p2) = 1`. Rewrite using `[Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hψ1]`. Simplify using the standard rewrite rules. Rewrite using `[e1, e2, e3]`.

Simplify using `only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, inner_smul_left, inner_smul_right, hiso, map_mul, starRingEnd_apply, star_mul', star_star]`. Take the linear combination `(⟪v, R.σ (p1 * p2) w⟫_ℂ * star ⟪v, R.σ (q1 * q2 * (p1 * p2)) w⟫_ℂ * (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd q2 * ⟪π q1⁻¹ ξ, ξ⟫_ℂ)) * e4`.
-/
private theorem GlobalTheory.BesselNorm.InnerIntegralSquares.double_integral : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∀ v ∈ R.TK, ∀ w ∈ R.sm, ∀ ξ : Wp, ((‖be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v ξ‖ ^ 2 : ℝ) : ℂ) = ∫ p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r, (∫ q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r, ⟪v, R.σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ * star ⟪v, R.σ (Matrix.of q.1 * Matrix.of q.2 * (Matrix.of p.1 * Matrix.of p.2)) w⟫_ℂ * (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (Matrix.of q.2) * ⟪π (Matrix.of q.1)⁻¹ ξ, ξ⟫_ℂ) ∂(μW.prod μN)) ∂(μW.prod μN) := by
  intro hH k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq hDS hgap hok hS v hv w hw ξ
  have hint := (GlobalTheory.BesselNorm.BesselConvolution.be_conv hH k r ε mu h R Wp z π u μW μN μG νq hDS hgap hok hS v hv).1 w hw
  obtain ⟨hz, hT, ⟨u₀, hπ⟩, -, hW, hN, -, -⟩ := hS
  obtain ⟨hψ1, hψm, -, hψc, hUW, -⟩ := GlobalTheory.T.besselCharacter_unipotentRadical_properties k r z Formalism.QuantumDeterminants.cStd hz
  obtain ⟨hmp, -, -, -, -, hae⟩ := GlobalTheory.T.besselSubgroup_parameter_measurePreserving k r z μW μN hok.1 hz hT hW hN
  obtain ⟨-, hmul, hunit, -⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_facts hT hπ
  have e0 : ((‖be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v ξ‖ ^ 2 : ℝ) : ℂ) =
      ⟪be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v ξ, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v ξ⟫_ℂ := by
    rw [inner_self_eq_norm_sq_to_K]; simp
  rw [e0]
  refine ((inner_integral_apply hint ξ _).1).trans (integral_congr_ae ?_)
  filter_upwards [hae] with p hp
  obtain ⟨-, h2, h3⟩ := inner_integral_apply hint ξ (beInt z Formalism.QuantumDeterminants.cStd π R.σ w v p ξ)
  refine h2.trans ((integral_comp_mp (hmp _ hp.1 _ hp.2).1 h3).trans (integral_congr_ae ?_))
  filter_upwards [hae] with q hq
  obtain ⟨⟨p1, p2⟩, hp1, hp2⟩ : ∃ p' : Mx k r × Mx k r, p'.1 = Matrix.of p.1 ∧ p'.2 = Matrix.of p.2 :=
    ⟨(_, _), rfl, rfl⟩
  obtain ⟨⟨q1, q2⟩, hq1, hq2⟩ : ∃ p' : Mx k r × Mx k r, p'.1 = Matrix.of q.1 ∧ p'.2 = Matrix.of q.2 :=
    ⟨(_, _), rfl, rfl⟩
  simp only at hp1 hp2 hq1 hq2
  have key : ∀ A : Mx k r, Matrix.of (fun i j => A i j) = A := fun A => rfl
  unfold beInt
  simp only [key]
  rw [← hp1, ← hp2] at hp
  rw [← hq1, ← hq2] at hq
  rw [← hp1, ← hp2, ← hq1, ← hq2]
  obtain ⟨hpi, hpp, hpp'⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uw_inv hp.1
  obtain ⟨hqi, -, -⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uw_inv hq.1
  have e1 : q1 * p1 * (p1⁻¹ * q2 * p1 * p2) = q1 * q2 * (p1 * p2) := by
    calc q1 * p1 * (p1⁻¹ * q2 * p1 * p2) = q1 * (p1 * p1⁻¹) * q2 * (p1 * p2) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hpp, Matrix.mul_one]
  have e2 : Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (p1⁻¹ * q2 * p1 * p2) =
      Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd q2 * Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd p2 := by
    obtain ⟨-, a2, -, a4⟩ := hψc p1 hp.1 q2 hq.2
    rw [(hψm _ a2 _ hp.2).2, a4]
  have e3 : π (q1 * p1)⁻¹ = (π p1⁻¹).comp (π q1⁻¹) := by
    rw [Matrix.mul_inv_rev, hmul _ hpi _ hqi]
  have hiso : ∀ a b, ⟪π p1⁻¹ a, π p1⁻¹ b⟫_ℂ = ⟪a, b⟫_ℂ :=
    (LinearMap.norm_map_iff_inner_map_map ((π p1⁻¹ : Wp →L[ℂ] Wp) : Wp →ₗ[ℂ] Wp)).1 (hunit _ hpi)
  have e4 : Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd p2 * star (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd p2) = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hψ1]; simp
  rw [e1, e2, e3]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, inner_smul_left, inner_smul_right,
    hiso, map_mul, starRingEnd_apply, star_mul', star_star]
  linear_combination (⟪v, R.σ (p1 * p2) w⟫_ℂ * star ⟪v, R.σ (q1 * q2 * (p1 * p2)) w⟫_ℂ *
    (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd q2 * ⟪π q1⁻¹ ξ, ξ⟫_ℂ)) * e4

namespace GlobalTheory.BesselNorm.GrowthIntegrability

open Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Introduce `H k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq hR hgap hok hS v hv w hw`. Take `⟨hz, hT, -, -, hWh, hNh, hGh, hq⟩` from `hS`. Use `hWh.1` as an intermediate fact. Use `hNh.1` as an intermediate fact. Use `hGh.1` as an intermediate fact.

Take `⟨C0, Ws, -, hdec⟩` from `GlobalTheory.BesselDecay.decay_TK H k r ε mu h R hR hgap hok v hv`. Use `set a := aOf r h - 1 with ha_def`. Establish `hAG : 0 ≤ AG k r` using `by unfold AG; positivity`. Establish `ha4` using `hok.2.2.2`. Establish `hn2 : (0 : ℝ) ≤ 9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2` using `by positivity`.

Establish `ha : 0 < a` using `by linarith`. Establish `ha2 : AG k r < a / 2` using `by linarith`. Establish `hsub : ∀ x y : Mx k r, B.gN (x * y) ≤ B.gN x * B.gN y` using `fun x y => PI.PolynomialProperness.GN.gN_mul_le x y`. Establish `hNIG : ∀ x ∈ GG k r, B.gN x⁻¹ = B.gN x ∧ 1 ≤ B.gN x` using `fun x hx => PI.PolynomialProperness.GN.polynomial_normInv k r x hx`. Establish `gN0 : ∀ g : Mx k r, 0 ≤ B.gN g` using `fun g => Real.sqrt_nonneg _`.

Use `set C := max (C0 * (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W w‖).sum) 0 with hC`. Establish `hC0 : 0 ≤ C` using `le_max_right _ _`. Establish `hb : ∀ g ∈ GG k r, ‖⟪v, R.σ g w⟫_ℂ‖ ≤ C * B.gN g ^ (-a)`. Introduce `g hg`. Establish `e : -a = 1 - aOf r h` using `by rw [ha_def]; ring`.

Rewrite using `[e]`. Conclude with `(hdec w hw g hg).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (gN0 g) _))`. Establish `hGae : ∀ᵐ y ∂μG, Matrix.of y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)` using `ae_iff.mpr hGh.2.2.1`. Establish `hWae : ∀ᵐ p1 ∂μW, Matrix.of p1 ∈ Formalism.QuantumDeterminants.UWset k r z` using `ae_iff.mpr hWh.2.2.1`. Establish `hNae : ∀ᵐ p2 ∂μN, Matrix.of p2 ∈ Formalism.QuantumDeterminants.Nset k r` using `ae_iff.mpr hNh.2.2.1`.

Establish `hPae : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r` using `(Measure.quasiMeasurePreserving_fst.ae hWae).and (Measure.quasiMeasurePreserving_snd.ae hNae)`. Establish `hQae : ∀ᵐ q ∂(μG.prod (μW.prod μN)), Matrix.of q.1 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ∧ Matrix.of q.2.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of q.2.2 ∈ Formalism.QuantumDeterminants.Nset k r` using `(Measure.quasiMeasurePreserving_fst.ae hGae).and (Measure.quasiMeasurePreserving_snd.ae hPae)`. Establish `sUH : ∀ p1 p2 : Formalism.QuantumDeterminants.Mt k r, Matrix.of p1 ∈ Formalism.QuantumDeterminants.UWset k r z → Matrix.of p2 ∈ Formalism.QuantumDeterminants.Nset k r → Matrix.of p1 * Matrix.of p2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)` using `fun p1 p2 h1 h2 => DDSmoothness.uh_mul h1.1 h2.1`. Establish `hφ : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) => (Matrix.of q.2.1 : Mx k r) * Matrix.of q.2.2 * Matrix.of q.1)`. Establish `h1 : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) => (Matrix.of q.2.1 : Mx k r))` using `continuous_fst.comp continuous_snd`.

Establish `h2 : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) => (Matrix.of q.2.2 : Mx k r))` using `continuous_snd.comp continuous_snd`. Establish `h3 : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) => (Matrix.of q.1 : Mx k r))` using `continuous_fst`. Conclude with `(h1.matrix_mul h2).matrix_mul h3`. Establish `hTm : MeasurableSet ((fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) => (Matrix.of q.2.1 : Mx k r) * Matrix.of q.2.2 * Matrix.of q.1) ⁻¹' Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants. …` using `(isClosed_UH.preimage hφ).measurableSet`. Establish `hTae : ∀ᵐ q ∂(μG.prod (μW.prod μN)), q ∈ ((fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) => (Matrix.of q.2.1 : Mx k r) * Matrix.of q.2.2 * Matrix.of q.1) ⁻¹' Formalism.QuantumDeterminants.UH (Formalism …` using `by filter_upwards [hQae] with q hq`.

Conclude with `DDSmoothness.uh_mul (sUH _ _ hq.2.1 hq.2.2) hq.1`. Establish `hcs` using `Formalism.FourierDecayAlt.P.S3dx4.sigma_contOn hR.2 w`. Establish `hof : Continuous (fun y : Formalism.QuantumDeterminants.Mt k r => (Matrix.of y : Mx k r))` using `continuous_id`. Establish `hc1 : AEStronglyMeasurable (fun y : Formalism.QuantumDeterminants.Mt k r => ⟪v, R.σ (Matrix.of y) w⟫_ℂ) μG`. Use `aesm_of_contOn (α := Formalism.QuantumDeterminants.Mt k r) (μ := μG) (s := {y : Formalism.QuantumDeterminants.Mt k r | Matrix.of y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)}) ?_ ?_ hGae` and prove the remaining obligations.

Establish `h0 : ContinuousOn (fun y : Formalism.QuantumDeterminants.Mt k r => R.σ (Matrix.of y) w) {y : Formalism.QuantumDeterminants.Mt k r | Matrix.of y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)}` using `hcs.comp hof.continuousOn (fun y hy => hy)`. Conclude with `continuousOn_const.inner h0`. Conclude with `(isClosed_UH.preimage hof).measurableSet`. Establish `hc2 : AEStronglyMeasurable (fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) => ⟪v, R.σ (Matrix.of q.2.1 * Matrix.of q.2.2 * Matrix.of q.1) w⟫_ℂ) (μG.prod (μW.prod μN))` using `aesm_of_contOn (α := Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (μ := μG.prod (μW.prod μN)) (continuousOn_const.inner (hcs.comp hφ.continuousOn (fun q hq => hq))) hTm hTae`. Establish `h1' : AEStronglyMeasurable (fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) => ⟪v, R.σ (Matrix.of q.1) w⟫_ℂ) (μG.prod (μW.prod μN))` using `AEStronglyMeasurable.comp_fst (μ := μG) (ν := μW.prod μN) hc1`.

Establish `hMi : Integrable (fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) => (C * C) * (B.gN (Matrix.of q.1) ^ (-(a / 2)) * B.gN (Matrix.of q.2.1 * Matrix.of q.2.2) ^ (-(a / 2)))) (μG.prod (μW.prod μN))` using `Integrable.const_mul (Integrable.mul_prod (hGG k r μG (a / 2) hGh ha2) (hGS k r z μW μN μG νq (a / 2) hz hT hWh hNh hGh hq ha2)) _`. Use `Integrable.mono' hMi (h1'.mul (continuous_star.comp_aestronglyMeasurable hc2)) ?_` and prove the remaining obligations. Use `filter_upwards [hQae] with q hq`. Take `⟨hy, hp1, hp2⟩` from `hq`. Establish `hs` using `sUH _ _ hp1 hp2`.

Use `set s := Matrix.of q.2.1 * Matrix.of q.2.2 with hs_def`. Use `set Y : Mx k r := Matrix.of q.1 with hY_def`. Establish `hg : s * Y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)` using `DDSmoothness.uh_mul hs hy`. Establish `hY1` using `(hNIG Y hy).2`. Establish `hg1` using `(hNIG _ hg).2`.

Establish `hs1` using `(hNIG s hs).2`. Establish `hSle : B.gN s ≤ B.gN (s * Y) * 1 * B.gN Y`. Establish `e : s = (s * Y) * Y⁻¹`. Rewrite using `[Matrix.mul_assoc, (uh_inv hy).2.1, Matrix.mul_one]`. Combine the equalities or inequalities in the displayed calculation.

Establish `key` using `key_bound hg1 le_rfl hY1 (by linarith) ha hSle`. Rewrite `key` using `[Real.one_rpow, one_mul]`. Rewrite using `[norm_mul, norm_star]`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem integrable_of_growth (hGG : GrowthG) (hGS : GrowthS) : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∀ v ∈ R.TK, ∀ w ∈ R.sm, Integrable (fun y : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) => ⟪v, R.σ (Matrix.of y.1) w⟫_ℂ * star ⟪v, R.σ (Matrix.of y.2.1 * Matrix.of y.2.2 * Matrix.of y.1) w⟫_ℂ) (μG.prod (μW.prod μN)) := by
  intro H k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq hR hgap hok hS v hv w hw
  obtain ⟨hz, hT, -, -, hWh, hNh, hGh, hq⟩ := hS
  have := hWh.1; have := hNh.1; have := hGh.1
  obtain ⟨C0, Ws, -, hdec⟩ := GlobalTheory.BesselDecay.decay_TK H k r ε mu h R hR hgap hok v hv
  set a := aOf r h - 1 with ha_def
  have hAG : 0 ≤ AG k r := by unfold AG; positivity
  have ha4 := hok.2.2.2
  have hn2 : (0 : ℝ) ≤ 9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by positivity
  have ha : 0 < a := by linarith
  have ha2 : AG k r < a / 2 := by linarith
  have hsub : ∀ x y : Mx k r, B.gN (x * y) ≤ B.gN x * B.gN y := fun x y => PI.PolynomialProperness.GN.gN_mul_le x y
  have hNIG : ∀ x ∈ GG k r, B.gN x⁻¹ = B.gN x ∧ 1 ≤ B.gN x :=
    fun x hx => PI.PolynomialProperness.GN.polynomial_normInv k r x hx
  have gN0 : ∀ g : Mx k r, 0 ≤ B.gN g := fun g => Real.sqrt_nonneg _
  set C := max (C0 * (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W w‖).sum) 0 with hC
  have hC0 : 0 ≤ C := le_max_right _ _
  have hb : ∀ g ∈ GG k r, ‖⟪v, R.σ g w⟫_ℂ‖ ≤ C * B.gN g ^ (-a) := by
    intro g hg
    have e : -a = 1 - aOf r h := by rw [ha_def]; ring
    rw [e]
    exact (hdec w hw g hg).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (gN0 g) _))
  have hGae : ∀ᵐ y ∂μG, Matrix.of y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := ae_iff.mpr hGh.2.2.1
  have hWae : ∀ᵐ p1 ∂μW, Matrix.of p1 ∈ Formalism.QuantumDeterminants.UWset k r z := ae_iff.mpr hWh.2.2.1
  have hNae : ∀ᵐ p2 ∂μN, Matrix.of p2 ∈ Formalism.QuantumDeterminants.Nset k r := ae_iff.mpr hNh.2.2.1
  have hPae : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r :=
    (Measure.quasiMeasurePreserving_fst.ae hWae).and (Measure.quasiMeasurePreserving_snd.ae hNae)
  have hQae : ∀ᵐ q ∂(μG.prod (μW.prod μN)), Matrix.of q.1 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ∧
      Matrix.of q.2.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of q.2.2 ∈ Formalism.QuantumDeterminants.Nset k r :=
    (Measure.quasiMeasurePreserving_fst.ae hGae).and (Measure.quasiMeasurePreserving_snd.ae hPae)
  have sUH : ∀ p1 p2 : Formalism.QuantumDeterminants.Mt k r, Matrix.of p1 ∈ Formalism.QuantumDeterminants.UWset k r z → Matrix.of p2 ∈ Formalism.QuantumDeterminants.Nset k r →
      Matrix.of p1 * Matrix.of p2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
    fun p1 p2 h1 h2 => DDSmoothness.uh_mul h1.1 h2.1
  have hφ : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      (Matrix.of q.2.1 : Mx k r) * Matrix.of q.2.2 * Matrix.of q.1) := by
    have h1 : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
        (Matrix.of q.2.1 : Mx k r)) := continuous_fst.comp continuous_snd
    have h2 : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
        (Matrix.of q.2.2 : Mx k r)) := continuous_snd.comp continuous_snd
    have h3 : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
        (Matrix.of q.1 : Mx k r)) := continuous_fst
    exact (h1.matrix_mul h2).matrix_mul h3
  have hTm : MeasurableSet ((fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      (Matrix.of q.2.1 : Mx k r) * Matrix.of q.2.2 * Matrix.of q.1) ⁻¹' Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :=
    (isClosed_UH.preimage hφ).measurableSet
  have hTae : ∀ᵐ q ∂(μG.prod (μW.prod μN)), q ∈ ((fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      (Matrix.of q.2.1 : Mx k r) * Matrix.of q.2.2 * Matrix.of q.1) ⁻¹' Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) := by
    filter_upwards [hQae] with q hq
    exact DDSmoothness.uh_mul (sUH _ _ hq.2.1 hq.2.2) hq.1
  have hcs := Formalism.FourierDecayAlt.P.S3dx4.sigma_contOn hR.2 w
  have hof : Continuous (fun y : Formalism.QuantumDeterminants.Mt k r => (Matrix.of y : Mx k r)) := continuous_id
  have hc1 : AEStronglyMeasurable (fun y : Formalism.QuantumDeterminants.Mt k r => ⟪v, R.σ (Matrix.of y) w⟫_ℂ) μG := by
    refine aesm_of_contOn (α := Formalism.QuantumDeterminants.Mt k r) (μ := μG)
      (s := {y : Formalism.QuantumDeterminants.Mt k r | Matrix.of y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)}) ?_ ?_ hGae
    · have h0 : ContinuousOn (fun y : Formalism.QuantumDeterminants.Mt k r => R.σ (Matrix.of y) w)
          {y : Formalism.QuantumDeterminants.Mt k r | Matrix.of y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} :=
        hcs.comp hof.continuousOn (fun y hy => hy)
      exact continuousOn_const.inner h0
    · exact (isClosed_UH.preimage hof).measurableSet
  have hc2 : AEStronglyMeasurable (fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      ⟪v, R.σ (Matrix.of q.2.1 * Matrix.of q.2.2 * Matrix.of q.1) w⟫_ℂ) (μG.prod (μW.prod μN)) :=
    aesm_of_contOn (α := Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (μ := μG.prod (μW.prod μN))
      (continuousOn_const.inner (hcs.comp hφ.continuousOn (fun q hq => hq))) hTm hTae
  have h1' : AEStronglyMeasurable (fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      ⟪v, R.σ (Matrix.of q.1) w⟫_ℂ) (μG.prod (μW.prod μN)) :=
    AEStronglyMeasurable.comp_fst (μ := μG) (ν := μW.prod μN) hc1
  have hMi : Integrable (fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      (C * C) * (B.gN (Matrix.of q.1) ^ (-(a / 2)) *
        B.gN (Matrix.of q.2.1 * Matrix.of q.2.2) ^ (-(a / 2)))) (μG.prod (μW.prod μN)) :=
    Integrable.const_mul (Integrable.mul_prod (hGG k r μG (a / 2) hGh ha2)
      (hGS k r z μW μN μG νq (a / 2) hz hT hWh hNh hGh hq ha2)) _
  refine Integrable.mono' hMi (h1'.mul (continuous_star.comp_aestronglyMeasurable hc2)) ?_
  filter_upwards [hQae] with q hq
  obtain ⟨hy, hp1, hp2⟩ := hq
  have hs := sUH _ _ hp1 hp2
  set s := Matrix.of q.2.1 * Matrix.of q.2.2 with hs_def
  set Y : Mx k r := Matrix.of q.1 with hY_def
  have hg : s * Y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul hs hy
  have hY1 := (hNIG Y hy).2
  have hg1 := (hNIG _ hg).2
  have hs1 := (hNIG s hs).2
  have hSle : B.gN s ≤ B.gN (s * Y) * 1 * B.gN Y := by
    have e : s = (s * Y) * Y⁻¹ := by
      rw [Matrix.mul_assoc, (uh_inv hy).2.1, Matrix.mul_one]
    calc B.gN s = B.gN ((s * Y) * Y⁻¹) := by rw [← e]
      _ ≤ B.gN (s * Y) * B.gN Y⁻¹ := hsub _ _
      _ = _ := by rw [(hNIG _ hy).1, mul_one]
  have key := key_bound hg1 le_rfl hY1 (by linarith) ha hSle
  rw [Real.one_rpow, one_mul] at key
  rw [norm_mul, norm_star]
  calc ‖⟪v, R.σ Y w⟫_ℂ‖ * ‖⟪v, R.σ (s * Y) w⟫_ℂ‖
      ≤ (C * B.gN Y ^ (-a)) * (C * B.gN (s * Y) ^ (-a)) :=
        mul_le_mul (hb Y hy) (hb _ hg) (norm_nonneg _) (mul_nonneg hC0 (Real.rpow_nonneg (gN0 _) _))
    _ = (C * C) * (B.gN Y ^ (-a) * B.gN (s * Y) ^ (-a)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left key (mul_nonneg hC0 hC0)

/- English proof (translation)
The claim follows from `integrable_of_growth GlobalTheory.T.growth_unitaryGroup_rpow_neg_integrable GlobalTheory.T.besselGrowth_stabilizer_unipotent`.
-/
private theorem integrable_GS : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∀ v ∈ R.TK, ∀ w ∈ R.sm, Integrable (fun y : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) => ⟪v, R.σ (Matrix.of y.1) w⟫_ℂ * star ⟪v, R.σ (Matrix.of y.2.1 * Matrix.of y.2.2 * Matrix.of y.1) w⟫_ℂ) (μG.prod (μW.prod μN)) :=
  integrable_of_growth GlobalTheory.T.growth_unitaryGroup_rpow_neg_integrable GlobalTheory.T.besselGrowth_stabilizer_unipotent

end GlobalTheory.BesselNorm.GrowthIntegrability

noncomputable section

namespace GlobalTheory.BesselNorm

open Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity

/- English proof (translation)
Unfold `Formalism.QuantumDeterminants.fdegHC`. Apply `div_pos` to reduce the goal to its premises. Use `Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => ?_` and prove the remaining obligations. Establish `hab : a < b` using `(Finset.mem_filter.mp hb).2`. Conclude with `abs_pos.mpr (sub_ne_zero.mpr fun h => hab.ne (hlam h))`.

Use `Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => ?_` and prove the remaining obligations. Conclude with `sub_pos.mpr (Nat.cast_lt.mpr (Finset.mem_filter.mp hb).2)`.
-/
theorem fdegHC_pos {n : ℕ} (lam : Fin n → ℝ) (hlam : Function.Injective lam) :
    0 < Formalism.QuantumDeterminants.fdegHC lam := by
  unfold Formalism.QuantumDeterminants.fdegHC
  apply div_pos
  · refine Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => ?_
    have hab : a < b := (Finset.mem_filter.mp hb).2
    exact abs_pos.mpr (sub_ne_zero.mpr fun h => hab.ne (hlam h))
  · refine Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => ?_
    exact sub_pos.mpr (Nat.cast_lt.mpr (Finset.mem_filter.mp hb).2)

/- English proof (translation)
Establish `hof : Continuous (fun y : Formalism.QuantumDeterminants.Mt k r => (Matrix.of y : Mx k r))` using `continuous_id`. Establish `hm : MeasurableSet {y : Formalism.QuantumDeterminants.Mt k r | Matrix.of y ∈ GG k r}` using `(isClosed_UH.preimage hof).measurableSet`. Use `set f : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞ := ({y : Formalism.QuantumDeterminants.Mt k r | Matrix.of y ∈ GG k r}ᶜ).indicator 1 with hf`. Establish `hfm : Measurable f` using `measurable_one.indicator hm.compl`. Establish `h1 : ∫⁻ x, f x ∂μG = ∫⁻ x, ∫⁻ s, f (mulMt s x) ∂μS ∂νq` using `hq f hfm`.

Establish `h2 : ∫⁻ x, f x ∂μG = 0`. Rewrite using `[hf, lintegral_indicator_one hm.compl]`. Conclude with `hG`. Establish `h3 : Measurable (fun x => ∫⁻ s, f (mulMt s x) ∂μS)` using `(hfm.comp measurable_mulMt).lintegral_prod_left'`. Rewrite `h1` using `[h2, eq_comm, lintegral_eq_zero_iff h3]`.

Use `filter_upwards [h1] with x hx`. Assume the negation of the conclusion as `hxG`. Establish `h4 : ∫⁻ s, f (mulMt s x) ∂μS = ∫⁻ _s, 1 ∂μS`. Apply `lintegral_congr_ae` to reduce the goal to its premises. Use `filter_upwards [hS] with s hs`.

Establish `: mulMt s x ∈ ({y : Formalism.QuantumDeterminants.Mt k r | Matrix.of y ∈ GG k r}ᶜ)`. Introduce `hsx`. Apply `hxG` to reduce the goal to its premises. Establish `hsx' : Matrix.of s * Matrix.of x ∈ GG k r` using `hsx`. Use `DDSmoothness.uh_mul (uh_inv hs).1 hsx'` as an intermediate fact.

Rewrite `this` using `[← Matrix.mul_assoc, (uh_inv hs).2.2, Matrix.one_mul]`. Then use the resulting hypothesis. Rewrite using `[hf, Set.indicator_of_mem this]`. Both sides reduce to the same expression. Rewrite `hx` using `[h4]`. Simplify using `only [lintegral_const, one_mul, Pi.zero_apply, Measure.measure_univ_eq_zero] at hx`.

Conclude with `h0 hx`.
-/
theorem quot_ae {k r : ℕ} {μG μS νq : Measure (Formalism.QuantumDeterminants.Mt k r)} [SFinite μS]
    (hq : PI.BesselPeriodGGP.IsQuotMeas μG μS νq) (hG : ∀ᵐ x ∂μG, Matrix.of x ∈ GG k r)
    (hS : ∀ᵐ x ∂μS, Matrix.of x ∈ GG k r) (h0 : μS ≠ 0) : ∀ᵐ x ∂νq, Matrix.of x ∈ GG k r := by
  have hof : Continuous (fun y : Formalism.QuantumDeterminants.Mt k r => (Matrix.of y : Mx k r)) := continuous_id
  have hm : MeasurableSet {y : Formalism.QuantumDeterminants.Mt k r | Matrix.of y ∈ GG k r} :=
    (isClosed_UH.preimage hof).measurableSet
  set f : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞ := ({y : Formalism.QuantumDeterminants.Mt k r | Matrix.of y ∈ GG k r}ᶜ).indicator 1 with hf
  have hfm : Measurable f := measurable_one.indicator hm.compl
  have h1 : ∫⁻ x, f x ∂μG = ∫⁻ x, ∫⁻ s, f (mulMt s x) ∂μS ∂νq := hq f hfm
  have h2 : ∫⁻ x, f x ∂μG = 0 := by
    rw [hf, lintegral_indicator_one hm.compl]; exact hG
  have h3 : Measurable (fun x => ∫⁻ s, f (mulMt s x) ∂μS) :=
    (hfm.comp measurable_mulMt).lintegral_prod_left'
  rw [h2, eq_comm, lintegral_eq_zero_iff h3] at h1
  filter_upwards [h1] with x hx
  by_contra hxG
  have h4 : ∫⁻ s, f (mulMt s x) ∂μS = ∫⁻ _s, 1 ∂μS := by
    apply lintegral_congr_ae
    filter_upwards [hS] with s hs
    have : mulMt s x ∈ ({y : Formalism.QuantumDeterminants.Mt k r | Matrix.of y ∈ GG k r}ᶜ) := by
      intro hsx
      apply hxG
      have hsx' : Matrix.of s * Matrix.of x ∈ GG k r := hsx
      have := DDSmoothness.uh_mul (uh_inv hs).1 hsx'
      rwa [← Matrix.mul_assoc, (uh_inv hs).2.2, Matrix.one_mul] at this
    rw [hf, Set.indicator_of_mem this]; rfl
  rw [h4] at hx
  simp only [lintegral_const, one_mul, Pi.zero_apply, Measure.measure_univ_eq_zero] at hx
  exact h0 hx

/- English proof (translation)
Establish `hm : Continuous (fun p1 : Formalism.QuantumDeterminants.Mt k r => Formalism.QuantumDeterminants.Hpk k r * (Matrix.of p1 : Mx k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r)` using `(continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const`. Establish `hmaps : Set.MapsTo (fun p1 : Formalism.QuantumDeterminants.Mt k r => Formalism.QuantumDeterminants.Hpk k r * (Matrix.of p1 : Mx k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r) {p1 : Formalism.QuantumDeterminants.Mt k r | Matrix.of p1 ∈ Formalism.QuantumDeterminants.UWset k r z} (F …`. Introduce `p1 hp1`. Establish `e : (Matrix.of p1 : Mx k r)⁻¹ = Formalism.QuantumDeterminants.Hpk k r * (Matrix.of p1 : Mx k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r` using `PI.HwUniqW.inv_eq_UH hp1.1`. Use `show Formalism.QuantumDeterminants.Hpk k r * (Matrix.of p1 : Mx k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r ∈ Formalism.QuantumDeterminants.UWset k r z`.

Rewrite using `[← e]`. Conclude with `(uw_inv hp1).1`. Use `((piW_cont hT hπ ξ).comp hm.continuousOn hmaps).congr ?_` and prove the remaining obligations. Introduce `p1 hp1`. Establish `e : (Matrix.of p1 : Mx k r)⁻¹ = Formalism.QuantumDeterminants.Hpk k r * (Matrix.of p1 : Mx k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r` using `PI.HwUniqW.inv_eq_UH hp1.1`.

Simplify using `only [Function.comp]`. Rewrite using `[e]`.
-/
theorem piInv_contOn {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π) (ξ : Wp) :
    ContinuousOn (fun p1 : Formalism.QuantumDeterminants.Mt k r => π (Matrix.of p1)⁻¹ ξ)
      {p1 : Formalism.QuantumDeterminants.Mt k r | Matrix.of p1 ∈ Formalism.QuantumDeterminants.UWset k r z} := by
  have hm : Continuous (fun p1 : Formalism.QuantumDeterminants.Mt k r =>
      Formalism.QuantumDeterminants.Hpk k r * (Matrix.of p1 : Mx k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r) :=
    (continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const
  have hmaps : Set.MapsTo (fun p1 : Formalism.QuantumDeterminants.Mt k r =>
      Formalism.QuantumDeterminants.Hpk k r * (Matrix.of p1 : Mx k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r)
      {p1 : Formalism.QuantumDeterminants.Mt k r | Matrix.of p1 ∈ Formalism.QuantumDeterminants.UWset k r z} (Formalism.QuantumDeterminants.UWset k r z) := by
    intro p1 hp1
    have e : (Matrix.of p1 : Mx k r)⁻¹ = Formalism.QuantumDeterminants.Hpk k r * (Matrix.of p1 : Mx k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r :=
      PI.HwUniqW.inv_eq_UH hp1.1
    show Formalism.QuantumDeterminants.Hpk k r * (Matrix.of p1 : Mx k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r ∈ Formalism.QuantumDeterminants.UWset k r z
    rw [← e]; exact (uw_inv hp1).1
  refine ((piW_cont hT hπ ξ).comp hm.continuousOn hmaps).congr ?_
  intro p1 hp1
  have e : (Matrix.of p1 : Mx k r)⁻¹ = Formalism.QuantumDeterminants.Hpk k r * (Matrix.of p1 : Mx k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r :=
    PI.HwUniqW.inv_eq_UH hp1.1
  simp only [Function.comp]
  rw [e]

def kern {k r : ℕ} (R : Rep k r) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (v w : R.H) (ξ : Wp)
    (y : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) : ℂ :=
  ⟪v, R.σ (Matrix.of y.1) w⟫_ℂ * star ⟪v, R.σ (Matrix.of y.2.1 * Matrix.of y.2.2 * Matrix.of y.1) w⟫_ℂ *
    (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (Matrix.of y.2.2) * ⟪π (Matrix.of y.2.1)⁻¹ ξ, ξ⟫_ℂ)

def good (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) :
    Set (Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) :=
  {y | Matrix.of y.1 ∈ GG k r ∧ Matrix.of y.2.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of y.2.2 ∈ GG k r}

/- English proof (translation)
Establish `h1 : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) => (Matrix.of q.2.1 : Mx k r))` using `continuous_fst.comp continuous_snd`. Establish `h2 : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) => (Matrix.of q.2.2 : Mx k r))` using `continuous_snd.comp continuous_snd`. Establish `h3 : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) => (Matrix.of q.1 : Mx k r))` using `continuous_fst`. Conclude with `((isClosed_UH.preimage h3).inter (((isClosed_UW z).preimage h1).inter (isClosed_UH.preimage h2))).measurableSet`.
-/
theorem good_meas (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : MeasurableSet (good k r z) := by
  have h1 : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      (Matrix.of q.2.1 : Mx k r)) := continuous_fst.comp continuous_snd
  have h2 : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      (Matrix.of q.2.2 : Mx k r)) := continuous_snd.comp continuous_snd
  have h3 : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      (Matrix.of q.1 : Mx k r)) := continuous_fst
  exact ((isClosed_UH.preimage h3).inter (((isClosed_UW z).preimage h1).inter
    (isClosed_UH.preimage h2))).measurableSet

/- English proof (translation)
Establish `h1 : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) => (Matrix.of q.2.1 : Mx k r))` using `continuous_fst.comp continuous_snd`. Establish `h2 : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) => (Matrix.of q.2.2 : Mx k r))` using `continuous_snd.comp continuous_snd`. Establish `h3 : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) => (Matrix.of q.1 : Mx k r))` using `continuous_fst`. Establish `a1 : ContinuousOn (fun y : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) => R.σ (Matrix.of y.1) w) (good k r z)` using `hc.comp h3.continuousOn (fun y hy => hy.1)`. Establish `a2 : ContinuousOn (fun y : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) => R.σ (Matrix.of y.2.1 * Matrix.of y.2.2 * Matrix.of y.1) w) (good k r z)` using `hc.comp ((h1.matrix_mul h2).matrix_mul h3).continuousOn (fun y hy => DDSmoothness.uh_mul (DDSmoothness.uh_mul hy.2.1.1 hy.2.2) hy.1)`.

Establish `a3 : ContinuousOn (fun y : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) => π (Matrix.of y.2.1)⁻¹ ξ) (good k r z)` using `(piInv_contOn hT hπ ξ).comp (continuous_fst.comp continuous_snd).continuousOn (fun y hy => hy.2.1)`. Establish `hK : ContinuousOn (kern R z π v w ξ) (good k r z)` using `((continuousOn_const.inner a1).mul (continuous_star.comp_continuousOn (continuousOn_const.inner a2))).mul (((psi_cont z _).comp h2).continuousOn.mul (a3.inner continuousOn_const))`. Use `ContinuousOn.measurable_piecewise hK (continuousOn_const (c := (0 : ℂ))) (good_meas k r z)` as an intermediate fact. Rewrite using `[← Set.piecewise_eq_indicator]`. Conclude with `this`.
-/
theorem kern_meas {k r : ℕ} (R : Rep k r) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π) (v w : R.H) (ξ : Wp)
    (hc : ContinuousOn (fun g => R.σ g w) (GG k r)) :
    Measurable ((good k r z).indicator (kern R z π v w ξ)) := by
  classical
  have h1 : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      (Matrix.of q.2.1 : Mx k r)) := continuous_fst.comp continuous_snd
  have h2 : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      (Matrix.of q.2.2 : Mx k r)) := continuous_snd.comp continuous_snd
  have h3 : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      (Matrix.of q.1 : Mx k r)) := continuous_fst
  have a1 : ContinuousOn (fun y : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      R.σ (Matrix.of y.1) w) (good k r z) := hc.comp h3.continuousOn (fun y hy => hy.1)
  have a2 : ContinuousOn (fun y : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      R.σ (Matrix.of y.2.1 * Matrix.of y.2.2 * Matrix.of y.1) w) (good k r z) :=
    hc.comp ((h1.matrix_mul h2).matrix_mul h3).continuousOn
      (fun y hy => DDSmoothness.uh_mul (DDSmoothness.uh_mul hy.2.1.1 hy.2.2) hy.1)
  have a3 : ContinuousOn (fun y : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      π (Matrix.of y.2.1)⁻¹ ξ) (good k r z) :=
    (piInv_contOn hT hπ ξ).comp (continuous_fst.comp continuous_snd).continuousOn (fun y hy => hy.2.1)
  have hK : ContinuousOn (kern R z π v w ξ) (good k r z) :=
    ((continuousOn_const.inner a1).mul (continuous_star.comp_continuousOn (continuousOn_const.inner a2))).mul
      (((psi_cont z _).comp h2).continuousOn.mul (a3.inner continuousOn_const))
  have := ContinuousOn.measurable_piecewise hK (continuousOn_const (c := (0 : ℂ))) (good_meas k r z)
  rw [← Set.piecewise_eq_indicator]
  exact this

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Take `⟨hmul, hone, hun, hsm, hTK, -, -, -, hcont⟩` from `GlobalTheory.rep_basic_of_isDS hy.1.2.2.1 k r ε mu R hR`. Establish `hfub` using `GrowthIntegrability.integrable_GS hy k r ε mu h R Wp z π u μW μN μG νq hR hgap hok hS v hv w hw`. Establish `hpt` using `InnerIntegralSquares.double_integral hy k r ε mu h R Wp z π u μW μN μG νq hR hgap hok hS v hv`. Establish `hconv` using `(BesselConvolution.be_conv hy k r ε mu h R Wp z π u μW μN μG νq hR hgap hok hS v hv).1 v (hTK v hv)`. Take `⟨hz, hT, ⟨u₀, hπ⟩, -, hWh, hNh, hGh, hq⟩` from `hS`.

Use `hWh.1` as an intermediate fact. Use `hNh.1` as an intermediate fact. Use `hGh.1` as an intermediate fact. Establish `hGae : ∀ᵐ y ∂μG, Matrix.of y ∈ GG k r` using `ae_iff.mpr hGh.2.2.1`. Establish `hWae : ∀ᵐ p1 ∂μW, Matrix.of p1 ∈ Formalism.QuantumDeterminants.UWset k r z` using `ae_iff.mpr hWh.2.2.1`.

Establish `hNae : ∀ᵐ p2 ∂μN, Matrix.of p2 ∈ Formalism.QuantumDeterminants.Nset k r` using `ae_iff.mpr hNh.2.2.1`. Establish `hPae : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ GG k r` using `(Measure.quasiMeasurePreserving_fst.ae hWae).and (Measure.quasiMeasurePreserving_snd.ae (hNae.mono fun _ hx => hx.1))`. Establish `hQae : ∀ᵐ q ∂(μG.prod (μW.prod μN)), q ∈ good k r z` using `(Measure.quasiMeasurePreserving_fst.ae hGae).and (Measure.quasiMeasurePreserving_snd.ae hPae)`. Establish `hof : Continuous (fun y : Formalism.QuantumDeterminants.Mt k r => (Matrix.of y : Mx k r))` using `continuous_id`. Establish `hSeq : muSof μW μN = (μW.prod μN).map (fun p => mulMt p.1 p.2)` using `rfl`.

Establish `hsf : SFinite (muSof μW μN)` using `by rw [hSeq]; infer_instance`. Establish `hSae : ∀ᵐ s ∂(muSof μW μN), Matrix.of s ∈ GG k r`. Rewrite using `[hSeq]`. Use `(ae_map_iff measurable_mulMt.aemeasurable (isClosed_UH.preimage hof).measurableSet).2 ?_` and prove the remaining obligations. Use `filter_upwards [hPae] with p hp`.

Conclude with `DDSmoothness.uh_mul hp.1.1 hp.2`. Establish `hS0 : muSof μW μN ≠ 0`. Rewrite using `[hSeq, Ne, Measure.map_eq_zero_iff measurable_mulMt.aemeasurable]`. Introduce `h0`. Establish `h1 : (μW.prod μN) (Set.univ ×ˢ Set.univ) = 0` using `by rw [h0]; rfl`.

Rewrite `h1` using `[Measure.prod_prod, mul_eq_zero, Measure.measure_univ_eq_zero, Measure.measure_univ_eq_zero]`. Conclude with `h1.elim hWh.2.1 hNh.2.1`. Establish `hνae` using `quot_ae hq hGae hSae hS0`. Use `set F := (good k r z).indicator (kern R z π v w ξ) with hF`. Establish `hFm : Measurable F` using `kern_meas R hT hπ v w ξ (hcont w)`.

Establish `hFK : F =ᵐ[μG.prod (μW.prod μN)] kern R z π v w ξ` using `by filter_upwards [hQae] with q hq`. Rewrite using `[hF, Set.indicator_of_mem hq]`. Establish `hFi : Integrable F (μG.prod (μW.prod μN))`. Use `Integrable.mono' (hfub.norm.mul_const (‖ξ‖ * ‖ξ‖)) hFm.aestronglyMeasurable ?_` and prove the remaining obligations. Use `filter_upwards [hQae] with q hq`.

Rewrite using `[hF, Set.indicator_of_mem hq, kern, norm_mul]`. Use `mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)` and prove the remaining obligations. Rewrite using `[norm_mul, psi_norm, one_mul]`. Use `(norm_inner_le_norm _ _).trans ?_` and prove the remaining obligations. Rewrite using `[piW_unitary hT hπ _ (uw_inv hq.2.1).1 ξ]`.

Use `set f : Formalism.QuantumDeterminants.Mt k r → ℂ := fun x => ∫ q, F (x, q) ∂(μW.prod μN) with hf`. Establish `hfm : Measurable f` using `(hFm.stronglyMeasurable.integral_prod_right' (ν := μW.prod μN)).measurable`. Establish `hfi : Integrable f μG` using `hFi.integral_prod_left`. Take `⟨-, hgi, hge⟩` from `GlobalTheory.T.weil_formula_integrable_complex k r μG (muSof μW μN) νq f hq hfm hfi`. Establish `hg : ∀ᵐ x ∂νq, ∫ s, f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂(muSof μW μN) = ((‖be z Formalism.QuantumDeterminants.cStd π R.σ μW μN (R.σ (Matrix.of x) w) v ξ‖ ^ 2 : ℝ) : ℂ)` using `by filter_upwards [hνae] with x hx`.

Rewrite using `[hpt _ (hsm _ hx w hw) ξ, hSeq]`. Establish `hm : Measurable (fun s : Formalism.QuantumDeterminants.Mt k r => f (mulMt s x))` using `hfm.comp (measurable_mulMt.comp (measurable_id.prodMk measurable_const))`. Use `(integral_map measurable_mulMt.aemeasurable hm.aestronglyMeasurable).trans ?_` and prove the remaining obligations. Apply `integral_congr_ae` to reduce the goal to its premises. Use `filter_upwards [hPae] with p hp`.

Apply `integral_congr_ae` to reduce the goal to its premises. Use `filter_upwards [hPae] with q hq'`. Establish `hs : Matrix.of p.1 * Matrix.of p.2 ∈ GG k r` using `DDSmoothness.uh_mul hp.1.1 hp.2`. Establish `ht : Matrix.of q.1 * Matrix.of q.2 ∈ GG k r` using `DDSmoothness.uh_mul hq'.1.1 hq'.2`. Establish `hgood : (mulMt (mulMt p.1 p.2) x, q) ∈ good k r z` using `⟨DDSmoothness.uh_mul hs hx, hq'.1, hq'.2⟩`.

Rewrite using `[hF, Set.indicator_of_mem hgood, ← hmul _ hs _ hx, ← hmul _ (DDSmoothness.uh_mul ht hs) _ hx, Matrix.mul_assoc (Matrix.of q.1 * Matrix.of q.2)]`. Both sides reduce to the same expression. Establish `hI : ∫ x, f x ∂μG = ((‖w‖ ^ 2 : ℝ) : ℂ) / (d : ℂ) * ⟪be z Formalism.QuantumDeterminants.cStd π R.σ μW μN v v ξ, ξ⟫_ℂ`. Establish `e1 : ∫ x, f x ∂μG = ∫ q, ∫ x, F (x, q) ∂μG ∂(μW.prod μN)` using `integral_integral_swap (f := fun x q => F (x, q)) hFi`. Establish `e2 : be z Formalism.QuantumDeterminants.cStd π R.σ μW μN v v ξ = ∫ p, beInt z Formalism.QuantumDeterminants.cStd π R.σ v v p ξ ∂(μW.prod μN)` using `ContinuousLinearMap.integral_apply hconv ξ`.

Establish `e3 : ⟪be z Formalism.QuantumDeterminants.cStd π R.σ μW μN v v ξ, ξ⟫_ℂ = ∫ p, ⟪beInt z Formalism.QuantumDeterminants.cStd π R.σ v v p ξ, ξ⟫_ℂ ∂(μW.prod μN)`. Rewrite using `[← inner_conj_symm, e2, ← integral_inner (hconv.apply_continuousLinearMap ξ), ← integral_conj]`. Simplify using `only [inner_conj_symm]`. Rewrite using `[e1, e3, ← integral_const_mul]`. Apply `integral_congr_ae` to reduce the goal to its premises.

Use `filter_upwards [hPae] with q hq'`. Establish `ht : Matrix.of q.1 * Matrix.of q.2 ∈ GG k r` using `DDSmoothness.uh_mul hq'.1.1 hq'.2`. Establish `e4 : ∀ᵐ x ∂μG, F (x, q) = ⟪v, R.σ (Matrix.of x) w⟫_ℂ * star ⟪R.σ (Matrix.of q.1 * Matrix.of q.2)⁻¹ v, R.σ (Matrix.of x) w⟫_ℂ * (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (Matrix.of q.2) * ⟪π (Matrix.of q.1)⁻¹ ξ, ξ⟫_ℂ)` using `by filter_upwards [hGae] with x hx`. Establish `hgood : (x, q) ∈ good k r z` using `⟨hx, hq'.1, hq'.2⟩`. Rewrite using `[hF, Set.indicator_of_mem hgood, kern, hmul _ ht _ hx, sigma_inner hR.2 ht]`.

Rewrite using `[integral_congr_ae e4, integral_mul_const, hSd, ← inner_conj_symm v, ← sigma_inner hR.2 ht, inner_self_eq_norm_sq_to_K]`. Simplify using `only [beInt, ContinuousLinearMap.smul_apply, inner_smul_left, map_mul, RCLike.star_def, Complex.conj_conj]`. Use `push_cast`. Simplify using `only [Complex.coe_algebraMap]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hgi'` using `hgi.congr hg`. Use `⟨hgi'.re.congr (Filter.Eventually.of_forall fun x => Complex.ofReal_re _), ?_⟩` and prove the remaining obligations. Rewrite using `[← hI, hge, integral_congr_ae hg, integral_complex_ofReal]`.
-/
theorem norm_integral (hy : Hyps) (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ)
    (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (hR : R.IsDS ε mu) (hgap : Formalism.QuantumDeterminants.GapAtLeast ε mu h)
    (hok : GapOK k r h) (hS : SideG k r z π u μW μN μG νq) (d : ℝ)
    (hSd : ∀ v w v' w' : R.H, ∫ x, ⟪w, R.σ (Matrix.of x) v⟫_ℂ * star ⟪w', R.σ (Matrix.of x) v'⟫_ℂ ∂μG =
      ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ))
    (v : R.H) (hv : v ∈ R.TK) (ξ : Wp) (w : R.H) (hw : w ∈ R.sm) :
    Integrable (fun x : Formalism.QuantumDeterminants.Mt k r =>
      ‖be z Formalism.QuantumDeterminants.cStd π R.σ μW μN (R.σ (Matrix.of x) w) v ξ‖ ^ 2) νq ∧
    ((∫ x : Formalism.QuantumDeterminants.Mt k r, ‖be z Formalism.QuantumDeterminants.cStd π R.σ μW μN (R.σ (Matrix.of x) w) v ξ‖ ^ 2 ∂νq : ℝ) : ℂ) =
      ((‖w‖ ^ 2 : ℝ) : ℂ) / (d : ℂ) * ⟪be z Formalism.QuantumDeterminants.cStd π R.σ μW μN v v ξ, ξ⟫_ℂ := by
  obtain ⟨hmul, hone, hun, hsm, hTK, -, -, -, hcont⟩ := GlobalTheory.rep_basic_of_isDS hy.1.2.2.1 k r ε mu R hR
  have hfub := GrowthIntegrability.integrable_GS hy k r ε mu h R Wp z π u μW μN μG νq hR hgap hok hS v hv w hw
  have hpt := InnerIntegralSquares.double_integral hy k r ε mu h R Wp z π u μW μN μG νq hR hgap hok hS v hv
  have hconv := (BesselConvolution.be_conv hy k r ε mu h R Wp z π u μW μN μG νq hR hgap hok hS v hv).1 v (hTK v hv)
  obtain ⟨hz, hT, ⟨u₀, hπ⟩, -, hWh, hNh, hGh, hq⟩ := hS
  have := hWh.1; have := hNh.1; have := hGh.1
  have hGae : ∀ᵐ y ∂μG, Matrix.of y ∈ GG k r := ae_iff.mpr hGh.2.2.1
  have hWae : ∀ᵐ p1 ∂μW, Matrix.of p1 ∈ Formalism.QuantumDeterminants.UWset k r z := ae_iff.mpr hWh.2.2.1
  have hNae : ∀ᵐ p2 ∂μN, Matrix.of p2 ∈ Formalism.QuantumDeterminants.Nset k r := ae_iff.mpr hNh.2.2.1
  have hPae : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ GG k r :=
    (Measure.quasiMeasurePreserving_fst.ae hWae).and
      (Measure.quasiMeasurePreserving_snd.ae (hNae.mono fun _ hx => hx.1))
  have hQae : ∀ᵐ q ∂(μG.prod (μW.prod μN)), q ∈ good k r z :=
    (Measure.quasiMeasurePreserving_fst.ae hGae).and (Measure.quasiMeasurePreserving_snd.ae hPae)
  have hof : Continuous (fun y : Formalism.QuantumDeterminants.Mt k r => (Matrix.of y : Mx k r)) := continuous_id
  have hSeq : muSof μW μN = (μW.prod μN).map (fun p => mulMt p.1 p.2) := rfl
  have hsf : SFinite (muSof μW μN) := by rw [hSeq]; infer_instance
  have hSae : ∀ᵐ s ∂(muSof μW μN), Matrix.of s ∈ GG k r := by
    rw [hSeq]
    refine (ae_map_iff measurable_mulMt.aemeasurable (isClosed_UH.preimage hof).measurableSet).2 ?_
    filter_upwards [hPae] with p hp
    exact DDSmoothness.uh_mul hp.1.1 hp.2
  have hS0 : muSof μW μN ≠ 0 := by
    rw [hSeq, Ne, Measure.map_eq_zero_iff measurable_mulMt.aemeasurable]
    intro h0
    have h1 : (μW.prod μN) (Set.univ ×ˢ Set.univ) = 0 := by rw [h0]; rfl
    rw [Measure.prod_prod, mul_eq_zero, Measure.measure_univ_eq_zero, Measure.measure_univ_eq_zero] at h1
    exact h1.elim hWh.2.1 hNh.2.1
  have hνae := quot_ae hq hGae hSae hS0
  set F := (good k r z).indicator (kern R z π v w ξ) with hF
  have hFm : Measurable F := kern_meas R hT hπ v w ξ (hcont w)
  have hFK : F =ᵐ[μG.prod (μW.prod μN)] kern R z π v w ξ := by
    filter_upwards [hQae] with q hq
    rw [hF, Set.indicator_of_mem hq]
  have hFi : Integrable F (μG.prod (μW.prod μN)) := by
    refine Integrable.mono' (hfub.norm.mul_const (‖ξ‖ * ‖ξ‖)) hFm.aestronglyMeasurable ?_
    filter_upwards [hQae] with q hq
    rw [hF, Set.indicator_of_mem hq, kern, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [norm_mul, psi_norm, one_mul]
    refine (norm_inner_le_norm _ _).trans ?_
    rw [piW_unitary hT hπ _ (uw_inv hq.2.1).1 ξ]
  set f : Formalism.QuantumDeterminants.Mt k r → ℂ := fun x => ∫ q, F (x, q) ∂(μW.prod μN) with hf
  have hfm : Measurable f := (hFm.stronglyMeasurable.integral_prod_right' (ν := μW.prod μN)).measurable
  have hfi : Integrable f μG := hFi.integral_prod_left
  obtain ⟨-, hgi, hge⟩ := GlobalTheory.T.weil_formula_integrable_complex k r μG (muSof μW μN) νq f hq hfm hfi

  have hg : ∀ᵐ x ∂νq, ∫ s, f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂(muSof μW μN) =
      ((‖be z Formalism.QuantumDeterminants.cStd π R.σ μW μN (R.σ (Matrix.of x) w) v ξ‖ ^ 2 : ℝ) : ℂ) := by
    filter_upwards [hνae] with x hx
    rw [hpt _ (hsm _ hx w hw) ξ, hSeq]
    have hm : Measurable (fun s : Formalism.QuantumDeterminants.Mt k r => f (mulMt s x)) :=
      hfm.comp (measurable_mulMt.comp (measurable_id.prodMk measurable_const))
    refine (integral_map measurable_mulMt.aemeasurable hm.aestronglyMeasurable).trans ?_
    apply integral_congr_ae
    filter_upwards [hPae] with p hp
    apply integral_congr_ae
    filter_upwards [hPae] with q hq'
    have hs : Matrix.of p.1 * Matrix.of p.2 ∈ GG k r := DDSmoothness.uh_mul hp.1.1 hp.2
    have ht : Matrix.of q.1 * Matrix.of q.2 ∈ GG k r := DDSmoothness.uh_mul hq'.1.1 hq'.2
    have hgood : (mulMt (mulMt p.1 p.2) x, q) ∈ good k r z := ⟨DDSmoothness.uh_mul hs hx, hq'.1, hq'.2⟩
    rw [hF, Set.indicator_of_mem hgood, ← hmul _ hs _ hx, ← hmul _ (DDSmoothness.uh_mul ht hs) _ hx,
      Matrix.mul_assoc (Matrix.of q.1 * Matrix.of q.2)]
    rfl

  have hI : ∫ x, f x ∂μG = ((‖w‖ ^ 2 : ℝ) : ℂ) / (d : ℂ) * ⟪be z Formalism.QuantumDeterminants.cStd π R.σ μW μN v v ξ, ξ⟫_ℂ := by
    have e1 : ∫ x, f x ∂μG = ∫ q, ∫ x, F (x, q) ∂μG ∂(μW.prod μN) :=
      integral_integral_swap (f := fun x q => F (x, q)) hFi
    have e2 : be z Formalism.QuantumDeterminants.cStd π R.σ μW μN v v ξ = ∫ p, beInt z Formalism.QuantumDeterminants.cStd π R.σ v v p ξ ∂(μW.prod μN) :=
      ContinuousLinearMap.integral_apply hconv ξ
    have e3 : ⟪be z Formalism.QuantumDeterminants.cStd π R.σ μW μN v v ξ, ξ⟫_ℂ =
        ∫ p, ⟪beInt z Formalism.QuantumDeterminants.cStd π R.σ v v p ξ, ξ⟫_ℂ ∂(μW.prod μN) := by
      rw [← inner_conj_symm, e2, ← integral_inner (hconv.apply_continuousLinearMap ξ), ← integral_conj]
      simp only [inner_conj_symm]
    rw [e1, e3, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hPae] with q hq'
    have ht : Matrix.of q.1 * Matrix.of q.2 ∈ GG k r := DDSmoothness.uh_mul hq'.1.1 hq'.2
    have e4 : ∀ᵐ x ∂μG, F (x, q) = ⟪v, R.σ (Matrix.of x) w⟫_ℂ *
        star ⟪R.σ (Matrix.of q.1 * Matrix.of q.2)⁻¹ v, R.σ (Matrix.of x) w⟫_ℂ *
        (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (Matrix.of q.2) * ⟪π (Matrix.of q.1)⁻¹ ξ, ξ⟫_ℂ) := by
      filter_upwards [hGae] with x hx
      have hgood : (x, q) ∈ good k r z := ⟨hx, hq'.1, hq'.2⟩
      rw [hF, Set.indicator_of_mem hgood, kern, hmul _ ht _ hx, sigma_inner hR.2 ht]
    rw [integral_congr_ae e4, integral_mul_const, hSd, ← inner_conj_symm v, ← sigma_inner hR.2 ht,
      inner_self_eq_norm_sq_to_K]
    simp only [beInt, ContinuousLinearMap.smul_apply, inner_smul_left, map_mul, RCLike.star_def,
      Complex.conj_conj]
    push_cast
    simp only [Complex.coe_algebraMap]
    ring
  have hgi' := hgi.congr hg
  refine ⟨hgi'.re.congr (Filter.Eventually.of_forall fun x => Complex.ofReal_re _), ?_⟩
  rw [← hI, hge, integral_congr_ae hg, integral_complex_ofReal]

/- English proof (translation)
Introduce `hy k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq hR hgap hok hS dd hdd v hv ξ`. Take `⟨-, -, -, -, hTK, -, hKT, ⟨w0, hw0, hw0K, -⟩, -⟩` from `GlobalTheory.rep_basic_of_isDS hy.1.2.2.1 k r ε mu R hR`. Take `⟨c, hc, hSch⟩` from `GlobalTheory.BesselDegree.schur_fdeg hy k r ε μG hS.2.2.2.2.2.2.1`. Take `⟨hdeg, hSd⟩` from `hSch mu R hR`. Establish `hw0ne : w0 ≠ 0` using `by intro h0; rw [h0, norm_zero] at hw0; exact zero_ne_one hw0`.

Establish `hd : c * Formalism.QuantumDeterminants.fdegHC mu = dd` using `by rw [← hdeg w0 hw0ne, hdd w0 hw0ne]`. Establish `hpos : 0 < dd` using `hd ▸ mul_pos hc (fdegHC_pos mu hR.1.1.injective)`. Rewrite `hSd` using `[hd]`. Establish `key` using `fun w hw => norm_integral hy k r ε mu h R Wp z π u μW μN μG νq hR hgap hok hS dd (fun a b a' b' => (hSd a b a' b').2) v hv ξ w hw`. Use `set β := ⟪ξ, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN v v ξ⟫_ℂ with hβ`.

Establish `hconj : ⟪be z Formalism.QuantumDeterminants.cStd π R.σ μW μN v v ξ, ξ⟫_ℂ = starRingEnd ℂ β`. Rewrite using `[hβ, inner_conj_symm]`. Establish `hre : ∀ w ∈ R.sm, ∫ x : Formalism.QuantumDeterminants.Mt k r, ‖be z Formalism.QuantumDeterminants.cStd π R.σ μW μN (R.σ (Matrix.of x) w) v ξ‖ ^ 2 ∂νq = ‖w‖ ^ 2 * β.re / dd`. Introduce `w hw`. Use `congrArg Complex.re (key w hw).2` as an intermediate fact.

Rewrite `this` using `[hconj, ← Complex.ofReal_div, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.conj_re]`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Establish `hw0s : w0 ∈ R.sm` using `hTK w0 (hKT w0 hw0K)`. Use `⟨?_, ?_, hpos, fun w hw => ?_⟩` and prove the remaining obligations.

Use `congrArg Complex.im (key w0 hw0s).2` as an intermediate fact. Rewrite `this` using `[hconj, ← Complex.ofReal_div, Complex.ofReal_im, Complex.im_ofReal_mul, Complex.conj_im, hw0]`. Establish `h1 : (1 : ℝ) ^ 2 / dd ≠ 0` using `by positivity`. Use `(mul_eq_zero.1 this.symm).resolve_left h1` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h1` using `hre w0 hw0s`. Establish `h2 : 0 ≤ ∫ x : Formalism.QuantumDeterminants.Mt k r, ‖be z Formalism.QuantumDeterminants.cStd π R.σ μW μN (R.σ (Matrix.of x) w0) v ξ‖ ^ 2 ∂νq` using `integral_nonneg fun x => by positivity`. Rewrite `h2` using `[h1, hw0, one_pow, one_mul]`. Assume the negation of the conclusion as `hneg`. Conclude with `absurd h2 (not_le.2 (div_neg_of_neg_of_pos (not_le.1 hneg) hpos))`.

Rewrite using `[← hre w hw, ofReal_integral_eq_lintegral_ofReal (key w hw).1 (Filter.Eventually.of_forall fun x => by positivity)]`. Unfold `PI.BesselPeriodGGP.l2SG`. Use `lintegral_congr fun x => ?_` and prove the remaining obligations. Rewrite using `[ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]`. Both sides reduce to the same expression.
-/
theorem norm_identity : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∀ dd : ℝ, (∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH μG R.σ w = dd) → ∀ v ∈ R.TK, ∀ ξ : Wp, (⟪ξ, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN v v ξ⟫_ℂ).im = 0 ∧ 0 ≤ (⟪ξ, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN v v ξ⟫_ℂ).re ∧ 0 < dd ∧ ∀ w ∈ R.sm, PI.BesselPeriodGGP.l2SG νq (fun g => be z Formalism.QuantumDeterminants.cStd π R.σ μW μN (R.σ g w) v ξ) = ENNReal.ofReal (‖w‖ ^ 2 * (⟪ξ, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN v v ξ⟫_ℂ).re / dd) := by
  intro hy k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq hR hgap hok hS dd hdd v hv ξ
  obtain ⟨-, -, -, -, hTK, -, hKT, ⟨w0, hw0, hw0K, -⟩, -⟩ := GlobalTheory.rep_basic_of_isDS hy.1.2.2.1 k r ε mu R hR
  obtain ⟨c, hc, hSch⟩ := GlobalTheory.BesselDegree.schur_fdeg hy k r ε μG hS.2.2.2.2.2.2.1
  obtain ⟨hdeg, hSd⟩ := hSch mu R hR
  have hw0ne : w0 ≠ 0 := by intro h0; rw [h0, norm_zero] at hw0; exact zero_ne_one hw0
  have hd : c * Formalism.QuantumDeterminants.fdegHC mu = dd := by rw [← hdeg w0 hw0ne, hdd w0 hw0ne]
  have hpos : 0 < dd := hd ▸ mul_pos hc (fdegHC_pos mu hR.1.1.injective)
  rw [hd] at hSd
  have key := fun w hw => norm_integral hy k r ε mu h R Wp z π u μW μN μG νq hR hgap hok hS dd
    (fun a b a' b' => (hSd a b a' b').2) v hv ξ w hw
  set β := ⟪ξ, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN v v ξ⟫_ℂ with hβ
  have hconj : ⟪be z Formalism.QuantumDeterminants.cStd π R.σ μW μN v v ξ, ξ⟫_ℂ = starRingEnd ℂ β := by
    rw [hβ, inner_conj_symm]
  have hre : ∀ w ∈ R.sm,
      ∫ x : Formalism.QuantumDeterminants.Mt k r, ‖be z Formalism.QuantumDeterminants.cStd π R.σ μW μN (R.σ (Matrix.of x) w) v ξ‖ ^ 2 ∂νq =
        ‖w‖ ^ 2 * β.re / dd := by
    intro w hw
    have := congrArg Complex.re (key w hw).2
    rw [hconj, ← Complex.ofReal_div, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.conj_re] at this
    rw [this]; ring
  have hw0s : w0 ∈ R.sm := hTK w0 (hKT w0 hw0K)
  refine ⟨?_, ?_, hpos, fun w hw => ?_⟩
  · have := congrArg Complex.im (key w0 hw0s).2
    rw [hconj, ← Complex.ofReal_div, Complex.ofReal_im, Complex.im_ofReal_mul, Complex.conj_im, hw0] at this
    have h1 : (1 : ℝ) ^ 2 / dd ≠ 0 := by positivity
    have := (mul_eq_zero.1 this.symm).resolve_left h1
    linarith
  · have h1 := hre w0 hw0s
    have h2 : 0 ≤ ∫ x : Formalism.QuantumDeterminants.Mt k r,
        ‖be z Formalism.QuantumDeterminants.cStd π R.σ μW μN (R.σ (Matrix.of x) w0) v ξ‖ ^ 2 ∂νq :=
      integral_nonneg fun x => by positivity
    rw [h1, hw0, one_pow, one_mul] at h2
    by_contra hneg
    exact absurd h2 (not_le.2 (div_neg_of_neg_of_pos (not_le.1 hneg) hpos))
  · rw [← hre w hw, ofReal_integral_eq_lintegral_ofReal (key w hw).1
      (Filter.Eventually.of_forall fun x => by positivity)]
    unfold PI.BesselPeriodGGP.l2SG
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
    rfl

end GlobalTheory.BesselNorm
