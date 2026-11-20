import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselIntegrability.IntegrableGNRpowOfLintegralLtTop
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.DecayZeroRight.NormDec
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.UnitNorm.UnrealifyRealify

open MeasureTheory Matrix
open scoped ENNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.QuantumDeterminants

variable {k r : ℕ}

def haarCompactGrowthDensity (A : ℝ) (y : Mt k r) : ℝ≥0∞ := ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (Matrix.of y) ^ (-A))

/- English proof (translation)
Unfold `Formalism.FourierDecayAlt.B.gN`. Simplify using `only [Matrix.of_apply]`. Use `Real.continuous_sqrt.comp ?_` and prove the remaining obligations. Use `continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_` and prove the remaining obligations. Conclude with `Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i))`.
-/
theorem s3dx1S_gNc : Continuous (fun y : Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of y)) := by
  unfold Formalism.FourierDecayAlt.B.gN
  simp only [Matrix.of_apply]
  refine Real.continuous_sqrt.comp ?_
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  exact Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i))

/- English proof (translation)
Unfold `haarCompactGrowthDensity`. Conclude with `ENNReal.measurable_ofReal.comp ((s3dx1S_gNc (k := k) (r := r)).measurable.pow_const (-A))`.
-/
theorem s3dx1S_Fm (A : ℝ) : Measurable (haarCompactGrowthDensity (k := k) (r := r) A) := by
  unfold haarCompactGrowthDensity
  exact ENNReal.measurable_ofReal.comp ((s3dx1S_gNc (k := k) (r := r)).measurable.pow_const (-A))

/- English proof (translation)
Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Simplify using `only [Matrix.mul_apply, Matrix.of_apply]`. Conclude with `continuous_finset_sum _ fun l _ => by fun_prop`.
-/
theorem s3dx1S_mulc :
    Continuous (fun p : Mt k r × Mt k r => (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Mt k r)) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  exact continuous_finset_sum _ fun l _ => by fun_prop

/- English proof (translation)
Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Simplify using `only [Matrix.mul_apply, Matrix.of_apply]`. Conclude with `continuous_finset_sum _ fun l _ => by fun_prop`.
-/
theorem s3dx1S_mulxc (x : Mt k r) :
    Continuous (fun s : Mt k r => (fun i j => (Matrix.of s * Matrix.of x) i j : Mt k r)) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  exact continuous_finset_sum _ fun l _ => by fun_prop

/- English proof (translation)
Rewrite using `[← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]`. Use `lintegral_mono_ae (hae.mono fun p hp => ?_)` and prove the remaining obligations. Establish `hs : Matrix.of p.1 * Matrix.of p.2 ∈ UH (Hpk k r)` using `PI.WUN.UH_mul hp.1.1 hp.2.1`. Establish `hsx : Matrix.of p.1 * Matrix.of p.2 * Matrix.of x ∈ UH (Hpk k r)` using `PI.WUN.UH_mul hs hx`. Establish `h1` using `((Formalism.MainNotions.InverseNormDecayBounds.normInvP k r).1 _ hsx).2`.

Establish `hsub` using `(Formalism.MainNotions.InverseNormDecayBounds.normInvP k r).2 (Matrix.of p.1 * Matrix.of p.2) (Matrix.of x)`. Establish `hs0` using `gN_nonneg_bessel_integrability (Matrix.of p.1 * Matrix.of p.2)`. Establish `hle : Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x) ≤ Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) * Rr` using `hsub.trans (mul_le_mul_of_nonneg_left hxR hs0)`. Establish `hmono` using `Real.rpow_le_rpow_of_nonpos (by linarith) hle (by linarith : -A ≤ 0)`. Rewrite `hmono` using `[Real.mul_rpow hs0 hR.le]`.

Rewrite using `[← ENNReal.ofReal_mul (Real.rpow_nonneg hR.le _)]`. Conclude with `ENNReal.ofReal_le_ofReal (by rw [mul_comm]; exact hmono)`.
-/
theorem s3dx1S_lower {z : Fin (2 * r + k + 1) → ℂ} {μW μN : Measure (Mt k r)} {A Rr : ℝ} (hA : 0 ≤ A)
    (hR : 0 < Rr) (hae : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r)
    {x : Mt k r} (hx : Matrix.of x ∈ UH (Hpk k r)) (hxR : Formalism.FourierDecayAlt.B.gN (Matrix.of x) ≤ Rr) :
    ENNReal.ofReal (Rr ^ (-A)) *
        ∫⁻ p, ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-A)) ∂(μW.prod μN) ≤
      ∫⁻ p, ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x) ^ (-A))
        ∂(μW.prod μN) := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae (hae.mono fun p hp => ?_)
  have hs : Matrix.of p.1 * Matrix.of p.2 ∈ UH (Hpk k r) := PI.WUN.UH_mul hp.1.1 hp.2.1
  have hsx : Matrix.of p.1 * Matrix.of p.2 * Matrix.of x ∈ UH (Hpk k r) := PI.WUN.UH_mul hs hx
  have h1 := ((Formalism.MainNotions.InverseNormDecayBounds.normInvP k r).1 _ hsx).2
  have hsub := (Formalism.MainNotions.InverseNormDecayBounds.normInvP k r).2 (Matrix.of p.1 * Matrix.of p.2) (Matrix.of x)
  have hs0 := gN_nonneg_bessel_integrability (Matrix.of p.1 * Matrix.of p.2)
  have hle : Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x) ≤
      Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) * Rr :=
    hsub.trans (mul_le_mul_of_nonneg_left hxR hs0)
  have hmono := Real.rpow_le_rpow_of_nonpos (by linarith) hle (by linarith : -A ≤ 0)
  rw [Real.mul_rpow hs0 hR.le] at hmono
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hR.le _)]
  exact ENNReal.ofReal_le_ofReal (by rw [mul_comm]; exact hmono)

/- English proof (translation)
Establish `hGsm : MeasurableSet {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)}` using `((PI.WUN.isClosed_UH k r).preimage PI.WUN.continuous_of).measurableSet`. Establish `hSnull : Formalism.FourierDecayAlt.ThreeDimData.muSof μW μN {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)}ᶜ = 0`. Unfold `Formalism.FourierDecayAlt.ThreeDimData.muSof`. Rewrite using `[Measure.map_apply s3dx1S_mulc.measurable hGsm.compl]`. Conclude with `ae_iff.1 (hae.mono fun p hp => PI.WUN.UH_mul hp.1.1 hp.2.1)`.

Introduce `h0`. Establish `hnot : ∀ᵐ x ∂νq, x ∉ {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)}`. Rewrite using `[ae_iff]`. Simplify using `only [not_not]`. Conclude with `h0`.

Establish `hin : ∀ x ∉ {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)}, (∫⁻ s, {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)}.indicator 1 (fun i j => (Matrix.of s * Matrix.of x) i j) ∂(Formalism.FourierDecayAlt.ThreeDimData.muSof μW μN)) = 0`. Introduce `x hx`. Use `le_antisymm ?_ (zero_le)` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `lintegral_mono fun s => ?_` and prove the remaining obligations.

Distinguish the cases in `hs : s ∈ {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)}`. Establish `hsx : (fun i j => (Matrix.of s * Matrix.of x) i j : Mt k r) ∉ {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)}`. Introduce `hsx`. Apply `hx` to reduce the goal to its premises. Establish `hs' : Matrix.of s ∈ UH (Hpk k r)` using `hs`.

Establish `hsx' : Matrix.of s * Matrix.of x ∈ UH (Hpk k r)` using `hsx`. Establish `hu : IsUnit (Matrix.of s).det` using `PI.WUN.UH_det hs'`. Establish `e : Matrix.of x = (Matrix.of s)⁻¹ * (Matrix.of s * Matrix.of x)`. Rewrite using `[← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]`. Use `show Matrix.of x ∈ UH (Hpk k r)`.

Rewrite using `[e]`. Conclude with `PI.WUN.UH_mul (PI.WUN.UH_inv hs') hsx'`. Rewrite using `[Set.indicator_of_notMem hsx]`. Conclude with `zero_le`. Rewrite using `[Set.indicator_of_mem (show s ∈ {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)}ᶜ from hs)]`.

Conclude with `Set.indicator_apply_le' (fun _ => le_rfl) (fun _ => zero_le)`. Use `_ = Formalism.FourierDecayAlt.ThreeDimData.muSof μW μN {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)}ᶜ := lintegral_indicator_one hGsm.compl`. Use `_ = 0 := hSnull`. Establish `hI` using `hq ({x : Mt k r | Matrix.of x ∈ UH (Hpk k r)}.indicator 1) (measurable_one.indicator hGsm)`. Rewrite `hI` using `[lintegral_indicator_one hGsm, lintegral_congr_ae (hnot.mono fun x hx => hin x hx), lintegral_zero]`.

Establish `hc : μG {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)}ᶜ = 0` using `hG.2.2.1`. Establish `hu` using `measure_univ_le_add_compl (μ := μG) {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)}`. Rewrite `hu` using `[hI, hc, add_zero, nonpos_iff_eq_zero, Measure.measure_univ_eq_zero]`. Conclude with `hG.2.1 hu`.
-/
theorem s3dx1S_quot_pos {z : Fin (2 * r + k + 1) → ℂ} {μW μN μG νq : Measure (Mt k r)}
    (hG : PI.BesselPeriodGGP.IsHaarOn (UH (Hpk k r)) μG)
    (hq : PI.BesselPeriodGGP.IsQuotMeas μG (Formalism.FourierDecayAlt.ThreeDimData.muSof μW μN) νq)
    (hae : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r) :
    νq {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)} ≠ 0 := by
  have hGsm : MeasurableSet {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)} :=
    ((PI.WUN.isClosed_UH k r).preimage PI.WUN.continuous_of).measurableSet
  have hSnull : Formalism.FourierDecayAlt.ThreeDimData.muSof μW μN {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)}ᶜ = 0 := by
    unfold Formalism.FourierDecayAlt.ThreeDimData.muSof
    rw [Measure.map_apply s3dx1S_mulc.measurable hGsm.compl]
    exact ae_iff.1 (hae.mono fun p hp => PI.WUN.UH_mul hp.1.1 hp.2.1)
  intro h0
  have hnot : ∀ᵐ x ∂νq, x ∉ {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)} := by
    rw [ae_iff]
    simp only [not_not]
    exact h0
  have hin : ∀ x ∉ {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)},
      (∫⁻ s, {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)}.indicator 1
        (fun i j => (Matrix.of s * Matrix.of x) i j) ∂(Formalism.FourierDecayAlt.ThreeDimData.muSof μW μN)) = 0 := by
    intro x hx
    refine le_antisymm ?_ (zero_le)
    calc _ ≤ ∫⁻ s, {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)}ᶜ.indicator 1 s ∂(Formalism.FourierDecayAlt.ThreeDimData.muSof μW μN) := by
          refine lintegral_mono fun s => ?_
          by_cases hs : s ∈ {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)}
          · have hsx : (fun i j => (Matrix.of s * Matrix.of x) i j : Mt k r) ∉
                {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)} := by
              intro hsx
              apply hx
              have hs' : Matrix.of s ∈ UH (Hpk k r) := hs
              have hsx' : Matrix.of s * Matrix.of x ∈ UH (Hpk k r) := hsx
              have hu : IsUnit (Matrix.of s).det := PI.WUN.UH_det hs'
              have e : Matrix.of x = (Matrix.of s)⁻¹ * (Matrix.of s * Matrix.of x) := by
                rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
              show Matrix.of x ∈ UH (Hpk k r)
              rw [e]
              exact PI.WUN.UH_mul (PI.WUN.UH_inv hs') hsx'
            rw [Set.indicator_of_notMem hsx]
            exact zero_le
          · rw [Set.indicator_of_mem (show s ∈ {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)}ᶜ from hs)]
            exact Set.indicator_apply_le' (fun _ => le_rfl) (fun _ => zero_le)
      _ = Formalism.FourierDecayAlt.ThreeDimData.muSof μW μN {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)}ᶜ :=
          lintegral_indicator_one hGsm.compl
      _ = 0 := hSnull
  have hI := hq ({x : Mt k r | Matrix.of x ∈ UH (Hpk k r)}.indicator 1) (measurable_one.indicator hGsm)
  rw [lintegral_indicator_one hGsm, lintegral_congr_ae (hnot.mono fun x hx => hin x hx), lintegral_zero] at hI
  have hc : μG {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)}ᶜ = 0 := hG.2.2.1
  have hu := measure_univ_le_add_compl (μ := μG) {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)}
  rw [hI, hc, add_zero, nonpos_iff_eq_zero, Measure.measure_univ_eq_zero] at hu
  exact hG.2.1 hu

/- English proof (translation)
Introduce `k r z μW μN μG νq A hz hT hW hN hG hq hA`. Establish `hA0 : 0 < A` using `lt_of_le_of_lt (by unfold Formalism.FourierDecayAlt.ThreeDimData.AG; positivity) hA`. Establish `: SigmaFinite μW` using `hW.1`. Establish `: SigmaFinite μN` using `hN.1`. Establish `hae : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r`.

Establish `h1 : ∀ᵐ x ∂μW, Matrix.of x ∈ UWset k r z` using `by rw [ae_iff]; exact hW.2.2.1`. Establish `h2 : ∀ᵐ x ∂μN, Matrix.of x ∈ Nset k r` using `by rw [ae_iff]; exact hN.2.2.1`. Conclude with `(Measure.quasiMeasurePreserving_fst.ae h1).and (Measure.quasiMeasurePreserving_snd.ae h2)`. Establish `hqG` using `s3dx1S_quot_pos hG hq hae`. Choose the witnesses or unpack the hypotheses as in `⟨n, hn⟩ : ∃ n : ℕ, νq {x : Mt k r | Matrix.of x ∈ UH (Hpk k r) ∧ Formalism.FourierDecayAlt.B.gN (Matrix.of x) ≤ (n : ℝ) + 1} ≠ 0 := by`.

Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Apply `hqG` to reduce the goal to its premises. Establish `hU : {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)} = ⋃ n : ℕ, {x : Mt k r | Matrix.of x ∈ UH (Hpk k r) ∧ Formalism.FourierDecayAlt.B.gN (Matrix.of x) ≤ (n : ℝ) + 1}`. Use extensionality with `x`.

Simplify using `only [Set.mem_iUnion, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Take `⟨n, hn⟩` from `exists_nat_ge (Formalism.FourierDecayAlt.B.gN (Matrix.of x))`. Conclude with `⟨n, hx, by linarith⟩`.

Introduce and unpack `⟨n, hx, -⟩`. Conclude with `hx`. Rewrite using `[hU]`. Conclude with `measure_iUnion_null hcon`. Establish `hR0 : (0 : ℝ) < (n : ℝ) + 1` using `by positivity`.

Establish `hEm : MeasurableSet {x : Mt k r | Matrix.of x ∈ UH (Hpk k r) ∧ Formalism.FourierDecayAlt.B.gN (Matrix.of x) ≤ (n : ℝ) + 1}` using `(((PI.WUN.isClosed_UH k r).preimage PI.WUN.continuous_of).measurableSet).inter (measurableSet_le (s3dx1S_gNc (k := k) (r := r)).measurable measurable_const)`. Establish `hlow : ∀ x : Mt k r, {x : Mt k r | Matrix.of x ∈ UH (Hpk k r) ∧ Formalism.FourierDecayAlt.B.gN (Matrix.of x) ≤ (n : ℝ) + 1}.indicator (fun _ => ENNReal.ofReal (((n : ℝ) + 1) ^ (-A)) * ∫⁻ p, ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-A)) ∂(μ …`. Introduce `x`. Distinguish the cases in `hx : x ∈ {x : Mt k r | Matrix.of x ∈ UH (Hpk k r) ∧ Formalism.FourierDecayAlt.B.gN (Matrix.of x) ≤ (n : ℝ) + 1}`. Rewrite using `[Set.indicator_of_mem hx]`.

Establish `hf : Measurable (fun s : Mt k r => haarCompactGrowthDensity A (fun i j => (Matrix.of s * Matrix.of x) i j : Mt k r))` using `(s3dx1S_Fm A).comp (s3dx1S_mulxc x).measurable`. Unfold `Formalism.FourierDecayAlt.ThreeDimData.muSof`. Rewrite using `[lintegral_map hf s3dx1S_mulc.measurable]`. Conclude with `s3dx1S_lower hA0.le hR0 hae hx.1 hx.2`. Rewrite using `[Set.indicator_of_notMem hx]`.

Conclude with `zero_le`. Establish `hGint` using `Formalism.FourierDecayAlt.P.growth_group_bound k r μG A hG hA`. Establish `hT : ∫⁻ x, haarCompactGrowthDensity A x ∂μG < ⊤` using `(hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (gN_nonneg_bessel_integrability _) _)).1 hGint.2`. Establish `hchain : ENNReal.ofReal (((n : ℝ) + 1) ^ (-A)) * (∫⁻ p, ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-A)) ∂(μW.prod μN)) * νq {x : Mt k r | Matrix.of x ∈ UH (Hpk k r) ∧ Formalism.FourierDecayAlt.B.gN (Matrix.of x) ≤ (n : ℝ) + 1} ≤ ∫⁻ x, haarCo …`. Rewrite using `[hq (haarCompactGrowthDensity A) (s3dx1S_Fm A), ← lintegral_indicator_const hEm]`.

Conclude with `lintegral_mono hlow`. Establish `hc0 : ENNReal.ofReal (((n : ℝ) + 1) ^ (-A)) ≠ 0` using `(ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hR0 _)).ne'`. Establish `hI : (∫⁻ p, ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-A)) ∂(μW.prod μN)) < ⊤`. Assume the negation of the conclusion as `hc`. Rewrite `hc` using `[not_lt, top_le_iff]`.

Establish `hlt` using `hchain.trans_lt hT`. Rewrite `hlt` using `[hc, ENNReal.mul_top hc0, ENNReal.top_mul hn]`. Conclude with `lt_irrefl _ hlt`. Use `⟨((s3dx1S_gNc.comp s3dx1S_mulc).measurable.pow_const (-A)).aestronglyMeasurable, ?_⟩` and prove the remaining obligations. Rewrite using `[hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun p => Real.rpow_nonneg (gN_nonneg_bessel_integrability _) _)]`.

Conclude with `hI`.
-/
theorem growth_spherical_bound : Formalism.FourierDecayAlt.ThreeDimData.GrowthS := by
  intro k r z μW μN μG νq A hz hT hW hN hG hq hA
  have hA0 : 0 < A := lt_of_le_of_lt (by unfold Formalism.FourierDecayAlt.ThreeDimData.AG; positivity) hA
  have : SigmaFinite μW := hW.1
  have : SigmaFinite μN := hN.1
  have hae : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r := by
    have h1 : ∀ᵐ x ∂μW, Matrix.of x ∈ UWset k r z := by rw [ae_iff]; exact hW.2.2.1
    have h2 : ∀ᵐ x ∂μN, Matrix.of x ∈ Nset k r := by rw [ae_iff]; exact hN.2.2.1
    exact (Measure.quasiMeasurePreserving_fst.ae h1).and (Measure.quasiMeasurePreserving_snd.ae h2)
  have hqG := s3dx1S_quot_pos hG hq hae
  obtain ⟨n, hn⟩ : ∃ n : ℕ,
      νq {x : Mt k r | Matrix.of x ∈ UH (Hpk k r) ∧ Formalism.FourierDecayAlt.B.gN (Matrix.of x) ≤ (n : ℝ) + 1} ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hqG
    have hU : {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)} =
        ⋃ n : ℕ, {x : Mt k r | Matrix.of x ∈ UH (Hpk k r) ∧ Formalism.FourierDecayAlt.B.gN (Matrix.of x) ≤ (n : ℝ) + 1} := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      constructor
      · intro hx
        obtain ⟨n, hn⟩ := exists_nat_ge (Formalism.FourierDecayAlt.B.gN (Matrix.of x))
        exact ⟨n, hx, by linarith⟩
      · rintro ⟨n, hx, -⟩
        exact hx
    rw [hU]
    exact measure_iUnion_null hcon
  have hR0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hEm : MeasurableSet
      {x : Mt k r | Matrix.of x ∈ UH (Hpk k r) ∧ Formalism.FourierDecayAlt.B.gN (Matrix.of x) ≤ (n : ℝ) + 1} :=
    (((PI.WUN.isClosed_UH k r).preimage PI.WUN.continuous_of).measurableSet).inter
      (measurableSet_le (s3dx1S_gNc (k := k) (r := r)).measurable measurable_const)
  have hlow : ∀ x : Mt k r,
      {x : Mt k r | Matrix.of x ∈ UH (Hpk k r) ∧ Formalism.FourierDecayAlt.B.gN (Matrix.of x) ≤ (n : ℝ) + 1}.indicator
        (fun _ => ENNReal.ofReal (((n : ℝ) + 1) ^ (-A)) *
          ∫⁻ p, ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-A)) ∂(μW.prod μN)) x ≤
        ∫⁻ s, haarCompactGrowthDensity A (fun i j => (Matrix.of s * Matrix.of x) i j) ∂(Formalism.FourierDecayAlt.ThreeDimData.muSof μW μN) := by
    intro x
    by_cases hx : x ∈ {x : Mt k r | Matrix.of x ∈ UH (Hpk k r) ∧ Formalism.FourierDecayAlt.B.gN (Matrix.of x) ≤ (n : ℝ) + 1}
    · rw [Set.indicator_of_mem hx]
      have hf : Measurable (fun s : Mt k r => haarCompactGrowthDensity A (fun i j => (Matrix.of s * Matrix.of x) i j : Mt k r)) :=
        (s3dx1S_Fm A).comp (s3dx1S_mulxc x).measurable
      unfold Formalism.FourierDecayAlt.ThreeDimData.muSof
      rw [lintegral_map hf s3dx1S_mulc.measurable]
      exact s3dx1S_lower hA0.le hR0 hae hx.1 hx.2
    · rw [Set.indicator_of_notMem hx]
      exact zero_le
  have hGint := Formalism.FourierDecayAlt.P.growth_group_bound k r μG A hG hA
  have hT : ∫⁻ x, haarCompactGrowthDensity A x ∂μG < ⊤ :=
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x =>
      Real.rpow_nonneg (gN_nonneg_bessel_integrability _) _)).1 hGint.2
  have hchain : ENNReal.ofReal (((n : ℝ) + 1) ^ (-A)) *
      (∫⁻ p, ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-A)) ∂(μW.prod μN)) *
      νq {x : Mt k r | Matrix.of x ∈ UH (Hpk k r) ∧ Formalism.FourierDecayAlt.B.gN (Matrix.of x) ≤ (n : ℝ) + 1} ≤
      ∫⁻ x, haarCompactGrowthDensity A x ∂μG := by
    rw [hq (haarCompactGrowthDensity A) (s3dx1S_Fm A), ← lintegral_indicator_const hEm]
    exact lintegral_mono hlow
  have hc0 : ENNReal.ofReal (((n : ℝ) + 1) ^ (-A)) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hR0 _)).ne'
  have hI : (∫⁻ p, ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-A)) ∂(μW.prod μN)) < ⊤ := by
    by_contra hc
    rw [not_lt, top_le_iff] at hc
    have hlt := hchain.trans_lt hT
    rw [hc, ENNReal.mul_top hc0, ENNReal.top_mul hn] at hlt
    exact lt_irrefl _ hlt
  refine ⟨((s3dx1S_gNc.comp s3dx1S_mulc).measurable.pow_const (-A)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun p => Real.rpow_nonneg (gN_nonneg_bessel_integrability _) _)]
  exact hI

end Formalism.FourierDecayAlt.P
