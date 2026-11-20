import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPtRepTrDat
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
import Formalism.SharpRestriction.CuspSpanNormBounds.SBridge
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPlacesEqTrace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.JEqOrbInt
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CellConv
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UniformBesselConstant
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellHermitian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingConstruction
import Formalism.FormalDegreeBessel.FormalDegreeRatio.BFCell
import Formalism.FormalDegreeBessel.FinalBF
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

noncomputable section

namespace GlobalTheory.CellMajTransfer

open Formalism.FourierDecayAlt in

/- English proof (translation)
Take `⟨h1, h2, h3, h4⟩` from `hp`. Use `set X : B.Mat k r := (Matrix.of p.1.1 : B.Mat k r)⁻¹ * (Matrix.of p.1.2 : B.Mat k r)⁻¹ * (γ₁ * a) * Matrix.of p.2.2 * Matrix.of p.2.1 with hX`. Use `set Y : B.Mat k r := (Matrix.of p.1.1 : B.Mat k r)⁻¹ * (Matrix.of p.1.2 : B.Mat k r)⁻¹ * γ₁ * (a * Matrix.of p.2.2 * a⁻¹) * Matrix.of h'' with hY`. Establish `hXv : pairMaj (γ₁ * a) b p = B.gN X ^ (-b)` using `rfl`. Establish `hYv : pairMaj γ₁ b (p.1, (h'', conjM a p.2.2)) = B.gN Y ^ (-b)` using `rfl`.

Rewrite using `[hXv, hYv]`. Establish `hh'u : IsUnit (Matrix.of p.2.1 : B.Mat k r).det` using `(P.unitary_group_closed k r).unit _ h3.1`. Establish `eY : Y = X * ((Matrix.of p.2.1 : B.Mat k r)⁻¹ * a⁻¹ * Matrix.of h'')`. Simplify using `only [hX, hY, Matrix.mul_assoc]`. Rewrite using `[Matrix.mul_nonsing_inv_cancel_left _ _ hh'u]`.

Establish `hai : a⁻¹ ∈ UH (Hpk k r)` using `Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv ha`. Establish `hA1 : 1 ≤ B.gN a⁻¹` using `P.BetaSesquilinearity.gN_ge_one hai`. Establish `hYG : Y ∈ B.GV k r`. Rewrite using `[hY]`. Conclude with `Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv h1.1) (Formalism …`.

Establish `hY1 : 1 ≤ B.gN Y` using `P.BetaSesquilinearity.gN_ge_one hYG`. Establish `hX0 : 0 ≤ B.gN X` using `P.B6.gN_nonneg X`. Establish `hle : B.gN Y ≤ (K * K * B.gN a⁻¹) * B.gN X`. Rewrite using `[eY]`. Establish `e1` using `P.B6.gN_mul_le X ((Matrix.of p.2.1 : B.Mat k r)⁻¹ * a⁻¹ * Matrix.of h'')`.

Establish `e2` using `P.B6.gN_mul_le ((Matrix.of p.2.1 : B.Mat k r)⁻¹ * a⁻¹) (Matrix.of h'')`. Establish `e3` using `P.B6.gN_mul_le ((Matrix.of p.2.1 : B.Mat k r)⁻¹) a⁻¹`. Establish `k1` using `hK _ (Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv h3)`. Establish `k2` using `hK _ hh`. Establish `n1` using `P.B6.gN_nonneg ((Matrix.of p.2.1 : B.Mat k r)⁻¹)`.

Establish `n2` using `P.B6.gN_nonneg (a⁻¹)`. Establish `n3` using `P.B6.gN_nonneg (Matrix.of h'' : B.Mat k r)`. Establish `n4` using `P.B6.gN_nonneg ((Matrix.of p.2.1 : B.Mat k r)⁻¹ * a⁻¹)`. Establish `n5` using `P.B6.gN_nonneg ((Matrix.of p.2.1 : B.Mat k r)⁻¹ * a⁻¹ * Matrix.of h'')`. Establish `s1 : B.gN ((Matrix.of p.2.1 : B.Mat k r)⁻¹ * a⁻¹ * Matrix.of h'') ≤ K * K * B.gN a⁻¹`.

Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Use `set c : ℝ := K * K * B.gN a⁻¹ with hc`. Establish `hc1 : 1 ≤ c` using `by rw [hc]; nlinarith`. Establish `hc0 : 0 < c` using `by linarith`.

Establish `hcb : c ^ b * c ^ (-b) = 1`. Rewrite using `[← Real.rpow_add hc0, add_neg_cancel, Real.rpow_zero]`. Establish `hmono : (c * B.gN X) ^ (-b) ≤ B.gN Y ^ (-b)` using `Real.rpow_le_rpow_of_nonpos (by linarith) hle (by linarith)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.mul_rpow hc0.le hX0, ← mul_assoc, hcb, one_mul]`.

Use `_ ≤ c ^ b * B.gN Y ^ (-b) := mul_le_mul_of_nonneg_left hmono (Real.rpow_nonneg hc0.le _)`.
-/
theorem pt_bound {k r : ℕ} (L : LocBessel k r) {γ₁ a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hγ : γ₁ ∈ UH (Hpk k r)) (ha : a ∈ UH (Hpk k r)) {b : ℝ} (hb : 0 ≤ b) {K : ℝ} (hK1 : 1 ≤ K)
    (hK : ∀ h ∈ UWset k r L.z', B.gN h ≤ K)
    {p : PairSp k r} (hp : p ∈ GlobalTheory.CellOrbInt.pairSet L) {h'' : Mt k r} (hh : Matrix.of h'' ∈ UWset k r L.z') :
    pairMaj (γ₁ * a) b p ≤ (K * K * B.gN a⁻¹) ^ b * pairMaj γ₁ b (p.1, (h'', conjM a p.2.2)) := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  set X : B.Mat k r := (Matrix.of p.1.1 : B.Mat k r)⁻¹ * (Matrix.of p.1.2 : B.Mat k r)⁻¹ * (γ₁ * a) *
    Matrix.of p.2.2 * Matrix.of p.2.1 with hX
  set Y : B.Mat k r := (Matrix.of p.1.1 : B.Mat k r)⁻¹ * (Matrix.of p.1.2 : B.Mat k r)⁻¹ * γ₁ *
    (a * Matrix.of p.2.2 * a⁻¹) * Matrix.of h'' with hY
  have hXv : pairMaj (γ₁ * a) b p = B.gN X ^ (-b) := rfl
  have hYv : pairMaj γ₁ b (p.1, (h'', conjM a p.2.2)) = B.gN Y ^ (-b) := rfl
  rw [hXv, hYv]
  have hh'u : IsUnit (Matrix.of p.2.1 : B.Mat k r).det := (P.unitary_group_closed k r).unit _ h3.1
  have eY : Y = X * ((Matrix.of p.2.1 : B.Mat k r)⁻¹ * a⁻¹ * Matrix.of h'') := by
    simp only [hX, hY, Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hh'u]
  have hai : a⁻¹ ∈ UH (Hpk k r) := Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv ha
  have hA1 : 1 ≤ B.gN a⁻¹ := P.BetaSesquilinearity.gN_ge_one hai
  have hYG : Y ∈ B.GV k r := by
    rw [hY]
    exact Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul
      (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv h1.1) (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv h2.1)) hγ)
      (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul ha h4.1) hai)) hh.1
  have hY1 : 1 ≤ B.gN Y := P.BetaSesquilinearity.gN_ge_one hYG
  have hX0 : 0 ≤ B.gN X := P.B6.gN_nonneg X
  have hle : B.gN Y ≤ (K * K * B.gN a⁻¹) * B.gN X := by
    rw [eY]
    have e1 := P.B6.gN_mul_le X ((Matrix.of p.2.1 : B.Mat k r)⁻¹ * a⁻¹ * Matrix.of h'')
    have e2 := P.B6.gN_mul_le ((Matrix.of p.2.1 : B.Mat k r)⁻¹ * a⁻¹) (Matrix.of h'')
    have e3 := P.B6.gN_mul_le ((Matrix.of p.2.1 : B.Mat k r)⁻¹) a⁻¹
    have k1 := hK _ (Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv h3)
    have k2 := hK _ hh
    have n1 := P.B6.gN_nonneg ((Matrix.of p.2.1 : B.Mat k r)⁻¹)
    have n2 := P.B6.gN_nonneg (a⁻¹)
    have n3 := P.B6.gN_nonneg (Matrix.of h'' : B.Mat k r)
    have n4 := P.B6.gN_nonneg ((Matrix.of p.2.1 : B.Mat k r)⁻¹ * a⁻¹)
    have n5 := P.B6.gN_nonneg ((Matrix.of p.2.1 : B.Mat k r)⁻¹ * a⁻¹ * Matrix.of h'')
    have s1 : B.gN ((Matrix.of p.2.1 : B.Mat k r)⁻¹ * a⁻¹ * Matrix.of h'') ≤ K * K * B.gN a⁻¹ := by
      calc _ ≤ B.gN ((Matrix.of p.2.1 : B.Mat k r)⁻¹ * a⁻¹) * B.gN (Matrix.of h'' : B.Mat k r) := e2
        _ ≤ (B.gN ((Matrix.of p.2.1 : B.Mat k r)⁻¹) * B.gN a⁻¹) * K :=
            mul_le_mul e3 k2 n3 (mul_nonneg n1 n2)
        _ ≤ (K * B.gN a⁻¹) * K := by gcongr
        _ = K * K * B.gN a⁻¹ := by ring
    calc _ ≤ B.gN X * B.gN ((Matrix.of p.2.1 : B.Mat k r)⁻¹ * a⁻¹ * Matrix.of h'') := e1
      _ ≤ B.gN X * (K * K * B.gN a⁻¹) := mul_le_mul_of_nonneg_left s1 hX0
      _ = (K * K * B.gN a⁻¹) * B.gN X := by ring
  set c : ℝ := K * K * B.gN a⁻¹ with hc
  have hc1 : 1 ≤ c := by rw [hc]; nlinarith
  have hc0 : 0 < c := by linarith
  have hcb : c ^ b * c ^ (-b) = 1 := by
    rw [← Real.rpow_add hc0, add_neg_cancel, Real.rpow_zero]
  have hmono : (c * B.gN X) ^ (-b) ≤ B.gN Y ^ (-b) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) hle (by linarith)
  calc B.gN X ^ (-b) = c ^ b * (c * B.gN X) ^ (-b) := by
        rw [Real.mul_rpow hc0.le hX0, ← mul_assoc, hcb, one_mul]
    _ ≤ c ^ b * B.gN Y ^ (-b) := mul_le_mul_of_nonneg_left hmono (Real.rpow_nonneg hc0.le _)

end GlobalTheory.CellMajTransfer

namespace GlobalTheory.CellMajTransfer

open Formalism.FourierDecayAlt in

/- English proof (translation)
Establish `: SFinite L.μN` using `by unfold LocBessel.μN haarLie; infer_instance`. Establish `: SigmaFinite L.μW'` using `L.hμW'.1.1`. Establish `hconj : Measurable (conjM (k` using `k) (r := r) a) := by`. Establish `: Continuous (conjM (k` using `k) (r := r) a) := by`. Unfold `conjM`.

Conclude with `(continuous_const.matrix_mul continuous_id).matrix_mul continuous_const`. Conclude with `this.measurable`. Establish `hF : Measurable fun q : Mt k r × (Mt k r × Mt k r) => f (x, (q.1, conjM a q.2.2))` using `hfm.comp (measurable_const.prodMk (measurable_fst.prodMk (hconj.comp measurable_snd.snd)))`. Establish `hG : Measurable fun y : Mt k r × Mt k r => ∫⁻ h'', f (x, (h'', conjM a y.2)) ∂L.μW'` using `hF.lintegral_prod_left'`. Establish `hH' : Measurable fun q : Mt k r × Mt k r => f (x, (q.1, q.2))` using `hfm.comp (measurable_const.prodMk (measurable_fst.prodMk measurable_snd))`.

Establish `hH : Measurable fun n' : Mt k r => ∫⁻ h'', f (x, (h'', n')) ∂L.μW'` using `hH'.lintegral_prod_left'`. Establish `hfx : Measurable fun y : Mt k r × Mt k r => f (x, y)` using `hfm.comp (measurable_const.prodMk measurable_id)`. Rewrite using `[lintegral_prod _ hG.aemeasurable, lintegral_prod _ hfx.aemeasurable]`. Simplify using `only [lintegral_const, L.hμW'.2, one_mul]`. Establish `e1 : ∫⁻ n', ∫⁻ h'', f (x, (h'', conjM a n')) ∂L.μW' ∂L.μN = ∫⁻ n', ∫⁻ h'', f (x, (h'', n')) ∂L.μW' ∂(L.μN.map (conjM a))`.

Rewrite using `[lintegral_map hH hconj]`. Rewrite using `[e1, hmap, lintegral_smul_measure, smul_eq_mul]`. Establish `hs` using `lintegral_lintegral_swap (μ := L.μW') (ν := L.μN) (f := fun h'' n' => f (x, (h'', n'))) hH'.aemeasurable`. Rewrite using `[hs, mul_one]`.
-/
theorem inner_eq {k r : ℕ} (L : LocBessel k r) (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) {C : ℝ≥0∞}
    (hmap : L.μN.map (conjM a) = C • L.μN) {f : PairSp k r → ℝ≥0∞} (hfm : Measurable f) (x : Mt k r × Mt k r) :
    ∫⁻ y, ∫⁻ h'', f (x, (h'', conjM a y.2)) ∂L.μW' ∂(L.μW'.prod L.μN) = C * ∫⁻ y, f (x, y) ∂(L.μW'.prod L.μN) := by
  have : SFinite L.μN := by unfold LocBessel.μN haarLie; infer_instance
  have : SigmaFinite L.μW' := L.hμW'.1.1
  have hconj : Measurable (conjM (k := k) (r := r) a) := by
    have : Continuous (conjM (k := k) (r := r) a) := by
      unfold conjM
      exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    exact this.measurable
  have hF : Measurable fun q : Mt k r × (Mt k r × Mt k r) => f (x, (q.1, conjM a q.2.2)) :=
    hfm.comp (measurable_const.prodMk (measurable_fst.prodMk (hconj.comp measurable_snd.snd)))
  have hG : Measurable fun y : Mt k r × Mt k r => ∫⁻ h'', f (x, (h'', conjM a y.2)) ∂L.μW' :=
    hF.lintegral_prod_left'
  have hH' : Measurable fun q : Mt k r × Mt k r => f (x, (q.1, q.2)) :=
    hfm.comp (measurable_const.prodMk (measurable_fst.prodMk measurable_snd))
  have hH : Measurable fun n' : Mt k r => ∫⁻ h'', f (x, (h'', n')) ∂L.μW' := hH'.lintegral_prod_left'
  have hfx : Measurable fun y : Mt k r × Mt k r => f (x, y) := hfm.comp (measurable_const.prodMk measurable_id)
  rw [lintegral_prod _ hG.aemeasurable, lintegral_prod _ hfx.aemeasurable]
  simp only [lintegral_const, L.hμW'.2, one_mul]
  have e1 : ∫⁻ n', ∫⁻ h'', f (x, (h'', conjM a n')) ∂L.μW' ∂L.μN =
      ∫⁻ n', ∫⁻ h'', f (x, (h'', n')) ∂L.μW' ∂(L.μN.map (conjM a)) := by
    rw [lintegral_map hH hconj]
  rw [e1, hmap, lintegral_smul_measure, smul_eq_mul]
  have hs := lintegral_lintegral_swap (μ := L.μW') (ν := L.μN) (f := fun h'' n' => f (x, (h'', n')))
    hH'.aemeasurable
  rw [hs, mul_one]

open Formalism.FourierDecayAlt in

/- English proof (translation)
Introduce `k r L γ₁ a b C _hκ0 _hκ hb hγ ha hC hmap hint`. Establish `: SFinite L.μN` using `by unfold LocBessel.μN haarLie; infer_instance`. Establish `: SigmaFinite L.μW` using `L.hμW.1.1`. Establish `: SigmaFinite L.μW'` using `L.hμW'.1.1`. Take `⟨K, hK1, hK⟩` from `P.Dx3.UW_bound L.z' L.hz'.1 L.hz'.2`.

Use `set c : ℝ := K * K * B.gN a⁻¹ with hc`. Use `set f : PairSp k r → ℝ≥0∞ := fun p => ENNReal.ofReal (pairMaj γ₁ b p) with hfdef`. Establish `hfm : Measurable f` using `ENNReal.measurable_ofReal.comp (GlobalTheory.CellMaj.meas_pairMaj γ₁ b)`. Establish `hconj : Measurable (conjM (k` using `k) (r := r) a) := by`. Establish `: Continuous (conjM (k` using `k) (r := r) a) := by`.

Unfold `conjM`. Conclude with `(continuous_const.matrix_mul continuous_id).matrix_mul continuous_const`. Conclude with `this.measurable`. Use `set Φ : PairSp k r × Mt k r → PairSp k r := fun q => (q.1.1, (q.2, conjM a q.1.2.2)) with hΦdef`. Establish `hΦ : Measurable Φ` using `measurable_fst.fst.prodMk (measurable_snd.prodMk (hconj.comp measurable_fst.snd.snd))`.

Establish `aW' : ∀ᵐ y ∂L.μW', Matrix.of y ∈ UWset k r L.z'` using `by rw [ae_iff]; exact L.hμW'.1.2.2.1`. Establish `hP0 : ∀ p, 0 ≤ pairMaj (γ₁ * a) b p` using `fun p => Real.rpow_nonneg (P.B6.gN_nonneg _) _`. Establish `hQ0 : ∀ p, 0 ≤ pairMaj γ₁ b p` using `fun p => Real.rpow_nonneg (P.B6.gN_nonneg _) _`. Establish `hcb0 : 0 ≤ c ^ b` using `Real.rpow_nonneg (by rw [hc]; have := P.B6.gN_nonneg a⁻¹; positivity) _`. Establish `step1 : ∀ᵐ p ∂(pairMeas L), ENNReal.ofReal (pairMaj (γ₁ * a) b p) ≤ ∫⁻ h'', ENNReal.ofReal (c ^ b) * f (Φ (p, h'')) ∂L.μW'` using `by filter_upwards [GlobalTheory.CellOrbInt.ae_pairMeas L] with p hp`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[lintegral_const, L.hμW'.2, mul_one]`. Use `_ ≤ _ := by`. Use `lintegral_mono_ae ?_` and prove the remaining obligations. Use `filter_upwards [aW'] with h'' hh`.

Rewrite using `[hfdef, ← ENNReal.ofReal_mul hcb0]`. Conclude with `ENNReal.ofReal_le_ofReal (pt_bound L hγ ha hb hK1 hK hp hh)`. Establish `step2 : ∫⁻ p, ∫⁻ h'', f (Φ (p, h'')) ∂L.μW' ∂(pairMeas L) = C * ∫⁻ p, f p ∂(pairMeas L)`. Establish `hm : Measurable fun p : PairSp k r => ∫⁻ h'', f (Φ (p, h'')) ∂L.μW'` using `(hfm.comp hΦ).lintegral_prod_right'`. Unfold `pairMeas`.

Rewrite using `[lintegral_prod _ hm.aemeasurable, lintegral_prod _ hfm.aemeasurable]`. Rewrite using `[← lintegral_const_mul' _ _ hC]`. Use `lintegral_congr fun x => ?_` and prove the remaining obligations. Conclude with `inner_eq L a hmap hfm x`. Establish `hfin : ∫⁻ p, f p ∂(pairMeas L) < ⊤` using `(hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hQ0)).1 hint.2`.

Use `⟨(GlobalTheory.CellMaj.meas_pairMaj (γ₁ * a) b).aestronglyMeasurable, ?_⟩` and prove the remaining obligations. Rewrite using `[hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hP0)]`. Combine the equalities or inequalities in the displayed calculation. Repeatedly rewrite using `[lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]`. Rewrite using `[step2]`.

Use `_ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top hC.lt_top hfin)`.
-/
theorem integrable_mul_right : ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (γ₁ a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (b : ℝ) (C : ℝ≥0∞), 0 < L.κN → L.κN ≠ ⊤ → 0 ≤ b → γ₁ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) → a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) → C ≠ ⊤ → L.μN.map (Formalism.QuantumDeterminants.conjM a) = C • L.μN → MeasureTheory.Integrable (GlobalTheory.CellAmp.pairMaj γ₁ b) (Formalism.MainNotions.S.pairMeas L) → MeasureTheory.Integrable (GlobalTheory.CellAmp.pairMaj (γ₁ * a) b) (Formalism.MainNotions.S.pairMeas L) := by
  intro k r L γ₁ a b C _hκ0 _hκ hb hγ ha hC hmap hint
  have : SFinite L.μN := by unfold LocBessel.μN haarLie; infer_instance
  have : SigmaFinite L.μW := L.hμW.1.1
  have : SigmaFinite L.μW' := L.hμW'.1.1
  obtain ⟨K, hK1, hK⟩ := P.Dx3.UW_bound L.z' L.hz'.1 L.hz'.2
  set c : ℝ := K * K * B.gN a⁻¹ with hc
  set f : PairSp k r → ℝ≥0∞ := fun p => ENNReal.ofReal (pairMaj γ₁ b p) with hfdef
  have hfm : Measurable f := ENNReal.measurable_ofReal.comp (GlobalTheory.CellMaj.meas_pairMaj γ₁ b)
  have hconj : Measurable (conjM (k := k) (r := r) a) := by
    have : Continuous (conjM (k := k) (r := r) a) := by
      unfold conjM
      exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    exact this.measurable
  set Φ : PairSp k r × Mt k r → PairSp k r := fun q => (q.1.1, (q.2, conjM a q.1.2.2)) with hΦdef
  have hΦ : Measurable Φ := measurable_fst.fst.prodMk (measurable_snd.prodMk (hconj.comp measurable_fst.snd.snd))
  have aW' : ∀ᵐ y ∂L.μW', Matrix.of y ∈ UWset k r L.z' := by rw [ae_iff]; exact L.hμW'.1.2.2.1
  have hP0 : ∀ p, 0 ≤ pairMaj (γ₁ * a) b p := fun p => Real.rpow_nonneg (P.B6.gN_nonneg _) _
  have hQ0 : ∀ p, 0 ≤ pairMaj γ₁ b p := fun p => Real.rpow_nonneg (P.B6.gN_nonneg _) _
  have hcb0 : 0 ≤ c ^ b := Real.rpow_nonneg (by rw [hc]; have := P.B6.gN_nonneg a⁻¹; positivity) _
  have step1 : ∀ᵐ p ∂(pairMeas L), ENNReal.ofReal (pairMaj (γ₁ * a) b p) ≤
      ∫⁻ h'', ENNReal.ofReal (c ^ b) * f (Φ (p, h'')) ∂L.μW' := by
    filter_upwards [GlobalTheory.CellOrbInt.ae_pairMeas L] with p hp
    calc ENNReal.ofReal (pairMaj (γ₁ * a) b p) = ∫⁻ _h'', ENNReal.ofReal (pairMaj (γ₁ * a) b p) ∂L.μW' := by
          rw [lintegral_const, L.hμW'.2, mul_one]
      _ ≤ _ := by
          refine lintegral_mono_ae ?_
          filter_upwards [aW'] with h'' hh
          rw [hfdef, ← ENNReal.ofReal_mul hcb0]
          exact ENNReal.ofReal_le_ofReal (pt_bound L hγ ha hb hK1 hK hp hh)
  have step2 : ∫⁻ p, ∫⁻ h'', f (Φ (p, h'')) ∂L.μW' ∂(pairMeas L) = C * ∫⁻ p, f p ∂(pairMeas L) := by
    have hm : Measurable fun p : PairSp k r => ∫⁻ h'', f (Φ (p, h'')) ∂L.μW' := (hfm.comp hΦ).lintegral_prod_right'
    unfold pairMeas
    rw [lintegral_prod _ hm.aemeasurable, lintegral_prod _ hfm.aemeasurable]
    rw [← lintegral_const_mul' _ _ hC]
    refine lintegral_congr fun x => ?_
    exact inner_eq L a hmap hfm x
  have hfin : ∫⁻ p, f p ∂(pairMeas L) < ⊤ :=
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hQ0)).1 hint.2
  refine ⟨(GlobalTheory.CellMaj.meas_pairMaj (γ₁ * a) b).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hP0)]
  calc ∫⁻ p, ENNReal.ofReal (pairMaj (γ₁ * a) b p) ∂(pairMeas L)
      ≤ ∫⁻ p, ∫⁻ h'', ENNReal.ofReal (c ^ b) * f (Φ (p, h'')) ∂L.μW' ∂(pairMeas L) := lintegral_mono_ae step1
    _ = ENNReal.ofReal (c ^ b) * (C * ∫⁻ p, f p ∂(pairMeas L)) := by
        simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        rw [step2]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top hC.lt_top hfin)

end GlobalTheory.CellMajTransfer
