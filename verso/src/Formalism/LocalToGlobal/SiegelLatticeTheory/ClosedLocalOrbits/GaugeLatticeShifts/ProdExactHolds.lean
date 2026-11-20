import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ProductFormulaHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ExistsBox
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SecMeasLocHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StepRealHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalJacobianOfDoubleCoset
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NHLocHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealPf

noncomputable section

open MeasureTheory Topology NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal

namespace Formalism.L2.SG.RealObj.InfCut.ProductExactness

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Rewrite using `[← ENNReal.coe_toNNReal hc, ← ENNReal.smul_def]`. Use `infer_instance`.
-/
theorem sf_smul {β : Type*} [MeasurableSpace β] (μ : Measure β) [SigmaFinite μ] (c : ℝ≥0∞) (hc : c ≠ ∞) :
    SigmaFinite (c • μ) := by
  rw [← ENNReal.coe_toNNReal hc, ← ENNReal.smul_def]
  infer_instance

/- English proof (translation)
Introduce `D X u u' μN μN' μH μH' C hσN hσN' hσH hσH' hC hN hN' hH hH' hDis`. Use `haveI : ∀ v, SigmaFinite (μN v) := hσN`. Use `haveI : ∀ v, SigmaFinite (μN' v) := hσN'`. Use `haveI : ∀ v, SigmaFinite (μH v) := hσH`. Use `haveI : ∀ v, SigmaFinite (μH' v) := hσH'`.

Establish `hU : UnimodLoc` using `JL.rightInvS_of JL.setCorr_holds (JL.haarCorr_of JL.setCorr_holds)`. Apply the tactic sequence `have hep : ∀ v a b, hJ (X.B.I.ε v) (eV X v a) (pV X v b) = if a = b then 1 else 0 := fun v a b => (hJ_X X v _ _).trans (by rw [X.ef]; split_ifs <;> simp)`. Establish `hpp : ∀ v a b, hJ (X.B.I.ε v) (pV X v a) (pV X v b) = 0` using `fun v a b => (hJ_X X v _ _).trans (by rw [X.ff]; simp)`. Establish `hzp : ∀ w v b, hJ (X.B.I.ε v) (zV X w v) (pV X v b) = 0` using `fun w v b => by`. Establish `h0 : hJ (X.B.I.ε v) (pV X v b) (zV X w v) = 0` using `(hJ_X X v _ _).trans (by rw [(X.zu_orth w b).2]; simp)`.

Rewrite using `[hJ_cj, h0, map_zero]`. Establish `hSH : ∀ w v, IsHaarS (SLoc (X.B.I.ε v) (eV X v) (zV X w v)) (muSv X w v)` using `fun w v => NilradicalHermitianFrames.NH.NHLoc_holds _ _ _ _ _ _ _ _ _ _ (frameLoc_X X w u v) (hep v) (hpp v) (hzp w v) _ _ (muNv_haar X w v) (muHv_haar X w v)`. Establish `fN : ∀ (w : D.what₂.Word) (μ : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v))) [∀ v, SigmaFinite (μ v)], X.muN w = Measure.pi μ → ∀ v, ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ∞ ∧ μ v = κ • muNv X w v`. Introduce `w μ _ hw v`. Take `⟨_, h0, hc, hi⟩` from `X.muN_haar w`.

Rewrite `hc`, `hi` using `[← NinfG_coe, hw]`. Rewrite `h0` using `[hw]`. Rewrite `hc` using `[NinfG, Subgroup.coe_pi]`. Conclude with `PiM.factor_uniq μ (NGv X w) (fun v => NilradicalHermitianFrames.NH.NG_closed _ _ _) (muNv X w) (fun v => (muNv_haar X w v).1.2.2.1) (fun v => (muNv_haar X w v).1.2.2.2) (fun v => (muNv_haar X w v).1.2.1) h0 hc (fun g hg => hi g ((Subgroup.mem_pi _).2 fun v _ => hg v)) v`. Establish `fH : ∀ (w : D.what₂.Word) (μ : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v))) [∀ v, SigmaFinite (μ v)], X.muH w = Measure.pi μ → ∀ v, ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ∞ ∧ μ v = κ • muHv X w v`.

Introduce `w μ _ hw v`. Take `⟨_, h0, hc, hi⟩` from `X.muH_haar w`. Rewrite `hc`, `hi` using `[← HinfG_coe, hw]`. Rewrite `h0` using `[hw]`. Rewrite `hc` using `[HinfG, Subgroup.coe_pi]`.

Conclude with `PiM.factor_uniq μ (HGv X w) (fun v => NilradicalHermitianFrames.NH.HG_closed _ _ _ _) (muHv X w) (fun v => (muHv_haar X w v).1.2.2.1) (fun v => (muHv_haar X w v).1.2.2.2) (fun v => (muHv_haar X w v).1.2.1) h0 hc (fun g hg => hi g ((Subgroup.mem_pi _).2 fun v _ => hg v)) v`. Use `choose κN hκN0 hκNT hκN using fN u μN hN`. Use `choose κN' hκN'0 hκN'T hκN' using fN u' μN' hN'`. Use `choose κH hκH0 hκHT hκH using fH u μH hH`. Use `choose κH' hκH'0 hκH'T hκH' using fH u' μH' hH'`.

Establish `hSL : ∀ v, Formalism.L2.SG.Pf.NcReal.muSL (μH v) (μN v) = (κN v * κH v) • muSv X u v` using `fun v => by haveI : SigmaFinite (muHv X u v) := inferInstance`. Unfold `Formalism.L2.SG.Pf.NcReal.muSL muSv`. Rewrite using `[hκN v, hκH v, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, Measure.map_smul]`. Establish `hSL' : ∀ v, Formalism.L2.SG.Pf.NcReal.muSL (μH' v) (μN' v) = (κN' v * κH' v) • muSv X u' v` using `fun v => by`. Unfold `Formalism.L2.SG.Pf.NcReal.muSL muSv`.

Rewrite using `[hκN' v, hκH' v, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, Measure.map_smul]`. Use `haveI : ∀ w v, SigmaFinite (muSv X w v) := fun w v => (hSH w v).1.1`. Use `haveI hσS : ∀ v, SigmaFinite (Formalism.L2.SG.Pf.NcReal.muSL (μH v) (μN v)) := fun v => by`. Rewrite using `[hSL v]`. Conclude with `sf_smul _ _ (ENNReal.mul_ne_top (hκNT v) (hκHT v))`.

Use `haveI hσS' : ∀ v, SigmaFinite (Formalism.L2.SG.Pf.NcReal.muSL (μH' v) (μN' v)) := fun v => by`. Rewrite using `[hSL' v]`. Conclude with `sf_smul _ _ (ENNReal.mul_ne_top (hκN'T v) (hκH'T v))`. Establish `hmS : ∀ (w : D.what₂.Word) (ρN ρH : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v))) [∀ v, SigmaFinite (ρN v)] [∀ v, SigmaFinite (ρH v)] [∀ v, SigmaFinite (Formalism.L2.SG.Pf.NcReal.muSL (ρH v) (ρN v))], X.muN w = Measure.pi ρN → X.muH w = Measure.pi ρH → muS X w = Measure.pi fun v …`. Introduce `w ρN ρH _ _ hσ h1 h2`.

Unfold `muS`. Rewrite using `[h1, h2]`. Establish `mp` using `measurePreserving_piProd ρN ρH`. Rewrite using `[← mp.map_eq, Measure.map_map (measurable_mul : Measurable fun p : X.B.I.Ginf × X.B.I.Ginf => p.1 * p.2) mp.measurable]`. Use `haveI : ∀ v, SigmaFinite (((ρN v).prod (ρH v)).map (fun q : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v) => q.1 * q.2)) := hσ`.

Conclude with `Measure.pi_map_pi (f := fun v (q : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v)) => q.1 * q.2) (fun v => measurable_mul.aemeasurable)`. Establish `hmu` using `hmS u μN μH hN hH`. Establish `hmu'` using `hmS u' μN' μH' hN' hH'`. Establish `hsec` using `fun v => SecMeasLoc_holds _ _ _ _ _ _ _ _ _ 1 (frameLoc_X X u u' v) one_pos`. Use `choose hs hsm hss using hsec`.

Establish `hloc : ∀ v, Formalism.REAL.muG (X.B.I.ε v) = ((nuLoc (r` using `D.R.rS) D.R.k (Tw u) (Tw u') (C v)).prod ((Formalism.L2.SG.Pf.NcReal.muSL (μH v) (μN v)).prod (Formalism.L2.SG.Pf.NcReal.muSL (μH' v) (μN' v)))).map (phiLoc (X.B.I.ε v) (hs v)) := fun v => muG_eq_map _ _ _ _ _ _ _ (hsm v) _ (hDis v (hs v) (hss v))`. Introduce `φ hφ`. Establish `hpf` using `prod_formula (fun v => Formalism.REAL.muG (X.B.I.ε v)) (fun v => nuLoc (r := D.R.rS) D.R.k (Tw u) (Tw u') (C v)) (fun v => Formalism.L2.SG.Pf.NcReal.muSL (μH v) (μN v)) (fun v => Formalism.L2.SG.Pf.NcReal.muSL (μH' v) (μN' v)) hs hsm hloc φ hφ`. Express the relevant statement in the definitionally equal form `∫⁻ x, φ x ∂(Measure.pi fun v => Formalism.REAL.muG (X.B.I.ε v)) = _`. Rewrite using `[hpf]`.

Establish `hwm : ∀ v, Measurable fun c : Fin (D.R.rS + 1) → ℂ => ENNReal.ofReal (C v * wtLoc D.R.k (Tw u) (Tw u') c)` using `fun v => ENNReal.measurable_ofReal.comp (measurable_const.mul (wtLoc_cont D.R.k (Tw u) (Tw u')).measurable)`. Establish `hν : Measure.pi (fun v => nuLoc (r` using `D.R.rS) D.R.k (Tw u) (Tw u') (C v)) = ((dcInf X).restrict (Good X u u')).withDensity (fun c => ∏ v, ENNReal.ofReal (C v * wtLoc D.R.k (Tw u) (Tw u') (c v))) := by`. Unfold `nuLoc`. Use `haveI : SigmaFinite (dcLoc (r := D.R.rS)) := by unfold dcLoc; infer_instance`. Rewrite using `[PiM.pi_withDensity _ _ hwm (fun v x => ENNReal.ofReal_ne_top), ← Measure.restrict_pi_pi, good_eq]`.

Both sides reduce to the same expression. Use `set H : (Cinf X) → X.B.I.Ginf := fun c v => hs v (c v) with hHd`. Establish `hHm : Measurable H` using `measurable_pi_lambda _ fun v => (hsm v).comp (measurable_pi_apply v)`. Use `set μP := Measure.pi fun v => Formalism.L2.SG.Pf.NcReal.muSL (μH v) (μN v) with hμP`. Use `set μP' := Measure.pi fun v => Formalism.L2.SG.Pf.NcReal.muSL (μH' v) (μN' v) with hμP'`.

Use `set Fc : Cinf X → ℝ≥0∞ := fun c => ∫⁻ s, ∫⁻ s', φ (s * H c * s'⁻¹) ∂μP' ∂μP with hFc`. Establish `hFm : Measurable Fc`. Establish `h1 : Measurable fun q : (Cinf X × X.B.I.Ginf) × X.B.I.Ginf => φ (q.1.2 * H q.1.1 * q.2⁻¹)` using `hφ.comp (((measurable_snd.comp measurable_fst).mul (hHm.comp (measurable_fst.comp measurable_fst))).mul measurable_snd.inv)`. Conclude with `h1.lintegral_prod_right'.lintegral_prod_right'`. Rewrite using `[show (∫⁻ c, ∫⁻ s, ∫⁻ s', φ (s * (fun v => hs v (c v)) * s'⁻¹) ∂μP' ∂μP ∂Measure.pi fun v => nuLoc (r := D.R.rS) D.R.k (Tw u) (Tw u') (C v)) = ∫⁻ c, Fc c ∂Measure.pi fun v => nuLoc (r := D.R.rS) D.R.k (Tw u) (Tw u') (C v) from rfl, hν, lintegral_withDensity_eq_lintegral_mul _ (f …`.

Establish `hGm : MeasurableSet (Good X u u')`. Rewrite using `[good_eq]`. Conclude with `MeasurableSet.univ_pi fun v => measurableSet_goodLoc _ _`. Use `setLIntegral_congr_fun hGm fun c hc => ?_` and prove the remaining obligations. Simplify using `only [Pi.mul_apply]`.

Establish `hcv : ∀ v, c v ∈ GoodLoc (r` using `D.R.rS) (Tw u) (Tw u') := fun v => by`. Rewrite `hc` using `[good_eq, Set.mem_univ_pi]`. Conclude with `hc v`. Establish `hW : ∏ v, ENNReal.ofReal (C v * wtLoc D.R.k (Tw u) (Tw u') (c v)) = ENNReal.ofReal ((∏ v, C v) * wt X u u' c)`. Rewrite using `[← ENNReal.ofReal_prod_of_nonneg fun v _ => mul_nonneg (hC v).le (wtLoc_nonneg _ _ _ (hcv v)), Finset.prod_mul_distrib]`.

Both sides reduce to the same expression. Establish `hex` using `StepReal_holds D X u u' 1 one_pos c hc`. Establish `hh : HasDiag X u u' 1 c (hOf X u u' 1 c)`. Unfold `hOf`. Rewrite using `[dif_pos hex]`.

Conclude with `hex.choose_spec`. Establish `hdc` using `fun v => Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.DiagDCLoc_holds _ _ _ _ _ _ _ _ _ 1 (frameLoc_X X u u' v) (c v) (hcv v) (hs v (c v)) (hOf X u u' 1 c v) (hss v (c v) (hcv v)) (hh v)`. Use `choose t ht t' ht' htt using hdc`. Establish `hofe : hOf X u u' 1 c = t * H c * t'⁻¹` using `funext fun v => htt v`. Establish `hrt : μP.map (fun x => x * t) = μP` using `PiM.pi_map_mul_right _ t fun v => by`.

Rewrite using `[hSL v, Measure.map_smul, hU _ _ _ _ _ _ _ _ _ (frameLoc_X X u u' v) _ (hSH u v) (t v) (ht v)]`. Establish `hrt' : μP'.map (fun x => x * t') = μP'` using `PiM.pi_map_mul_right _ t' fun v => by`. Rewrite using `[hSL' v, Measure.map_smul, hU _ _ _ _ _ _ _ _ _ (frameLoc_X X u' u v) _ (hSH u' v) (t' v) (ht' v)]`. Establish `hsw : ∫⁻ s, ∫⁻ s', φ (s * hOf X u u' 1 c * s'⁻¹) ∂μP' ∂μP = Fc c`. Rewrite using `[hofe]`.

Conclude with `dc_switch _ _ φ hφ (H c) t t' hrt hrt'`. Rewrite using `[hW, hmu, hmu', hsw]`.
-/
theorem ProdExact_holds : Formalism.L2.SG.Pf.NcReal.ProdExact := by
  classical
  intro D X u u' μN μN' μH μH' C hσN hσN' hσH hσH' hC hN hN' hH hH' hDis
  haveI : ∀ v, SigmaFinite (μN v) := hσN
  haveI : ∀ v, SigmaFinite (μN' v) := hσN'
  haveI : ∀ v, SigmaFinite (μH v) := hσH
  haveI : ∀ v, SigmaFinite (μH' v) := hσH'
  have hU : UnimodLoc := JL.rightInvS_of JL.setCorr_holds (JL.haarCorr_of JL.setCorr_holds)
  have hep : ∀ v a b, hJ (X.B.I.ε v) (eV X v a) (pV X v b) = if a = b then 1 else 0 := fun v a b =>
    (hJ_X X v _ _).trans (by rw [X.ef]; split_ifs <;> simp)
  have hpp : ∀ v a b, hJ (X.B.I.ε v) (pV X v a) (pV X v b) = 0 := fun v a b =>
    (hJ_X X v _ _).trans (by rw [X.ff]; simp)
  have hzp : ∀ w v b, hJ (X.B.I.ε v) (zV X w v) (pV X v b) = 0 := fun w v b => by
    have h0 : hJ (X.B.I.ε v) (pV X v b) (zV X w v) = 0 :=
      (hJ_X X v _ _).trans (by rw [(X.zu_orth w b).2]; simp)
    rw [hJ_cj, h0, map_zero]
  have hSH : ∀ w v, IsHaarS (SLoc (X.B.I.ε v) (eV X v) (zV X w v)) (muSv X w v) := fun w v =>
    NilradicalHermitianFrames.NH.NHLoc_holds _ _ _ _ _ _ _ _ _ _ (frameLoc_X X w u v) (hep v) (hpp v) (hzp w v) _ _
      (muNv_haar X w v) (muHv_haar X w v)

  have fN : ∀ (w : D.what₂.Word) (μ : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v))) [∀ v, SigmaFinite (μ v)],
      X.muN w = Measure.pi μ → ∀ v, ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ∞ ∧ μ v = κ • muNv X w v := by
    intro w μ _ hw v
    obtain ⟨_, h0, hc, hi⟩ := X.muN_haar w
    rw [← NinfG_coe, hw] at hc hi
    rw [hw] at h0
    rw [NinfG, Subgroup.coe_pi] at hc
    exact PiM.factor_uniq μ (NGv X w) (fun v => NilradicalHermitianFrames.NH.NG_closed _ _ _) (muNv X w)
      (fun v => (muNv_haar X w v).1.2.2.1) (fun v => (muNv_haar X w v).1.2.2.2) (fun v => (muNv_haar X w v).1.2.1)
      h0 hc (fun g hg => hi g ((Subgroup.mem_pi _).2 fun v _ => hg v)) v
  have fH : ∀ (w : D.what₂.Word) (μ : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v))) [∀ v, SigmaFinite (μ v)],
      X.muH w = Measure.pi μ → ∀ v, ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ∞ ∧ μ v = κ • muHv X w v := by
    intro w μ _ hw v
    obtain ⟨_, h0, hc, hi⟩ := X.muH_haar w
    rw [← HinfG_coe, hw] at hc hi
    rw [hw] at h0
    rw [HinfG, Subgroup.coe_pi] at hc
    exact PiM.factor_uniq μ (HGv X w) (fun v => NilradicalHermitianFrames.NH.HG_closed _ _ _ _) (muHv X w)
      (fun v => (muHv_haar X w v).1.2.2.1) (fun v => (muHv_haar X w v).1.2.2.2) (fun v => (muHv_haar X w v).1.2.1)
      h0 hc (fun g hg => hi g ((Subgroup.mem_pi _).2 fun v _ => hg v)) v
  choose κN hκN0 hκNT hκN using fN u μN hN
  choose κN' hκN'0 hκN'T hκN' using fN u' μN' hN'
  choose κH hκH0 hκHT hκH using fH u μH hH
  choose κH' hκH'0 hκH'T hκH' using fH u' μH' hH'
  have hSL : ∀ v, Formalism.L2.SG.Pf.NcReal.muSL (μH v) (μN v) = (κN v * κH v) • muSv X u v := fun v => by
    haveI : SigmaFinite (muHv X u v) := inferInstance
    unfold Formalism.L2.SG.Pf.NcReal.muSL muSv
    rw [hκN v, hκH v, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, Measure.map_smul]
  have hSL' : ∀ v, Formalism.L2.SG.Pf.NcReal.muSL (μH' v) (μN' v) = (κN' v * κH' v) • muSv X u' v := fun v => by
    unfold Formalism.L2.SG.Pf.NcReal.muSL muSv
    rw [hκN' v, hκH' v, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, Measure.map_smul]
  haveI : ∀ w v, SigmaFinite (muSv X w v) := fun w v => (hSH w v).1.1
  haveI hσS : ∀ v, SigmaFinite (Formalism.L2.SG.Pf.NcReal.muSL (μH v) (μN v)) := fun v => by
    rw [hSL v]; exact sf_smul _ _ (ENNReal.mul_ne_top (hκNT v) (hκHT v))
  haveI hσS' : ∀ v, SigmaFinite (Formalism.L2.SG.Pf.NcReal.muSL (μH' v) (μN' v)) := fun v => by
    rw [hSL' v]; exact sf_smul _ _ (ENNReal.mul_ne_top (hκN'T v) (hκH'T v))

  have hmS : ∀ (w : D.what₂.Word) (ρN ρH : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v))) [∀ v, SigmaFinite (ρN v)]
      [∀ v, SigmaFinite (ρH v)] [∀ v, SigmaFinite (Formalism.L2.SG.Pf.NcReal.muSL (ρH v) (ρN v))],
      X.muN w = Measure.pi ρN → X.muH w = Measure.pi ρH →
      muS X w = Measure.pi fun v => Formalism.L2.SG.Pf.NcReal.muSL (ρH v) (ρN v) := by
    intro w ρN ρH _ _ hσ h1 h2
    unfold muS
    rw [h1, h2]
    have mp := measurePreserving_piProd ρN ρH
    rw [← mp.map_eq, Measure.map_map (measurable_mul : Measurable fun p : X.B.I.Ginf × X.B.I.Ginf => p.1 * p.2)
      mp.measurable]
    haveI : ∀ v, SigmaFinite (((ρN v).prod (ρH v)).map
        (fun q : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v) => q.1 * q.2)) := hσ
    exact Measure.pi_map_pi (f := fun v (q : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v)) => q.1 * q.2)
      (fun v => measurable_mul.aemeasurable)
  have hmu := hmS u μN μH hN hH
  have hmu' := hmS u' μN' μH' hN' hH'

  have hsec := fun v => SecMeasLoc_holds _ _ _ _ _ _ _ _ _ 1 (frameLoc_X X u u' v) one_pos
  choose hs hsm hss using hsec
  have hloc : ∀ v, Formalism.REAL.muG (X.B.I.ε v) =
      ((nuLoc (r := D.R.rS) D.R.k (Tw u) (Tw u') (C v)).prod ((Formalism.L2.SG.Pf.NcReal.muSL (μH v) (μN v)).prod
        (Formalism.L2.SG.Pf.NcReal.muSL (μH' v) (μN' v)))).map (phiLoc (X.B.I.ε v) (hs v)) := fun v =>
    muG_eq_map _ _ _ _ _ _ _ (hsm v) _ (hDis v (hs v) (hss v))
  intro φ hφ
  have hpf := prod_formula (fun v => Formalism.REAL.muG (X.B.I.ε v)) (fun v => nuLoc (r := D.R.rS) D.R.k (Tw u) (Tw u') (C v))
    (fun v => Formalism.L2.SG.Pf.NcReal.muSL (μH v) (μN v)) (fun v => Formalism.L2.SG.Pf.NcReal.muSL (μH' v) (μN' v)) hs hsm hloc φ hφ
  change ∫⁻ x, φ x ∂(Measure.pi fun v => Formalism.REAL.muG (X.B.I.ε v)) = _
  rw [hpf]
  have hwm : ∀ v, Measurable fun c : Fin (D.R.rS + 1) → ℂ => ENNReal.ofReal (C v * wtLoc D.R.k (Tw u) (Tw u') c) :=
    fun v => ENNReal.measurable_ofReal.comp (measurable_const.mul (wtLoc_cont D.R.k (Tw u) (Tw u')).measurable)
  have hν : Measure.pi (fun v => nuLoc (r := D.R.rS) D.R.k (Tw u) (Tw u') (C v)) =
      ((dcInf X).restrict (Good X u u')).withDensity
        (fun c => ∏ v, ENNReal.ofReal (C v * wtLoc D.R.k (Tw u) (Tw u') (c v))) := by
    unfold nuLoc
    haveI : SigmaFinite (dcLoc (r := D.R.rS)) := by unfold dcLoc; infer_instance
    rw [PiM.pi_withDensity _ _ hwm (fun v x => ENNReal.ofReal_ne_top), ← Measure.restrict_pi_pi, good_eq]
    rfl
  set H : (Cinf X) → X.B.I.Ginf := fun c v => hs v (c v) with hHd
  have hHm : Measurable H := measurable_pi_lambda _ fun v => (hsm v).comp (measurable_pi_apply v)
  set μP := Measure.pi fun v => Formalism.L2.SG.Pf.NcReal.muSL (μH v) (μN v) with hμP
  set μP' := Measure.pi fun v => Formalism.L2.SG.Pf.NcReal.muSL (μH' v) (μN' v) with hμP'
  set Fc : Cinf X → ℝ≥0∞ := fun c => ∫⁻ s, ∫⁻ s', φ (s * H c * s'⁻¹) ∂μP' ∂μP with hFc
  have hFm : Measurable Fc := by
    have h1 : Measurable fun q : (Cinf X × X.B.I.Ginf) × X.B.I.Ginf => φ (q.1.2 * H q.1.1 * q.2⁻¹) :=
      hφ.comp (((measurable_snd.comp measurable_fst).mul (hHm.comp (measurable_fst.comp measurable_fst))).mul
        measurable_snd.inv)
    exact h1.lintegral_prod_right'.lintegral_prod_right'
  rw [show (∫⁻ c, ∫⁻ s, ∫⁻ s', φ (s * (fun v => hs v (c v)) * s'⁻¹) ∂μP' ∂μP
      ∂Measure.pi fun v => nuLoc (r := D.R.rS) D.R.k (Tw u) (Tw u') (C v)) = ∫⁻ c, Fc c
      ∂Measure.pi fun v => nuLoc (r := D.R.rS) D.R.k (Tw u) (Tw u') (C v) from rfl,
    hν, lintegral_withDensity_eq_lintegral_mul _
      (f := fun c : Cinf X => ∏ v, ENNReal.ofReal (C v * wtLoc D.R.k (Tw u) (Tw u') (c v)))
      (Finset.measurable_prod _ fun v _ => (hwm v).comp (measurable_pi_apply v)) hFm]
  have hGm : MeasurableSet (Good X u u') := by
    rw [good_eq]; exact MeasurableSet.univ_pi fun v => measurableSet_goodLoc _ _
  refine setLIntegral_congr_fun hGm fun c hc => ?_
  simp only [Pi.mul_apply]
  have hcv : ∀ v, c v ∈ GoodLoc (r := D.R.rS) (Tw u) (Tw u') := fun v => by
    rw [good_eq, Set.mem_univ_pi] at hc; exact hc v
  have hW : ∏ v, ENNReal.ofReal (C v * wtLoc D.R.k (Tw u) (Tw u') (c v)) =
      ENNReal.ofReal ((∏ v, C v) * wt X u u' c) := by
    rw [← ENNReal.ofReal_prod_of_nonneg fun v _ => mul_nonneg (hC v).le (wtLoc_nonneg _ _ _ (hcv v)),
      Finset.prod_mul_distrib]
    rfl
  have hex := StepReal_holds D X u u' 1 one_pos c hc
  have hh : HasDiag X u u' 1 c (hOf X u u' 1 c) := by
    unfold hOf; rw [dif_pos hex]; exact hex.choose_spec
  have hdc := fun v => Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.DiagDCLoc_holds _ _ _ _ _ _ _ _ _ 1 (frameLoc_X X u u' v) (c v)
    (hcv v) (hs v (c v)) (hOf X u u' 1 c v) (hss v (c v) (hcv v)) (hh v)
  choose t ht t' ht' htt using hdc
  have hofe : hOf X u u' 1 c = t * H c * t'⁻¹ := funext fun v => htt v
  have hrt : μP.map (fun x => x * t) = μP :=
    PiM.pi_map_mul_right _ t fun v => by
      rw [hSL v, Measure.map_smul,
        hU _ _ _ _ _ _ _ _ _ (frameLoc_X X u u' v) _ (hSH u v) (t v) (ht v)]
  have hrt' : μP'.map (fun x => x * t') = μP' :=
    PiM.pi_map_mul_right _ t' fun v => by
      rw [hSL' v, Measure.map_smul,
        hU _ _ _ _ _ _ _ _ _ (frameLoc_X X u' u v) _ (hSH u' v) (t' v) (ht' v)]
  have hsw : ∫⁻ s, ∫⁻ s', φ (s * hOf X u u' 1 c * s'⁻¹) ∂μP' ∂μP = Fc c := by
    rw [hofe]; exact dc_switch _ _ φ hφ (H c) t t' hrt hrt'
  rw [hW, hmu, hmu', hsw]

end Formalism.L2.SG.RealObj.InfCut.ProductExactness
