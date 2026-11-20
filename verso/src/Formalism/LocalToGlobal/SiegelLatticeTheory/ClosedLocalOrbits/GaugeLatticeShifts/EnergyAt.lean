import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyInst
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RealObjClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsMain
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HaarDisintegrationRealHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.SchurTensInst
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.HaarSubSWire
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.SecWGlob

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.SG.RealObj.EnergyInst

open Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.EnergyAbs

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def StepIntAt (D : D7) : Prop :=
  ∀ (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ), 0 < sc →
    ∀ c ∈ Good X u u', ∀ γ, HasDiag X u u' sc c γ →
      TermOp.OOInt (Formalism.L2.SG.ProjRows.muInf X.B.I) Set.univ (X.Wu u) (X.Wu u') γ

def StepConvAt (D : D7) : Prop :=
  ∀ (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ), 0 < sc →
    (∀ c ∈ Good X u u', ∀ γ, HasDiag X u u' sc c γ →
      ∫⁻ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', ‖⟪X.B.σs z (X.B.tens X.B.w),
          X.B.σs (s * γ * s'⁻¹) (X.B.σs z' (X.B.tens X.B.w))⟫_ℂ‖ₑ * ‖X.Wu u z‖ₑ * ‖X.Wu u' z'‖ₑ
        ∂(muS X u') ∂(muS X u) ∂(X.nuQ u') ∂(X.nuQ u) < ⊤) ∧
    ∀ w : D.what₂.Word,
      ∫⁻ z, ∫⁻ z', ∫⁻ s, ‖⟪X.B.σs z (X.B.tens X.B.w), X.B.σs s (X.B.σs z' (X.B.tens X.B.w))⟫_ℂ‖ₑ *
        ‖X.Wu w z‖ₑ * ‖X.Wu w z'‖ₑ ∂(muS X w) ∂(X.nuQ w) ∂(X.nuQ w) < ⊤

def StepEnergyAt (D : D7) : Prop :=
  ∀ (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ), 0 < sc →
    DisintegrationConstantPositive X u u' sc → CoordOK X u u' sc → intOOe X u u' sc ≤ ENNReal.ofReal (1 / degX X)

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

/- English proof (translation)
Introduce `X u u' sc hsc h27 _`. Take `⟨hUR, hSch, hw, -⟩` from `hS D X`. Take `⟨hHu, hFu, -, -, hSFu⟩` from `hG D X u`. Take `⟨hHu', hFu', -, -, hSFu'⟩` from `hG D X u'`. Take `⟨hh, hhm, hhd⟩` from `hSec D X u u' sc hsc`.

Establish `hGood : MeasurableSet (Good X u u')`. Rewrite using `[Formalism.L2.SG.RealObj.EnergyCut.good_eq_pi X u u']`. Conclude with `MeasurableSet.univ_pi fun _ => Formalism.L2.SG.RealObj.EnergyCut.goodV_meas u u'`. Distinguish the cases in `hne : (Good X u u').Nonempty`. Use `swap`.

Establish `h0 : Good X u u' = ∅` using `Set.not_nonempty_iff_eq_empty.mp hne`. Simplify using `[intOOe, nuM, h0]`. Take `⟨c₀, hc₀⟩` from `hne`. Set `g : Cinf X → X.B.I.Ginf` to `(Good X u u').piecewise hh (fun _ => hh c₀)`. Establish `hgm : Measurable g` using `Measurable.piecewise hGood hhm measurable_const`.

Establish `hgG : ∀ c ∈ Good X u u', g c = hh c` using `fun c hc => Set.piecewise_eq_of_mem _ _ _ hc`. Establish `hgd : ∀ c, ∃ c' ∈ Good X u u', HasDiag X u u' sc c' (g c)`. Introduce `c`. Distinguish the cases in `hc : c ∈ Good X u u'`. Conclude with `⟨c, hc, by rw [hgG c hc]; exact hhd c hc⟩`.

Use `⟨c₀, hc₀, ?_⟩` and prove the remaining obligations. Establish `: g c = hh c₀` using `Set.piecewise_eq_of_notMem _ _ _ hc`. Rewrite using `[this]`. Conclude with `hhd c₀ hc₀`. Establish `hgD : ∀ c ∈ Good X u u', HasDiag X u u' sc c (g c)` using `fun c hc => by`.

Rewrite using `[hgG c hc]`. Conclude with `hhd c hc`. Establish `hOfD : ∀ c ∈ Good X u u', HasDiag X u u' sc c (hOf X u u' sc c)`. Introduce `c hc`. Establish `hex : ∃ γ, HasDiag X u u' sc c γ` using `⟨hh c, hhd c hc⟩`.

Establish `e : hOf X u u' sc c = hex.choose` using `dif_pos hex`. Rewrite using `[e]`. Conclude with `hex.choose_spec`. Establish `hD : Disint X u u' sc (DisintegrationConstant X u u' sc)`. Establish `e : DisintegrationConstant X u u' sc = h27.choose` using `dif_pos h27`.

Rewrite using `[e]`. Conclude with `h27.choose_spec.2`. Establish `hm : Measurable fun c => ENNReal.ofReal (DisintegrationConstant X u u' sc * wt X u u' c)` using `ENNReal.measurable_ofReal.comp ((Formalism.L2.SG.RealObj.InfCut.wt_cont X u u').measurable.const_mul _)`. Establish `hDis : Formalism.L2.SG.Pf.EnergyAbs.IsDisint (Formalism.L2.SG.ProjRows.muInf X.B.I) (muS X u) (muS X u') (nuM X u u' sc) g`. Introduce `φ hφ`.

Rewrite using `[hD φ hφ, nuM, lintegral_withDensity_eq_lintegral_mul_non_measurable _ hm (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]`. Use `lintegral_congr_ae (ae_restrict_of_forall_mem hGood fun c hc => ?_)` and prove the remaining obligations. Simplify using `only [Pi.mul_apply]`. Use `congr 1`. Take `⟨a, ha, b, hb, hab⟩` from `InfCut.UnitaryIsometries.StepDiagDC_holds D X u u' sc c hc _ _ (hOfD c hc) (hgD c hc)`.

Conclude with `(inner_transfer X hG u u' φ hφ _ _ a ha b hb hab).symm`. Establish `key` using `hE X.B.I.Ginf (Formalism.L2.SG.ProjRows.muInf X.B.I) _ X.B.σs (degX X) (X.B.tens X.B.w) (X.Vpi u) (X.Vpi u') (X.SinfU u) (X.SinfU u') (muS X u) (muS X u') (X.nuQ u) (X.nuQ u') (tauU X u) (tauU X u') (X.Wu u) (X.Wu u') (Cinf X) inferInstance (nuM X u u' sc) g hUR hSch hw hHu hHu' …`. Take `⟨c', hc', hd⟩` from `hgd c`. Conclude with `integrableOn_univ.mp (hI X u u' sc hsc c' hc' (g c) hd))`. Use the proof step `(fun c => by`.

Take `⟨c', hc', hd⟩` from `hgd c`. Conclude with `(hC X u u' sc hsc).1 c' hc' (g c) hd)`. Use the proof step `((hC X u u' sc hsc).2 u) ((hC X u u' sc hsc).2 u')`. Use `le_trans (le_of_eq ?_) key` and prove the remaining obligations. Establish `hae : ∀ᵐ c ∂(nuM X u u' sc), c ∈ Good X u u'`.

Rewrite using `[nuM]`. Conclude with `withDensity_absolutelyContinuous _ _ (ae_restrict_mem hGood)`. Establish `hIndep : OOIndep X u u' sc` using `InfCut.ooIndep_of_step X InfCut.UnitaryIsometries.StepDiagDC_holds u u' sc`. Unfold `intOOe`. Use `lintegral_congr_ae ?_` and prove the remaining obligations.

Use `filter_upwards [hae] with c hc`. Rewrite using `[hilbertSchmidtSqGram, hIndep c hc _ _ (hOfD c hc) (hgD c hc)]`. Simplify using `only [OOinf, TermOp.OO, Measure.restrict_univ]`. Both sides reduce to the same expression.
-/
theorem stepEnergyAt_of_inst (D : D7) (hE : EnergyAbs) (hS : StepSchurG) (hG : StepSubG) (hSec : StepSection)
    (hC : StepConvAt D) (hI : StepIntAt D) : StepEnergyAt D := by
  classical
  intro X u u' sc hsc h27 _
  obtain ⟨hUR, hSch, hw, -⟩ := hS D X
  obtain ⟨hHu, hFu, -, -, hSFu⟩ := hG D X u
  obtain ⟨hHu', hFu', -, -, hSFu'⟩ := hG D X u'
  obtain ⟨hh, hhm, hhd⟩ := hSec D X u u' sc hsc
  have hGood : MeasurableSet (Good X u u') := by
    rw [Formalism.L2.SG.RealObj.EnergyCut.good_eq_pi X u u']
    exact MeasurableSet.univ_pi fun _ => Formalism.L2.SG.RealObj.EnergyCut.goodV_meas u u'
  by_cases hne : (Good X u u').Nonempty
  swap
  · have h0 : Good X u u' = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp [intOOe, nuM, h0]
  obtain ⟨c₀, hc₀⟩ := hne
  let g : Cinf X → X.B.I.Ginf := (Good X u u').piecewise hh (fun _ => hh c₀)
  have hgm : Measurable g := Measurable.piecewise hGood hhm measurable_const
  have hgG : ∀ c ∈ Good X u u', g c = hh c := fun c hc => Set.piecewise_eq_of_mem _ _ _ hc
  have hgd : ∀ c, ∃ c' ∈ Good X u u', HasDiag X u u' sc c' (g c) := by
    intro c
    by_cases hc : c ∈ Good X u u'
    · exact ⟨c, hc, by rw [hgG c hc]; exact hhd c hc⟩
    · refine ⟨c₀, hc₀, ?_⟩
      have : g c = hh c₀ := Set.piecewise_eq_of_notMem _ _ _ hc
      rw [this]; exact hhd c₀ hc₀
  have hgD : ∀ c ∈ Good X u u', HasDiag X u u' sc c (g c) := fun c hc => by
    rw [hgG c hc]; exact hhd c hc
  have hOfD : ∀ c ∈ Good X u u', HasDiag X u u' sc c (hOf X u u' sc c) := by
    intro c hc
    have hex : ∃ γ, HasDiag X u u' sc c γ := ⟨hh c, hhd c hc⟩
    have e : hOf X u u' sc c = hex.choose := dif_pos hex
    rw [e]
    exact hex.choose_spec
  have hD : Disint X u u' sc (DisintegrationConstant X u u' sc) := by
    have e : DisintegrationConstant X u u' sc = h27.choose := dif_pos h27
    rw [e]
    exact h27.choose_spec.2
  have hm : Measurable fun c => ENNReal.ofReal (DisintegrationConstant X u u' sc * wt X u u' c) :=
    ENNReal.measurable_ofReal.comp ((Formalism.L2.SG.RealObj.InfCut.wt_cont X u u').measurable.const_mul _)
  have hDis : Formalism.L2.SG.Pf.EnergyAbs.IsDisint (Formalism.L2.SG.ProjRows.muInf X.B.I) (muS X u) (muS X u')
      (nuM X u u' sc) g := by
    intro φ hφ
    rw [hD φ hφ, nuM, lintegral_withDensity_eq_lintegral_mul_non_measurable _ hm
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine lintegral_congr_ae (ae_restrict_of_forall_mem hGood fun c hc => ?_)
    simp only [Pi.mul_apply]
    congr 1
    obtain ⟨a, ha, b, hb, hab⟩ :=
      InfCut.UnitaryIsometries.StepDiagDC_holds D X u u' sc c hc _ _ (hOfD c hc) (hgD c hc)
    exact (inner_transfer X hG u u' φ hφ _ _ a ha b hb hab).symm
  have key := hE X.B.I.Ginf (Formalism.L2.SG.ProjRows.muInf X.B.I) _ X.B.σs (degX X) (X.B.tens X.B.w)
    (X.Vpi u) (X.Vpi u') (X.SinfU u) (X.SinfU u') (muS X u) (muS X u') (X.nuQ u) (X.nuQ u')
    (tauU X u) (tauU X u') (X.Wu u) (X.Wu u') (Cinf X) inferInstance (nuM X u u' sc) g
    hUR hSch hw hHu hHu' hFu hFu' hSFu hSFu' (fun f hf => X.nuQ_weil u f hf)
    (fun f hf => X.nuQ_weil u' f hf) (isWAbs_of X hS hG u) (isWAbs_of X hS hG u') hDis hgm
    (fun c => by
      obtain ⟨c', hc', hd⟩ := hgd c
      exact integrableOn_univ.mp (hI X u u' sc hsc c' hc' (g c) hd))
    (fun c => by
      obtain ⟨c', hc', hd⟩ := hgd c
      exact (hC X u u' sc hsc).1 c' hc' (g c) hd)
    ((hC X u u' sc hsc).2 u) ((hC X u u' sc hsc).2 u')
  refine le_trans (le_of_eq ?_) key
  have hae : ∀ᵐ c ∂(nuM X u u' sc), c ∈ Good X u u' := by
    rw [nuM]
    exact withDensity_absolutelyContinuous _ _ (ae_restrict_mem hGood)
  have hIndep : OOIndep X u u' sc := InfCut.ooIndep_of_step X InfCut.UnitaryIsometries.StepDiagDC_holds u u' sc
  unfold intOOe
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with c hc
  rw [hilbertSchmidtSqGram, hIndep c hc _ _ (hOfD c hc) (hgD c hc)]
  simp only [OOinf, TermOp.OO, Measure.restrict_univ]
  rfl

/- English proof (translation)
Establish `h27 : DisintegrationConstantPositive X u u' sc` using `InfCut.ProductExactness.haar_disintegration_real_holds D X u u' sc hsc`. Establish `hR` using `InfCut.ProductExactness.StepReal_holds D X u u' sc hsc`. Establish `hco : CoordOK X u u' sc`. Use `⟨hR, fun c hc => ?_⟩` and prove the remaining obligations. Establish `hex` using `hR c hc`.

Use `hI X u u' sc hsc c hc _ ?_` and prove the remaining obligations. Establish `e : hOf X u u' sc c = hex.choose` using `dif_pos hex`. Rewrite using `[e]`. Conclude with `hex.choose_spec`. Conclude with `⟨h27, hco, stepEnergyAt_of_inst D S.Pv.EnergyAbs.energyAbs_holds S.Pv.SchurTens.stepSchurG_holds S.Pv.HaarSubS.stepSubG_holds S.Pv.SecW.stepSection_holds hC hI X u u' sc hsc h27 hco⟩`.
-/
theorem inInfinityXAt (hI : StepIntAt D) (hC : StepConvAt D) (u u' : D.what₂.Word) (sc : ℝ) (hsc : 0 < sc) :
    InInfinityX X u u' sc := by
  have h27 : DisintegrationConstantPositive X u u' sc := InfCut.ProductExactness.haar_disintegration_real_holds D X u u' sc hsc
  have hR := InfCut.ProductExactness.StepReal_holds D X u u' sc hsc
  have hco : CoordOK X u u' sc := by
    refine ⟨hR, fun c hc => ?_⟩
    have hex := hR c hc
    refine hI X u u' sc hsc c hc _ ?_
    have e : hOf X u u' sc c = hex.choose := dif_pos hex
    rw [e]
    exact hex.choose_spec
  exact ⟨h27, hco, stepEnergyAt_of_inst D S.Pv.EnergyAbs.energyAbs_holds S.Pv.SchurTens.stepSchurG_holds
    S.Pv.HaarSubS.stepSubG_holds S.Pv.SecW.stepSection_holds hC hI X u u' sc hsc h27 hco⟩

end Formalism.L2.SG.RealObj.EnergyInst
