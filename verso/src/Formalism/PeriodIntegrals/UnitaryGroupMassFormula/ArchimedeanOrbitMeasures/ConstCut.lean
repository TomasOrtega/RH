import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PushCut

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

abbrev HmI {D : D7} (X : HidaSetting D) : Type :=
  HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)

abbrev MfI {D : D7} (X : HidaSetting D) : Type :=
  Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)

def Y0 {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) : TupI X :=
  ratTup (Ainf X.B.I.F) (tupH (frameOf X u'))

def rmulT {D : D7} (X : HidaSetting D) (a : MfI X) (Y : TupI X) : TupI X :=
  fun b i => ∑ c, a c b * Y c i

/- English proof (translation)
Use function extensionality and compare the values at `b i`. Simplify using `[rmulT, Matrix.one_apply]`.
-/
theorem rmulT_one {D : D7} (X : HidaSetting D) (Y : TupI X) : rmulT X 1 Y = Y := by
  funext b i
  simp [rmulT, Matrix.one_apply]

def GramMeas : Prop := ∀ {D : D7} (X : HidaSetting D) (S : Set (HmI X)), MeasurableSet S →
    MeasurableSet (gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' (Subtype.val '' S))

def OrbMeas : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word), Measurable (orbM X u')

def KPos : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → 0 < KVal X u'

def PolarLoc : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    ∃ (Ω : Set (HmI X)) (a : HmI X → MfI X) (KT : HmI X → ℝ),
      Ω ∈ 𝓝 (TI X u' hT) ∧ a (TI X u' hT) = 1 ∧ ContinuousAt a (TI X u' hT) ∧
      KT (TI X u' hT) = KVal X u' ∧ ContinuousAt KT (TI X u' hT) ∧
      ∀ φ : TupI X → ENNReal, Measurable φ → ∀ S ⊆ Ω, MeasurableSet S →
        ∫⁻ y in gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' (Subtype.val '' S) ∩ IndI X, φ y ∂μinf =
          ∫⁻ T in S, (ENNReal.ofReal (KT T))⁻¹ *
            ∫⁻ g, φ (g • rmulT X (a T) (Y0 X u')) ∂X.measG.μGinf ∂νinf

def PushCont : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    ∀ a : HmI X → MfI X, a (TI X u' hT) = 1 → ContinuousAt a (TI X u' hT) →
    ∃ φ : TupI X → ℝ, Continuous φ ∧ Measurable φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ IndI X ∧ (∀ y, 0 ≤ φ y) ∧
      0 < ∫⁻ g, ENNReal.ofReal (φ (g • Y0 X u')) ∂X.measG.μGinf ∧
      ∫⁻ g, ENNReal.ofReal (φ (g • Y0 X u')) ∂X.measG.μGinf < ⊤ ∧
      ContinuousAt (fun T => ∫⁻ g, ENNReal.ofReal (φ (g • rmulT X (a T) (Y0 X u'))) ∂X.measG.μGinf)
        (TI X u' hT)

def HermLF : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → ∃ V ∈ 𝓝 (TI X u' hT), νinf V < ⊤

/- English proof (translation)
Establish `key : ∀ g₁ g₂ : Y → ENNReal, ContinuousAt g₁ x → ContinuousAt g₂ x → (∀ S ⊆ Ω, MeasurableSet S → ∫⁻ y in S, g₁ y ∂ν = ∫⁻ y in S, g₂ y ∂ν) → ¬ g₁ x < g₂ x`. Introduce `g₁ g₂ c₁ c₂ hS hlt`. Take `⟨c, hc1, hc2⟩` from `exists_between hlt`. Take `⟨d, hd1, hd2⟩` from `exists_between hc2`. Establish `e1 : g₁ ⁻¹' Set.Iio c ∈ 𝓝 x` using `c₁ (Iio_mem_nhds hc1)`.

Establish `e2 : g₂ ⁻¹' Set.Ioi d ∈ 𝓝 x` using `c₂ (Ioi_mem_nhds hd2)`. Take `⟨U, hUsub, hUo, hxU⟩` from `mem_nhds_iff.1 (inter_mem (inter_mem hΩ hV) (inter_mem e1 e2))`. Establish `hUm : MeasurableSet U` using `hUo.measurableSet`. Establish `hpos : ν U ≠ 0` using `(hUo.measure_pos ν ⟨x, hxU⟩).ne'`. Establish `hfin : ν U ≠ ⊤` using `(lt_of_le_of_lt (measure_mono fun y hy => (hUsub hy).1.2) hVf).ne`.

Establish `le1 : ∫⁻ y in U, g₁ y ∂ν ≤ ∫⁻ _ in U, c ∂ν` using `lintegral_mono_ae ((ae_restrict_iff' hUm).2 (Eventually.of_forall fun y hy => le_of_lt (hUsub hy).2.1))`. Establish `le2 : ∫⁻ _ in U, d ∂ν ≤ ∫⁻ y in U, g₂ y ∂ν` using `lintegral_mono_ae ((ae_restrict_iff' hUm).2 (Eventually.of_forall fun y hy => le_of_lt (hUsub hy).2.2))`. Rewrite `le1`, `le2` using `[setLIntegral_const]`. Establish `hcd : c * ν U < d * ν U` using `ENNReal.mul_left_strictMono hpos hfin hd1`. Establish `hSU` using `hS U (fun y hy => (hUsub hy).1.1) hUm`.

Conclude with `absurd (le2.trans ((le_of_eq hSU.symm).trans le1)) (not_le.2 hcd)`. Break down `lt_trichotomy (f₁ x) (f₂ x) with hl | he | hg` into its components or cases. Conclude with `absurd hl (key f₁ f₂ h₁ h₂ h)`. Conclude with `he`. Conclude with `absurd hg (key f₂ f₁ h₂ h₁ fun S hS hm => (h S hS hm).symm)`.
-/
theorem eq_of_setLIntegral {Y : Type} [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    (ν : Measure Y) [ν.IsOpenPosMeasure] {x : Y} {Ω V : Set Y} (hΩ : Ω ∈ 𝓝 x) (hV : V ∈ 𝓝 x) (hVf : ν V < ⊤)
    {f₁ f₂ : Y → ENNReal} (h₁ : ContinuousAt f₁ x) (h₂ : ContinuousAt f₂ x)
    (h : ∀ S ⊆ Ω, MeasurableSet S → ∫⁻ y in S, f₁ y ∂ν = ∫⁻ y in S, f₂ y ∂ν) : f₁ x = f₂ x := by
  have key : ∀ g₁ g₂ : Y → ENNReal, ContinuousAt g₁ x → ContinuousAt g₂ x →
      (∀ S ⊆ Ω, MeasurableSet S → ∫⁻ y in S, g₁ y ∂ν = ∫⁻ y in S, g₂ y ∂ν) → ¬ g₁ x < g₂ x := by
    intro g₁ g₂ c₁ c₂ hS hlt
    obtain ⟨c, hc1, hc2⟩ := exists_between hlt
    obtain ⟨d, hd1, hd2⟩ := exists_between hc2
    have e1 : g₁ ⁻¹' Set.Iio c ∈ 𝓝 x := c₁ (Iio_mem_nhds hc1)
    have e2 : g₂ ⁻¹' Set.Ioi d ∈ 𝓝 x := c₂ (Ioi_mem_nhds hd2)
    obtain ⟨U, hUsub, hUo, hxU⟩ := mem_nhds_iff.1 (inter_mem (inter_mem hΩ hV) (inter_mem e1 e2))
    have hUm : MeasurableSet U := hUo.measurableSet
    have hpos : ν U ≠ 0 := (hUo.measure_pos ν ⟨x, hxU⟩).ne'
    have hfin : ν U ≠ ⊤ := (lt_of_le_of_lt (measure_mono fun y hy => (hUsub hy).1.2) hVf).ne
    have le1 : ∫⁻ y in U, g₁ y ∂ν ≤ ∫⁻ _ in U, c ∂ν :=
      lintegral_mono_ae ((ae_restrict_iff' hUm).2 (Eventually.of_forall fun y hy => le_of_lt (hUsub hy).2.1))
    have le2 : ∫⁻ _ in U, d ∂ν ≤ ∫⁻ y in U, g₂ y ∂ν :=
      lintegral_mono_ae ((ae_restrict_iff' hUm).2 (Eventually.of_forall fun y hy => le_of_lt (hUsub hy).2.2))
    rw [setLIntegral_const] at le1 le2
    have hcd : c * ν U < d * ν U := ENNReal.mul_left_strictMono hpos hfin hd1
    have hSU := hS U (fun y hy => (hUsub hy).1.1) hUm
    exact absurd (le2.trans ((le_of_eq hSU.symm).trans le1)) (not_le.2 hcd)
  rcases lt_trichotomy (f₁ x) (f₂ x) with hl | he | hg
  · exact absurd hl (key f₁ f₂ h₁ h₂ h)
  · exact he
  · exact absurd hg (key f₂ f₁ h₂ h₁ fun S hS hm => (h S hS hm).symm)

/- English proof (translation)
Introduce `D X u' ψ hT μinf νinf fibInf hH`. Take `⟨Ω, a, KT, hΩ, ha1, hac, hKT, hKc, hPol⟩` from `hP X u' ψ hT μinf νinf fibInf hH`. Establish `hK0 : 0 < KVal X u'` using `hK X u' ψ hT μinf νinf fibInf hH`. Take `⟨φ, hφc, hφm, hφs, hφU, hφ0, hIpos, hIfin, hIc⟩` from `hC X u' ψ hT μinf νinf fibInf hH a ha1 hac`. Take `⟨V, hV, hVf⟩` from `hL X u' ψ hT μinf νinf fibInf hH`.

Establish `hfib` using `hH.2.2.2.2.2.2`. Establish `: νinf.IsAddHaarMeasure` using `hH.2.2.2.2.2.1.1`. Establish `: BorelSpace (HmI X)` using `⟨rfl⟩`. Establish `hΦm : Measurable fun y => ENNReal.ofReal (φ y)` using `ENNReal.measurable_ofReal.comp hφm`. Set `Ff : HmI X → ENNReal` to `fun T => ∫⁻ y, ENNReal.ofReal (φ y) ∂(fibInf T)`.

Set `Fp : HmI X → ENNReal` to `fun T => (ENNReal.ofReal (KT T))⁻¹ * ∫⁻ g, ENNReal.ofReal (φ (g • rmulT X (a T) (Y0 X u'))) ∂X.measG.μGinf`. Establish `step1 : ∀ S ⊆ Ω, MeasurableSet S → ∫⁻ T in S, Ff T ∂νinf = ∫⁻ T in S, Fp T ∂νinf`. Introduce `S hSΩ hS`. Establish `hGS` using `hG X S hS`. Establish `c2` using `hfib.2.1 ((gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' (Subtype.val '' S)).indicator fun y => ENNReal.ofReal (φ y)) (hΦm.indicator hGS)`.

Rewrite `c2` using `[lintegral_indicator hGS, Measure.restrict_restrict hGS, hPol _ hΦm S hSΩ hS]`. Establish `inner : ∀ b, ∫⁻ v, (gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' (Subtype.val '' S)).indicator (fun y => ENNReal.ofReal (φ y)) v ∂(fibInf b) = S.indicator Ff b`. Introduce `b`. Establish `hae : ∀ᵐ y ∂(fibInf b), y ∈ gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' {Subtype.val b} ∩ IndI X` using `ae_iff.2 (hfib.1 b)`. Distinguish the cases in `hb : b ∈ S`.

Rewrite using `[Set.indicator_of_mem hb Ff]`. Apply `lintegral_congr_ae` to reduce the goal to its premises. Use `filter_upwards [hae] with y hy`. Establish `hy1` using `Set.mem_singleton_iff.1 (Set.mem_preimage.1 hy.1)`. Conclude with `Set.indicator_of_mem (Set.mem_preimage.2 (show gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J y ∈ Subtype.val '' S from ⟨b, hb, hy1.symm⟩)) _`.

Rewrite using `[Set.indicator_of_notMem hb Ff]`. Combine the equalities or inequalities in the displayed calculation. Apply `lintegral_congr_ae` to reduce the goal to its premises. Use `filter_upwards [hae] with y hy`. Establish `hy1` using `Set.mem_singleton_iff.1 (Set.mem_preimage.1 hy.1)`.

Use `Set.indicator_of_notMem ?_ _` and prove the remaining obligations. Introduce and unpack `⟨c, hc, hcy⟩`. Establish `hcb : c = b` using `Subtype.val_injective (hcy.trans hy1)`. Conclude with `hb (hcb ▸ hc)`. Use `_ = 0 := lintegral_zero`.

Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Use function extensionality and compare the values at `b`. Conclude with `(inner b).symm`. Use `_ = ∫⁻ T in S, Fp T ∂νinf := c2.symm`.

Establish `c3` using `hfib.2.2 φ hφc hφs hφU`. Establish `hFfeq : Ff = fun T => ENNReal.ofReal (∫ v, φ v ∂(fibInf T))`. Use function extensionality and compare the values at `T`. Conclude with `(ofReal_integral_eq_lintegral_ofReal (c3.1 T (Set.mem_univ _)) (Eventually.of_forall fun y => hφ0 y)).symm`. Establish `hFfc : ContinuousAt Ff (TI X u' hT)`.

Rewrite using `[hFfeq]`. Conclude with `(ENNReal.continuous_ofReal.comp (continuousOn_univ.1 c3.2)).continuousAt`. Establish `hKinv : (ENNReal.ofReal (KT (TI X u' hT)))⁻¹ ≠ ⊤`. Rewrite using `[hKT]`. Conclude with `ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hK0).ne'`.

Establish `hI1 : ∫⁻ g, ENNReal.ofReal (φ (g • rmulT X (a (TI X u' hT)) (Y0 X u'))) ∂X.measG.μGinf ≠ ⊤`. Rewrite using `[ha1, rmulT_one]`. Conclude with `hIfin.ne`. Establish `hKc' : ContinuousAt (fun T => (ENNReal.ofReal (KT T))⁻¹) (TI X u' hT)` using `tendsto_inv_iff.2 (ENNReal.continuous_ofReal.continuousAt.comp hKc)`. Establish `hFpc : ContinuousAt Fp (TI X u' hT)` using `ENNReal.Tendsto.mul hKc' (Or.inr hI1) hIc (Or.inr hKinv)`.

Establish `heq : Ff (TI X u' hT) = Fp (TI X u' hT)` using `eq_of_setLIntegral νinf hΩ hV hVf hFfc hFpc step1`. Establish `hFp0 : Fp (TI X u' hT) = (ENNReal.ofReal (KVal X u'))⁻¹ * ∫⁻ g, ENNReal.ofReal (φ (g • Y0 X u')) ∂X.measG.μGinf` using `by show (ENNReal.ofReal (KT (TI X u' hT)))⁻¹ * _ = _`. Rewrite using `[hKT, ha1, rmulT_one]`. Establish `hmap : ∫⁻ y, ENNReal.ofReal (φ y) ∂(X.measG.μGinf.map (orbM X u')) = ∫⁻ g, ENNReal.ofReal (φ (g • Y0 X u')) ∂X.measG.μGinf` using `lintegral_map hΦm (hO X u')`. Establish `hk0 : ENNReal.ofReal (KVal X u') ≠ 0` using `(ENNReal.ofReal_pos.2 hK0).ne'`.

Establish `hkT : ENNReal.ofReal (KVal X u') ≠ ⊤` using `ENNReal.ofReal_ne_top`. Establish `hF : ∫⁻ y, ENNReal.ofReal (φ y) ∂(fibInf (TI X u' hT)) = (ENNReal.ofReal (KVal X u'))⁻¹ * ∫⁻ g, ENNReal.ofReal (φ (g • Y0 X u')) ∂X.measG.μGinf` using `heq.trans hFp0`. Use `⟨fun y => ENNReal.ofReal (φ y), hΦm, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hF]`. Conclude with `ENNReal.mul_pos (ENNReal.inv_ne_zero.2 hkT) hIpos.ne'`.

Rewrite using `[hF]`. Conclude with `ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (ENNReal.ofReal_pos.2 hK0)) hIfin`. Rewrite using `[hF, hmap, ← mul_assoc, ENNReal.mul_inv_cancel hk0 hkT, one_mul]`.
-/
theorem constTest_of (hG : GramMeas) (hO : OrbMeas) (hK : KPos) (hP : PolarLoc) (hC : PushCont) (hL : HermLF) :
    ConstTest := by
  intro D X u' ψ hT μinf νinf fibInf hH
  obtain ⟨Ω, a, KT, hΩ, ha1, hac, hKT, hKc, hPol⟩ := hP X u' ψ hT μinf νinf fibInf hH
  have hK0 : 0 < KVal X u' := hK X u' ψ hT μinf νinf fibInf hH
  obtain ⟨φ, hφc, hφm, hφs, hφU, hφ0, hIpos, hIfin, hIc⟩ := hC X u' ψ hT μinf νinf fibInf hH a ha1 hac
  obtain ⟨V, hV, hVf⟩ := hL X u' ψ hT μinf νinf fibInf hH
  have hfib := hH.2.2.2.2.2.2
  have : νinf.IsAddHaarMeasure := hH.2.2.2.2.2.1.1
  have : BorelSpace (HmI X) := ⟨rfl⟩
  have hΦm : Measurable fun y => ENNReal.ofReal (φ y) := ENNReal.measurable_ofReal.comp hφm

  let Ff : HmI X → ENNReal := fun T => ∫⁻ y, ENNReal.ofReal (φ y) ∂(fibInf T)
  let Fp : HmI X → ENNReal := fun T =>
    (ENNReal.ofReal (KT T))⁻¹ * ∫⁻ g, ENNReal.ofReal (φ (g • rmulT X (a T) (Y0 X u'))) ∂X.measG.μGinf
  have step1 : ∀ S ⊆ Ω, MeasurableSet S → ∫⁻ T in S, Ff T ∂νinf = ∫⁻ T in S, Fp T ∂νinf := by
    intro S hSΩ hS
    have hGS := hG X S hS
    have c2 := hfib.2.1 ((gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' (Subtype.val '' S)).indicator
      fun y => ENNReal.ofReal (φ y)) (hΦm.indicator hGS)
    rw [lintegral_indicator hGS, Measure.restrict_restrict hGS, hPol _ hΦm S hSΩ hS] at c2
    have inner : ∀ b, ∫⁻ v, (gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' (Subtype.val '' S)).indicator
        (fun y => ENNReal.ofReal (φ y)) v ∂(fibInf b) = S.indicator Ff b := by
      intro b
      have hae : ∀ᵐ y ∂(fibInf b), y ∈ gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' {Subtype.val b} ∩ IndI X :=
        ae_iff.2 (hfib.1 b)
      by_cases hb : b ∈ S
      · rw [Set.indicator_of_mem hb Ff]
        apply lintegral_congr_ae
        filter_upwards [hae] with y hy
        have hy1 := Set.mem_singleton_iff.1 (Set.mem_preimage.1 hy.1)
        exact Set.indicator_of_mem (Set.mem_preimage.2 (show gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J y ∈ Subtype.val '' S
          from ⟨b, hb, hy1.symm⟩)) _
      · rw [Set.indicator_of_notMem hb Ff]
        calc _ = ∫⁻ _, (0 : ENNReal) ∂(fibInf b) := by
                apply lintegral_congr_ae
                filter_upwards [hae] with y hy
                have hy1 := Set.mem_singleton_iff.1 (Set.mem_preimage.1 hy.1)
                refine Set.indicator_of_notMem ?_ _
                rintro ⟨c, hc, hcy⟩
                have hcb : c = b := Subtype.val_injective (hcy.trans hy1)
                exact hb (hcb ▸ hc)
          _ = 0 := lintegral_zero
    calc ∫⁻ T in S, Ff T ∂νinf = ∫⁻ T, S.indicator Ff T ∂νinf := (lintegral_indicator hS _).symm
      _ = ∫⁻ b, ∫⁻ v, (gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' (Subtype.val '' S)).indicator
            (fun y => ENNReal.ofReal (φ y)) v ∂(fibInf b) ∂νinf := by
          congr 1; funext b; exact (inner b).symm
      _ = ∫⁻ T in S, Fp T ∂νinf := c2.symm

  have c3 := hfib.2.2 φ hφc hφs hφU
  have hFfeq : Ff = fun T => ENNReal.ofReal (∫ v, φ v ∂(fibInf T)) := by
    funext T
    exact (ofReal_integral_eq_lintegral_ofReal (c3.1 T (Set.mem_univ _))
      (Eventually.of_forall fun y => hφ0 y)).symm
  have hFfc : ContinuousAt Ff (TI X u' hT) := by
    rw [hFfeq]
    exact (ENNReal.continuous_ofReal.comp (continuousOn_univ.1 c3.2)).continuousAt

  have hKinv : (ENNReal.ofReal (KT (TI X u' hT)))⁻¹ ≠ ⊤ := by
    rw [hKT]; exact ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hK0).ne'
  have hI1 : ∫⁻ g, ENNReal.ofReal (φ (g • rmulT X (a (TI X u' hT)) (Y0 X u'))) ∂X.measG.μGinf ≠ ⊤ := by
    rw [ha1, rmulT_one]; exact hIfin.ne
  have hKc' : ContinuousAt (fun T => (ENNReal.ofReal (KT T))⁻¹) (TI X u' hT) :=
    tendsto_inv_iff.2 (ENNReal.continuous_ofReal.continuousAt.comp hKc)
  have hFpc : ContinuousAt Fp (TI X u' hT) := ENNReal.Tendsto.mul hKc' (Or.inr hI1) hIc (Or.inr hKinv)

  have heq : Ff (TI X u' hT) = Fp (TI X u' hT) := eq_of_setLIntegral νinf hΩ hV hVf hFfc hFpc step1
  have hFp0 : Fp (TI X u' hT) = (ENNReal.ofReal (KVal X u'))⁻¹ *
      ∫⁻ g, ENNReal.ofReal (φ (g • Y0 X u')) ∂X.measG.μGinf := by
    show (ENNReal.ofReal (KT (TI X u' hT)))⁻¹ * _ = _
    rw [hKT, ha1, rmulT_one]
  have hmap : ∫⁻ y, ENNReal.ofReal (φ y) ∂(X.measG.μGinf.map (orbM X u')) =
      ∫⁻ g, ENNReal.ofReal (φ (g • Y0 X u')) ∂X.measG.μGinf :=
    lintegral_map hΦm (hO X u')
  have hk0 : ENNReal.ofReal (KVal X u') ≠ 0 := (ENNReal.ofReal_pos.2 hK0).ne'
  have hkT : ENNReal.ofReal (KVal X u') ≠ ⊤ := ENNReal.ofReal_ne_top
  have hF : ∫⁻ y, ENNReal.ofReal (φ y) ∂(fibInf (TI X u' hT)) = (ENNReal.ofReal (KVal X u'))⁻¹ *
      ∫⁻ g, ENNReal.ofReal (φ (g • Y0 X u')) ∂X.measG.μGinf := heq.trans hFp0
  refine ⟨fun y => ENNReal.ofReal (φ y), hΦm, ?_, ?_, ?_⟩
  · rw [hF]; exact ENNReal.mul_pos (ENNReal.inv_ne_zero.2 hkT) hIpos.ne'
  · rw [hF]; exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (ENNReal.ofReal_pos.2 hK0)) hIfin
  · rw [hF, hmap, ← mul_assoc, ENNReal.mul_inv_cancel hk0 hkT, one_mul]

end PI.AprimeInfW
