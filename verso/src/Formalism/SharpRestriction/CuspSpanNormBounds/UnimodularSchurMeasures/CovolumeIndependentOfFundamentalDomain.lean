import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.KernelConditionsIffWithoutRegularRep

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Set Topology
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

def LocFinF (X : CData) : Prop := IsLocallyFiniteMeasure X.μf

/- English proof (translation)
Use `set U : Set G := e ⁻¹' {e 1} with hU`. Establish `hUo : IsOpen U` using `hl.isOpen_fiber (e 1)`. Establish `hUfin : μ U < ⊤`. Establish `hsub : U ⊆ {x | ‖e 1‖ ≤ ‖e x‖}` using `fun x hx => by`. Establish `: e x = e 1` using `hx`.

Simplify using `[this]`. Conclude with `lt_of_le_of_lt (measure_mono hsub) (hi.measure_norm_ge_lt_top (norm_pos_iff.2 h1))`. Use `⟨fun x => ⟨(fun y => x⁻¹ * y) ⁻¹' U, ?_, ?_⟩⟩` and prove the remaining obligations. Conclude with `(hUo.preimage (continuous_const_mul x⁻¹)).mem_nhds (by simp [hU])`. Rewrite using `[measure_preimage_mul]`.

Conclude with `hUfin`.
-/
theorem rr_locFin_of_integrable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (e : G → ℂ) (hl : IsLocallyConstant e) (hi : Integrable e μ)
    (h1 : e 1 ≠ 0) : IsLocallyFiniteMeasure μ := by
  set U : Set G := e ⁻¹' {e 1} with hU
  have hUo : IsOpen U := hl.isOpen_fiber (e 1)
  have hUfin : μ U < ⊤ := by
    have hsub : U ⊆ {x | ‖e 1‖ ≤ ‖e x‖} := fun x hx => by
      have : e x = e 1 := hx
      simp [this]
    exact lt_of_le_of_lt (measure_mono hsub) (hi.measure_norm_ge_lt_top (norm_pos_iff.2 h1))
  refine ⟨fun x => ⟨(fun y => x⁻¹ * y) ⁻¹' U, ?_, ?_⟩⟩
  · exact (hUo.preimage (continuous_const_mul x⁻¹)).mem_nhds (by simp [hU])
  · rw [measure_preimage_mul]; exact hUfin

/- English proof (translation)
Establish `hH : X.μf.IsHaarMeasure` using `hX.2.1.2.2.2.1`. Establish `hadm` using `hX.1.2.2.2.2.2.2.1`. Conclude with `rr_locFin_of_integrable X.μf X.e hadm.1 hX.2.1.2.2.2.2.2.2.1 h1`.
-/
theorem LocFinF_of_e (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A) (h1 : X.e 1 ≠ 0) : LocFinF X := by
  have hH : X.μf.IsHaarMeasure := hX.2.1.2.2.2.1
  have hadm := hX.1.2.2.2.2.2.2.1
  exact rr_locFin_of_integrable X.μf X.e hadm.1 hX.2.1.2.2.2.2.2.2.1 h1

/- English proof (translation)
The claim follows from `inferInstance`.
-/
example (X : CData) [SecondCountableTopology X.I.Gf] : BorelSpace X.I.GA := inferInstance
/- English proof (translation)
The claim follows from `inferInstance`.
-/
example (X : CData) : IsTopologicalGroup X.I.GA := inferInstance
/- English proof (translation)
The claim follows from `inferInstance`.
-/
example (X : CData) [SecondCountableTopology X.I.Gf] : SecondCountableTopology X.I.GA := inferInstance
/- English proof (translation)
Establish `: Fact ((2 : ℝ≥0∞) ≠ ⊤)` using `⟨by norm_num⟩`. Establish `: SigmaFinite (X.I.muA X.μf)` using `rr_muA_sigmaFinite X.I X.μf`. Use `infer_instance`.
-/
theorem automorphic_L2_secondCountable (X : CData) [SecondCountableTopology X.I.Gf] : SecondCountableTopology X.L2 := by
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  have : SigmaFinite (X.I.muA X.μf) := rr_muA_sigmaFinite X.I X.μf
  infer_instance
/- English proof (translation)
The claim follows from `inferInstance`.
-/
example (X : CData) : IsLocallyFiniteMeasure (Measure.pi fun v => Formalism.REAL.muG (X.I.ε v)) := inferInstance
/- English proof (translation)
The claim follows from `inferInstance`.
-/
example (X : CData) : (Measure.pi fun v => Formalism.REAL.muG (X.I.ε v)).IsHaarMeasure := inferInstance
/- English proof (translation)
The claim follows from `inferInstance`.
-/
example (X : CData) : LocallyCompactSpace X.I.Ginf := inferInstance
/- English proof (translation)
The claim follows from `inferInstance`.
-/
example (X : CData) : BorelSpace X.I.Ginf := inferInstance
/- English proof (translation)
The claim follows from `inferInstance`.
-/
example (X : CData) : T2Space X.I.Ginf := inferInstance

/- English proof (translation)
Establish `: IsLocallyFiniteMeasure X.μf` using `h`. Unfold `AutInst.muA`. Use `infer_instance`.
-/
theorem rr_muA_locFin (X : CData) (h : LocFinF X) : IsLocallyFiniteMeasure (X.I.muA X.μf) := by
  have : IsLocallyFiniteMeasure X.μf := h
  unfold AutInst.muA; infer_instance

/- English proof (translation)
Unfold `AutInst.muA`. Use `infer_instance`.
-/
theorem rr_muA_openPos (X : CData) [X.μf.IsHaarMeasure] : (X.I.muA X.μf).IsOpenPosMeasure := by
  unfold AutInst.muA; infer_instance

/- English proof (translation)
Establish `: (I.muA μf).IsMulLeftInvariant` using `rr_muA_left I μf`. Conclude with `(rr_isFD (rr_FD_of I μf fund h)).measure_eq (rr_isFD (rr_FD_of I μf fund' h'))`.
-/
theorem covolume_independent_of_fundamental_domain (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsMulLeftInvariant] (fund fund' : Set I.GA)
    (h : I.IsFundDom (I.muA μf) fund) (h' : I.IsFundDom (I.muA μf) fund') : I.muA μf fund = I.muA μf fund' := by
  have : (I.muA μf).IsMulLeftInvariant := rr_muA_left I μf
  exact (rr_isFD (rr_FD_of I μf fund h)).measure_eq (rr_isFD (rr_FD_of I μf fund' h'))

end Formalism.MainNotions.LeviCoordinates

end
