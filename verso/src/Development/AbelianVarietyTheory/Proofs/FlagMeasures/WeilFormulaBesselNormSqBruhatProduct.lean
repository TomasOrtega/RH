import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacobianCoordinates
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpWinLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NinfGClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.WuDecayPf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.LintegralFintypeProd
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.Pf.AmpWinLoc

namespace GlobalTheory

/- English proof (translation)
Introduce `D X u κ M hMs hS β hβm hβ1`. Use `haveI := hMs`. Take `⟨hNsf, -, hN0, -⟩` from `X.muN_haar u`. Take `⟨hHsf, -, hH0, -⟩` from `X.muH_haar u`. Use `haveI := hNsf`.

Use `haveI := hHsf`. Establish `hmul : Measurable (fun p : X.B.I.Ginf × X.B.I.Ginf => p.1 * p.2)` using `measurable_fst.mul measurable_snd`. Establish `hSmeas : MeasurableSet (X.SinfU u)` using `(Formalism.L2.SG.WuDecayPf.isClosed_sinfU X u).measurableSet`. Establish `hae : ∀ᵐ s ∂(((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)), s ∈ X.SinfU u`. Use `(ae_map_iff (p := fun s => s ∈ X.SinfU u) hmul.aemeasurable hSmeas).2 ?_` and prove the remaining obligations.

Establish `h1 : ∀ᵐ p ∂((X.muN u).prod (X.muH u)), p.1 ∈ X.NinfU u` using `Measure.quasiMeasurePreserving_fst.ae (p := fun s => s ∈ X.NinfU u) (by rw [ae_iff]; exact hN0)`. Establish `h2 : ∀ᵐ p ∂((X.muN u).prod (X.muH u)), p.2 ∈ Hset X.B.I (Set.range (fun c => crdOf X.B.I X.ιE X.bas (X.eX c)) ∪ Set.range (fun c => crdOf X.B.I X.ιE X.bas (X.fY c)) ∪ {crdOf X.B.I X.ιE X.bas (X.zu u)})` using `Measure.quasiMeasurePreserving_snd.ae (p := fun s => s ∈ Hset X.B.I (Set.range (fun c => crdOf X.B.I X.ιE X.bas (X.eX c)) ∪ Set.range (fun c => crdOf X.B.I X.ιE X.bas (X.fY c)) ∪ {crdOf X.B.I X.ιE X.bas (X.zu u)})) (by rw [ae_iff]; exact hH0)`. Use `filter_upwards [h1, h2] with p hp1 hp2`. Conclude with `Formalism.L2.SG.WuDecayPf.mul_mem_sinfU X u p.1 p.2 hp1 hp2`. Establish `hβprod : Measurable (fun x : X.B.I.Ginf => ∏ v, β v (x v))` using `Finset.measurable_prod _ fun v _ => (hβm v).comp (measurable_pi_apply v)`.

Establish `hWm : Measurable (fun x : X.B.I.Ginf => ‖X.Wu u x‖ₑ ^ 2)` using `(X.Wu_spec u).2.2.1.enorm.measurable.pow_const 2`. Establish `hfm : Measurable (fun x : X.B.I.Ginf => (∏ v, β v (x v)) * ‖X.Wu u x‖ₑ ^ 2)` using `hβprod.mul hWm`. Rewrite using `[X.nuQ_weil u _ hfm]`. Establish `hin : ∀ x : X.B.I.Ginf, ∫⁻ s, (∏ v, β v ((s * x) v)) * ‖X.Wu u (s * x)‖ₑ ^ 2 ∂(((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)) = κ * ‖X.Wu u x‖ₑ ^ 2`. Introduce `x`.

Establish `e1 : ∫⁻ s, (∏ v, β v ((s * x) v)) * ‖X.Wu u (s * x)‖ₑ ^ 2 ∂(((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)) = ∫⁻ s, (∏ v, β v ((s * x) v)) * ‖X.Wu u x‖ₑ ^ 2 ∂(((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2))`. Use `lintegral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [hae] with s hs`. Rewrite using `[← enorm_norm (X.Wu u (s * x)), Formalism.L2.SG.Pf.WuDec.norm_Wu_inv X u s hs x, enorm_norm]`. Rewrite using `[e1, lintegral_mul_const _ (show Measurable (fun s : X.B.I.Ginf => ∏ v, β v ((s * x) v)) from hβprod.comp (measurable_mul_const x)), hS, lintegral_smul_measure]`.

Establish `e2 : ∫⁻ s, ∏ v, β v ((s * x) v) ∂(Measure.pi M) = 1`. Establish `e3 : (fun s : X.B.I.Ginf => ∏ v, β v ((s * x) v)) = fun s => ∏ v, β v (s v * x v)` using `rfl`. Rewrite using `[e3, QPK.lintegral_fintype_prod (fun v s => β v (s * x v)) (fun v => (hβm v).comp (measurable_mul_const _))]`. Simplify using `[hβ1]`. Rewrite using `[e2, smul_eq_mul, mul_one]`.

Simplify using `only [hin]`. Rewrite using `[lintegral_const_mul _ hWm, (X.Wu_spec u).2.2.2.2, mul_one]`.
-/
theorem weil_bruhatProd_normSq : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (κ : ℝ≥0∞) (M : ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v))), (∀ v, SigmaFinite (M v)) → ((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2) = κ • Measure.pi M → ∀ (β : ∀ v : InfinitePlace X.B.I.F, Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞), (∀ v, Measurable (β v)) → (∀ v x, ∫⁻ s, β v (s * x) ∂(M v) = 1) → ∫⁻ x, (∏ v, β v (x v)) * ‖X.Wu u x‖ₑ ^ 2 ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) = κ := by
  intro D X u κ M hMs hS β hβm hβ1
  haveI := hMs
  obtain ⟨hNsf, -, hN0, -⟩ := X.muN_haar u
  obtain ⟨hHsf, -, hH0, -⟩ := X.muH_haar u
  haveI := hNsf
  haveI := hHsf
  have hmul : Measurable (fun p : X.B.I.Ginf × X.B.I.Ginf => p.1 * p.2) := measurable_fst.mul measurable_snd
  have hSmeas : MeasurableSet (X.SinfU u) := (Formalism.L2.SG.WuDecayPf.isClosed_sinfU X u).measurableSet
  have hae : ∀ᵐ s ∂(((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)), s ∈ X.SinfU u := by
    refine (ae_map_iff (p := fun s => s ∈ X.SinfU u) hmul.aemeasurable hSmeas).2 ?_
    have h1 : ∀ᵐ p ∂((X.muN u).prod (X.muH u)), p.1 ∈ X.NinfU u :=
      Measure.quasiMeasurePreserving_fst.ae (p := fun s => s ∈ X.NinfU u) (by rw [ae_iff]; exact hN0)
    have h2 : ∀ᵐ p ∂((X.muN u).prod (X.muH u)), p.2 ∈ Hset X.B.I
        (Set.range (fun c => crdOf X.B.I X.ιE X.bas (X.eX c)) ∪
          Set.range (fun c => crdOf X.B.I X.ιE X.bas (X.fY c)) ∪ {crdOf X.B.I X.ιE X.bas (X.zu u)}) :=
      Measure.quasiMeasurePreserving_snd.ae (p := fun s => s ∈ Hset X.B.I
        (Set.range (fun c => crdOf X.B.I X.ιE X.bas (X.eX c)) ∪
          Set.range (fun c => crdOf X.B.I X.ιE X.bas (X.fY c)) ∪ {crdOf X.B.I X.ιE X.bas (X.zu u)}))
        (by rw [ae_iff]; exact hH0)
    filter_upwards [h1, h2] with p hp1 hp2
    exact Formalism.L2.SG.WuDecayPf.mul_mem_sinfU X u p.1 p.2 hp1 hp2
  have hβprod : Measurable (fun x : X.B.I.Ginf => ∏ v, β v (x v)) :=
    Finset.measurable_prod _ fun v _ => (hβm v).comp (measurable_pi_apply v)
  have hWm : Measurable (fun x : X.B.I.Ginf => ‖X.Wu u x‖ₑ ^ 2) :=
    (X.Wu_spec u).2.2.1.enorm.measurable.pow_const 2
  have hfm : Measurable (fun x : X.B.I.Ginf => (∏ v, β v (x v)) * ‖X.Wu u x‖ₑ ^ 2) := hβprod.mul hWm
  rw [X.nuQ_weil u _ hfm]
  have hin : ∀ x : X.B.I.Ginf, ∫⁻ s, (∏ v, β v ((s * x) v)) * ‖X.Wu u (s * x)‖ₑ ^ 2
      ∂(((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)) = κ * ‖X.Wu u x‖ₑ ^ 2 := by
    intro x
    have e1 : ∫⁻ s, (∏ v, β v ((s * x) v)) * ‖X.Wu u (s * x)‖ₑ ^ 2
        ∂(((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)) =
        ∫⁻ s, (∏ v, β v ((s * x) v)) * ‖X.Wu u x‖ₑ ^ 2
          ∂(((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)) := by
      refine lintegral_congr_ae ?_
      filter_upwards [hae] with s hs
      rw [← enorm_norm (X.Wu u (s * x)), Formalism.L2.SG.Pf.WuDec.norm_Wu_inv X u s hs x, enorm_norm]
    rw [e1, lintegral_mul_const _ (show Measurable (fun s : X.B.I.Ginf => ∏ v, β v ((s * x) v)) from
      hβprod.comp (measurable_mul_const x)), hS, lintegral_smul_measure]
    have e2 : ∫⁻ s, ∏ v, β v ((s * x) v) ∂(Measure.pi M) = 1 := by
      have e3 : (fun s : X.B.I.Ginf => ∏ v, β v ((s * x) v)) = fun s => ∏ v, β v (s v * x v) := rfl
      rw [e3, QPK.lintegral_fintype_prod (fun v s => β v (s * x v))
        (fun v => (hβm v).comp (measurable_mul_const _))]
      simp [hβ1]
    rw [e2, smul_eq_mul, mul_one]
  simp only [hin]
  rw [lintegral_const_mul _ hWm, (X.Wu_spec u).2.2.2.2, mul_one]

end GlobalTheory
