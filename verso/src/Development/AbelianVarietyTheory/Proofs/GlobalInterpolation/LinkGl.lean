import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.TuSizeOfRealPlaceSecondLayer
import Formalism.SharpRestriction.GlobalSchurBounds.LogXLowerFamilyOfTheorems
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermRepUnram
import Formalism.LocalToGlobal.TieTwRecOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.JoinSISel

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT Formalism.L2.Top3 Formalism.L2.Top4

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Introduce `𝒜 hduty tie hU hG`. Establish `hC0 : (3 : ℝ) ≤ 3` using `le_refl _`. Establish `hC0' : (0 : ℝ) < 3` using `by norm_num`. Establish `hCe : Real.exp 1 ≤ 3` using `le_trans (le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))) hC0`. Establish `hCabs : (0 : ℝ) ≤ 2` using `by norm_num`.

Use `haveI : Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram := ⟨GlobalTheory.hermRepUnram⟩`. Establish `hGLm` using `Formalism.MainNotions.Wire.famGLmin_of_realPlaceSecondLayer (D3 3 𝒜) tie hU hG`. Establish `hRk : Closed (D3 3 𝒜) fun Fm CH => ChosenE Fm 3 CH → NuFullF Fm ∧ J.MuRank Fm` using `((hGLm.muRank 3 hC0').and (Closed.of_class (P := fun Fm _ => TuSize Fm) fun _ _ hc => hc.2.2.1)).imp fun _ _ _ h c => h.1 h.2 c`. Establish `hGL : Closed (D3 3 𝒜) fun Fm CH => TuSize Fm → DGamSize Fm → LinkGLOBAL Fm 2 CH 3 2 0` using `hGLm.link8 2 3 hCabs hC0 fun Fm hc => (hduty Fm (d3_a hc)).2.2.2.2.1`. Conclude with `⟨hRk, hGL⟩`.
-/
theorem GlobalTheory.Top.link_gl : ∀ (𝒜 : FamClass)
    (hduty : ∀ {eps : ℝ} (Fm : FamP eps), 𝒜 Fm → Duty Fm)
    (tie : Closed (D3 3 𝒜) fun Fm _ => RealPlaceSecondLayerConditions Fm)
    (hU : ∀ D, MassRatioUnderVolume D)
    (hG : ∀ D, GenusMassVolumes.GenusMassAt D 2), (Closed (D3 3 𝒜) fun Fm CH => ChosenE Fm 3 CH → NuFullF Fm ∧ J.MuRank Fm) ∧ (Closed (D3 3 𝒜) fun Fm CH => TuSize Fm → DGamSize Fm → LinkGLOBAL Fm 2 CH 3 2 0) := by
  intro 𝒜 hduty tie hU hG
  have hC0 : (3 : ℝ) ≤ 3 := le_refl _
  have hC0' : (0 : ℝ) < 3 := by norm_num
  have hCe : Real.exp 1 ≤ 3 := le_trans (le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))) hC0
  have hCabs : (0 : ℝ) ≤ 2 := by norm_num
  haveI : Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram := ⟨GlobalTheory.hermRepUnram⟩
  have hGLm := Formalism.MainNotions.Wire.famGLmin_of_realPlaceSecondLayer (D3 3 𝒜) tie hU hG
  have hRk : Closed (D3 3 𝒜) fun Fm CH => ChosenE Fm 3 CH → NuFullF Fm ∧ J.MuRank Fm :=
    ((hGLm.muRank 3 hC0').and
      (Closed.of_class (P := fun Fm _ => TuSize Fm) fun _ _ hc => hc.2.2.1)).imp fun _ _ _ h c => h.1 h.2 c
  have hGL : Closed (D3 3 𝒜) fun Fm CH => TuSize Fm → DGamSize Fm → LinkGLOBAL Fm 2 CH 3 2 0 :=
    hGLm.link8 2 3 hCabs hC0 fun Fm hc => (hduty Fm (d3_a hc)).2.2.2.2.1
  exact ⟨hRk, hGL⟩

end
