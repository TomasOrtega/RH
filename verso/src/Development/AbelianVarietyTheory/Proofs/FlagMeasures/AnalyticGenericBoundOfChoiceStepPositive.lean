import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.StepLocGenPinnedGP
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqWire

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic
  Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna GlobalTheory.SnPos

namespace GlobalTheory.SnPos

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `Cg cb Cw cT CT C0 hcb hcT`. Take `⟨C1, C0n, hA1⟩` from `hA Cg cb Cw cT CT C0 hcb hcT`. Take `⟨k₀, l₀, hB2⟩` from `hB Cg cb Cw cT CT C0`. Take `⟨m₀, n₀, hT2⟩` from `hTi Cg cb Cw cT CT C0`. Use `⟨C1, C0n, fun A => ?_⟩` and prove the remaining obligations.

Take `⟨CB, CSt, h1, h2, a₀, b₀, hA2⟩` from `hA1 A`. Use `⟨CB, CSt, h1, h2, max a₀ (max k₀ m₀), max b₀ (max l₀ n₀), fun C' Cl e1 e2 D large₂ X Y u hD hc => ?_⟩` and prove the remaining obligations. Take `⟨hb, X0, ψ, hT⟩` from `hT2 C' Cl (le_trans (by simp) e1) (le_trans (by simp) e2) D large₂ X Y u u hc`. Take `⟨sd, C, Th, F0, what₂, vR, Q, i0, i0', νq, Irat, Ire, hBk⟩` from `hB2 C' Cl (le_trans (by simp) e1) (le_trans (by simp) e2) D large₂ X Y u u hc hb X0 ψ hT`. Establish `hBk'` using `massDataValid_unscale (kapU_pos D) hBk`.

Take `⟨νL, νB, ng, cSt, e, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩` from `hA2 C' Cl (le_trans (by simp) e1) (le_trans (by simp) e2) D large₂ X Y u hD hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq (Irat * kapU D) (Ire * kapU D) hBk'`. Conclude with `⟨_, inferInstance, _, Irat * kapU D, Ire * kapU D, νL, νB, ng, cSt, e, hBk', a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩`.
-/
theorem stepAnalyticGP_of (hTi : TieOfCtx) (hB : StepChoiceConstantsC) (hA : StepAnalyticCGP) : StepAnalyticGP := by
  intro Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨C1, C0n, hA1⟩ := hA Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨k₀, l₀, hB2⟩ := hB Cg cb Cw cT CT C0
  obtain ⟨m₀, n₀, hT2⟩ := hTi Cg cb Cw cT CT C0
  refine ⟨C1, C0n, fun A => ?_⟩
  obtain ⟨CB, CSt, h1, h2, a₀, b₀, hA2⟩ := hA1 A
  refine ⟨CB, CSt, h1, h2, max a₀ (max k₀ m₀), max b₀ (max l₀ n₀), fun C' Cl e1 e2 D large₂ X Y u hD hc => ?_⟩
  obtain ⟨hb, X0, ψ, hT⟩ := hT2 C' Cl (le_trans (by simp) e1) (le_trans (by simp) e2) D large₂ X Y u u hc
  obtain ⟨sd, C, Th, F0, what₂, vR, Q, i0, i0', νq, Irat, Ire, hBk⟩ :=
    hB2 C' Cl (le_trans (by simp) e1) (le_trans (by simp) e2) D large₂ X Y u u hc hb X0 ψ hT
  have hBk' := massDataValid_unscale (kapU_pos D) hBk
  obtain ⟨νL, νB, ng, cSt, e, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ :=
    hA2 C' Cl (le_trans (by simp) e1) (le_trans (by simp) e2) D large₂ X Y u hD hc hb X0 ψ hT sd C Th
      F0 what₂ vR Q i0 i0' νq (Irat * kapU D) (Ire * kapU D) hBk'
  exact ⟨_, inferInstance, _, Irat * kapU D, Ire * kapU D, νL, νB, ng, cSt, e, hBk', a1, a2, a3, a4, a5, a6, a7,
    a8, a9, a10, a11⟩

end GlobalTheory.SnPos
