import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGVanish
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.StepAnalyticConstantsP

noncomputable section

open scoped Classical
open Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic GlobalTheory.NGRow

namespace GlobalTheory.NGRow

/- English proof (translation)
Introduce `Cg cb Cw cT CT C0 hcb hcT`. Take `⟨C1, C0n, hA1⟩` from `hA Cg cb Cw cT CT C0 hcb hcT`. Take `⟨k₀, l₀, hB2⟩` from `hB Cg cb Cw cT CT C0`. Take `⟨m₀, n₀, hT2⟩` from `hTi Cg cb Cw cT CT C0`. Use `⟨C1, C0n, fun A => ?_⟩` and prove the remaining obligations.

Take `⟨CB, CSt, h1, h2, a₀, b₀, hA2⟩` from `hA1 A`. Use `⟨CB, CSt, h1, h2, max a₀ (max k₀ m₀), max b₀ (max l₀ n₀), fun C' Cl e1 e2 D large₂ X Y u u' hTies hc => ?_⟩` and prove the remaining obligations. Take `⟨hb, X0, ψ, hT⟩` from `hT2 C' Cl (le_trans (by simp) e1) (le_trans (by simp) e2) D large₂ X Y u u' hc`. Take `⟨sd, C, Th, F0, what₂, vR, Q, i0, i0', νq, Irat, Ire, hBk⟩` from `hB2 C' Cl (le_trans (by simp) e1) (le_trans (by simp) e2) D large₂ X Y u u' hc hb X0 ψ hT`. Establish `hBk'` using `massDataValid_unscale (kapU_pos D) hBk`.

Conclude with `⟨_, inferInstance, _, Irat * kapU D, Ire * kapU D, hBk', hA2 C' Cl (le_trans (by simp) e1) (le_trans (by simp) e2) D large₂ X Y u u' hTies hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq (Irat * kapU D) (Ire * kapU D) hBk'⟩`.
-/
theorem exists_row_level_analytic (hTi : TieOfCtx) (hB : StepChoiceConstantsC) (hA : StepAnalyticP) : StepAnalyticConstantsP := by
  intro Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨C1, C0n, hA1⟩ := hA Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨k₀, l₀, hB2⟩ := hB Cg cb Cw cT CT C0
  obtain ⟨m₀, n₀, hT2⟩ := hTi Cg cb Cw cT CT C0
  refine ⟨C1, C0n, fun A => ?_⟩
  obtain ⟨CB, CSt, h1, h2, a₀, b₀, hA2⟩ := hA1 A
  refine ⟨CB, CSt, h1, h2, max a₀ (max k₀ m₀), max b₀ (max l₀ n₀),
    fun C' Cl e1 e2 D large₂ X Y u u' hTies hc => ?_⟩
  obtain ⟨hb, X0, ψ, hT⟩ := hT2 C' Cl (le_trans (by simp) e1) (le_trans (by simp) e2) D large₂ X Y u u' hc
  obtain ⟨sd, C, Th, F0, what₂, vR, Q, i0, i0', νq, Irat, Ire, hBk⟩ :=
    hB2 C' Cl (le_trans (by simp) e1) (le_trans (by simp) e2) D large₂ X Y u u' hc hb X0 ψ hT
  have hBk' := massDataValid_unscale (kapU_pos D) hBk
  exact ⟨_, inferInstance, _, Irat * kapU D, Ire * kapU D, hBk',
    hA2 C' Cl (le_trans (by simp) e1) (le_trans (by simp) e2) D large₂ X Y u u' hTies hc hb X0 ψ hT sd C Th
      F0 what₂ vR Q i0 i0' νq (Irat * kapU D) (Ire * kapU D) hBk'⟩

end GlobalTheory.NGRow
