import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.StepLocGenPinnedGP
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqWire

noncomputable section

open scoped Classical
open Formalism.FourierDecayAlt Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna GlobalTheory.SnPos

namespace GlobalTheory.SnPos

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `Cg cb Cw cT CT C0 A0 hcb hcT`. Take `⟨C1, C0n, hA1⟩` from `hA Cg cb Cw cT CT C0 hcb hcT`. Take `⟨CB, CSt, hCB, hCSt, a₀, b₀, hA2⟩` from `hA1 (C1 + C0n + 38)`. Take `⟨Cgs, CTs, hCg, hCT, s₀, t₀, hS2⟩` from `hS Cg cb Cw cT CT C0`. Take `⟨n₀, m₀, hN2⟩` from `hN Cg cb Cw cT CT C0`.

Take `⟨p₀, q₀, hP2⟩` from `hP Cg cb Cw cT CT C0`. Take `⟨h₀, j₀, hH2⟩` from `hH Cg cb Cw cT CT C0`. Use `⟨C1, C0n, C1 + C0n + 38, CB, CSt, Cgs, CTs, hCB, hCSt, hCg, hCT, le_refl _, max a₀ (max s₀ (max n₀ (max p₀ h₀))), max b₀ (max t₀ (max m₀ (max q₀ j₀))), fun C' Cl h1 h2 D large₂ X Y u hTies hHy hT => ?_⟩` and prove the remaining obligations. Establish `hc : Formalism.L2.SG.NGCut.Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u` using `⟨hHy.1, hHy.2.1, hT⟩`. Establish `e1' : a₀ ≤ C'` using `le_trans (le_max_left _ _) h1`.

Establish `e2' : b₀ ≤ Cl` using `le_trans (le_max_left _ _) h2`. Establish `f1 : s₀ ≤ C'` using `le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) h1`. Establish `f2 : t₀ ≤ Cl` using `le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) h2`. Establish `i1 : n₀ ≤ C'` using `le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) h1`. Establish `i2 : m₀ ≤ Cl` using `le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) h2`.

Establish `j1 : p₀ ≤ C'` using `le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))) h1`. Establish `j2 : q₀ ≤ Cl` using `le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))) h2`. Establish `k1 : h₀ ≤ C'` using `le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))) h1`. Establish `k2 : j₀ ≤ Cl` using `le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))) h2`. Take `⟨P, iP, B, Irat, Ire, νL, νB, ng, cSt, e1, hBk, hL, hBq, c1, c2, c3, c4, hV, hLoc, hGen, hMeas, hSum⟩` from `hA2 C' Cl e1' e2' D large₂ X Y u hTies hc`.

Take `⟨hG, hdd, hNI, hFI⟩` from `hBk`. Use `⟨P, iP, B, cSt, e1, Irat, Ire, νL, νB, ng, hL, hBq, hG, hdd, hNI, hFI, Formalism.L2.SG.NGCut.ngSizes_of (hS2 C' Cl f1 f2 D large₂ X Y u u hc) c1 c2 c3 c4, ?_⟩` and prove the remaining obligations. Conclude with `⟨classInputG_of Y u (hC D X Y u (g_ge_three hc) hT) νL νB ng, ampInputG_of_vanish Y u νL νB ng hV, hN2 C' Cl i1 i2 D large₂ X Y u hc νL νB ng, hP2 C' Cl j1 j2 D large₂ X Y u hc νL νB ng, hLoc, hMeas, hGen, hH2 C' Cl k1 k2 D large₂ X Y u hc νL νB ng, hSum⟩`.
-/
theorem genCutP_of_steps (hS : StepSizes) (hC : StepClassG) (hN : StepNormalsG) (hP : StepPointsG)
    (hH : StepHeightG) (hA : StepAnalyticGP) : GenCutP := by
  intro Cg cb Cw cT CT C0 A0 hcb hcT
  obtain ⟨C1, C0n, hA1⟩ := hA Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨CB, CSt, hCB, hCSt, a₀, b₀, hA2⟩ := hA1 (C1 + C0n + 38)
  obtain ⟨Cgs, CTs, hCg, hCT, s₀, t₀, hS2⟩ := hS Cg cb Cw cT CT C0
  obtain ⟨n₀, m₀, hN2⟩ := hN Cg cb Cw cT CT C0
  obtain ⟨p₀, q₀, hP2⟩ := hP Cg cb Cw cT CT C0
  obtain ⟨h₀, j₀, hH2⟩ := hH Cg cb Cw cT CT C0
  refine ⟨C1, C0n, C1 + C0n + 38, CB, CSt, Cgs, CTs, hCB, hCSt, hCg, hCT, le_refl _,
    max a₀ (max s₀ (max n₀ (max p₀ h₀))), max b₀ (max t₀ (max m₀ (max q₀ j₀))),
    fun C' Cl h1 h2 D large₂ X Y u hTies hHy hT => ?_⟩
  have hc : Formalism.L2.SG.NGCut.Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u := ⟨hHy.1, hHy.2.1, hT⟩
  have e1' : a₀ ≤ C' := le_trans (le_max_left _ _) h1
  have e2' : b₀ ≤ Cl := le_trans (le_max_left _ _) h2
  have f1 : s₀ ≤ C' := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) h1
  have f2 : t₀ ≤ Cl := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) h2
  have i1 : n₀ ≤ C' :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) h1
  have i2 : m₀ ≤ Cl :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) h2
  have j1 : p₀ ≤ C' := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))) h1
  have j2 : q₀ ≤ Cl := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))) h2
  have k1 : h₀ ≤ C' := le_trans (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))) h1
  have k2 : j₀ ≤ Cl := le_trans (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))) h2
  obtain ⟨P, iP, B, Irat, Ire, νL, νB, ng, cSt, e1, hBk, hL, hBq, c1, c2, c3, c4, hV, hLoc, hGen, hMeas, hSum⟩ :=
    hA2 C' Cl e1' e2' D large₂ X Y u hTies hc
  obtain ⟨hG, hdd, hNI, hFI⟩ := hBk
  refine ⟨P, iP, B, cSt, e1, Irat, Ire, νL, νB, ng, hL, hBq, hG, hdd, hNI, hFI,
    Formalism.L2.SG.NGCut.ngSizes_of (hS2 C' Cl f1 f2 D large₂ X Y u u hc) c1 c2 c3 c4, ?_⟩
  exact ⟨classInputG_of Y u (hC D X Y u (g_ge_three hc) hT) νL νB ng, ampInputG_of_vanish Y u νL νB ng hV,
    hN2 C' Cl i1 i2 D large₂ X Y u hc νL νB ng, hP2 C' Cl j1 j2 D large₂ X Y u hc νL νB ng, hLoc, hMeas, hGen,
    hH2 C' Cl k1 k2 D large₂ X Y u hc νL νB ng, hSum⟩

end GlobalTheory.SnPos
