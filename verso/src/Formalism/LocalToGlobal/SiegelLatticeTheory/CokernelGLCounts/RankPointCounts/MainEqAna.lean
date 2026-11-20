import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqSteps
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic
  Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps

namespace Formalism.L2.SG.Pf.MainEqAna

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def AnaAtG (CSt CB : ℝ) (C1 C0n A : ℕ) {D : D7} (large₂ : SizeData₂ D) {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word)
    {P : Type} [Fintype P] (B : S3.MassData P) (Ire : ℝ) : Prop :=
  ∃ (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ) (cSt e1 : ℝ),
    Formalism.L2.SG.RealObj.NuQOK X u u νL ∧ Formalism.L2.SG.RealObj.NuQOK X u u νB ∧
    0 ≤ cSt ∧ cSt ≤ large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f) ∧ 0 ≤ e1 ∧ e1 ≤ 2 ∧
    AmpVanishG Y u νL ∧
    LocalInputG (genT (Y.tO u u)) (NOfG Y u νL νB ng) C1 C0n ∧
    PN.GenMassInput (genT (Y.tO u u)) (NOfG Y u νL νB ng) (PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * B.AA) e1 ∧
    PN.MeasureInput (genT (Y.tO u u)) (NOfG Y u νL νB ng) cSt ∧
    PN.PointSumInput (genT (Y.tO u u)) (NOfG Y u νL νB ng) (A * (D.R.rS + 1) ^ 2)
      (Real.exp (CB * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5 * D.R.f * Real.log large₂.sc.b) * Ire)

def StepAnalyticCG : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C1 C0n : ℕ, ∀ A : ℕ, ∃ CB CSt : ℝ, 0 ≤ CB ∧ 0 ≤ CSt ∧
    ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u →
      ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
        (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ →
      ∀ (sd C Th : ℝ) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
        (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
        (vR : Formalism.L2.SG.TermDef.Term D u u F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u F0 what₂)
        (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (Irat Ire : ℝ),
        MassDataAdmissible X Y u u (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq) Irat Ire →
        AnaAtG CSt CB C1 C0n A large₂ Y u (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq) Ire

section Pin

variable {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word)

/- English proof (translation)
Simplify using `only [Jw, OO, sc, Measure.restrict_smul, integral_smul_measure, ENNReal.coe_toReal]`. Rewrite using `[smul_comm]`.
-/
private theorem Jw_sc_eq_smul {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word) (s : X.B.I.Ginf → NNReal)
    (ν : X.B.I.Ginf → Measure X.B.I.Ginf) (w : Point D.host.E (D.R.rS + 1)) :
    Jw Y u u (sc s ν) w = ((s (RealObj.gamW X u u w) : NNReal) : ℝ) • Jw Y u u ν w := by
  simp only [Jw, OO, sc, Measure.restrict_smul, integral_smul_measure, ENNReal.coe_toReal]
  rw [smul_comm]

/- English proof (translation)
Introduce `c γ ν' hJ`. Use `h c γ ν' ?_` and prove the remaining obligations. Unfold `J2of at hJ ⊢`. Use `split_ifs at hJ ⊢ with hc`. Rewrite `hJ` using `[Jw_sc_eq_smul, LinearMap.map_smul_of_tower, norm_smul, mul_pow]`.

Break down `mul_eq_zero.mp hJ with h1 | h1` into its components or cases. It suffices to derive a contradiction. Establish `hp : (0 : ℝ) < ((s (RealObj.gamW X u u hc.choose) : NNReal) : ℝ)` using `hs _`. Establish `: (0 : ℝ) < ‖((s (RealObj.gamW X u u hc.choose) : NNReal) : ℝ)‖ ^ 2` using `pow_pos (norm_pos_iff.mpr hp.ne') 2`. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `h1`. Both sides reduce to the same expression.
-/
theorem ampVanishG_sc (s : X.B.I.Ginf → NNReal) (hs : ∀ γ, 0 < s γ) (ν : X.B.I.Ginf → Measure X.B.I.Ginf)
    (h : AmpVanishG Y u ν) : AmpVanishG Y u (sc s ν) := by
  intro c γ ν' hJ
  refine h c γ ν' ?_
  unfold J2of at hJ ⊢
  split_ifs at hJ ⊢ with hc
  · rw [Jw_sc_eq_smul, LinearMap.map_smul_of_tower, norm_smul, mul_pow] at hJ
    rcases mul_eq_zero.mp hJ with h1 | h1
    · exfalso
      have hp : (0 : ℝ) < ((s (RealObj.gamW X u u hc.choose) : NNReal) : ℝ) := hs _
      have : (0 : ℝ) < ‖((s (RealObj.gamW X u u hc.choose) : NNReal) : ℝ)‖ ^ 2 :=
        pow_pos (norm_pos_iff.mpr hp.ne') 2
      linarith
    · exact h1
  · rfl

/- English proof (translation)
Introduce `γ _`. Simplify using `only [NOfG]`. Unfold `J2of`. Use `split_ifs with hc`. Rewrite using `[Jw_sc_eq_smul, LinearMap.map_smul_of_tower, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]`.

Conclude with `⟨by positivity, mul_le_mul_of_nonneg_right (hs _) (by positivity)⟩`. Simplify using the standard rewrite rules.
-/
theorem measureInputG_sc (s : X.B.I.Ginf → NNReal) (ν : X.B.I.Ginf → Measure X.B.I.Ginf) (c : ℝ)
    (hs : ∀ γ, (s γ : ℝ) ^ 2 ≤ c) (ng : PN.Pts D.host.E D.R.rS → ℝ) :
    PN.MeasureInput (genT (Y.tO u u)) (NOfG Y u (sc s ν) ν ng) c := by
  intro γ _
  simp only [NOfG]
  unfold J2of
  split_ifs with hc
  · rw [Jw_sc_eq_smul, LinearMap.map_smul_of_tower, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    exact ⟨by positivity, mul_le_mul_of_nonneg_right (hs _) (by positivity)⟩
  · simp

/- English proof (translation)
Introduce `c γ ν' hJ`. Unfold `grpGC`. Use `(tsum_congr fun t => ?_).trans tsum_zero` and prove the remaining obligations. Distinguish the cases in `ht : t ∈ (Y.tO u u).genSet ∩ {t | clsG Y u t = c ∧ ptPN t = γ ∧ nmlOf Y u u t = ν'}`. Rewrite using `[Set.indicator_of_mem ht]`.

Conclude with `h t ht.1 (by rw [ht.2.2.1]; exact hJ)`. Simplify using `[Set.indicator, ht]`.
-/
theorem ampVanishG_of_term (ν : X.B.I.Ginf → Measure X.B.I.Ginf)
    (h : ∀ t ∈ (Y.tO u u).genSet, J2of Y u u ν (ptPN t) = 0 → (Y.tO u u).vec t = 0) : AmpVanishG Y u ν := by
  intro c γ ν' hJ
  unfold grpGC
  refine (tsum_congr fun t => ?_).trans tsum_zero
  by_cases ht : t ∈ (Y.tO u u).genSet ∩ {t | clsG Y u t = c ∧ ptPN t = γ ∧ nmlOf Y u u t = ν'}
  · rw [Set.indicator_of_mem ht]
    exact h t ht.1 (by rw [ht.2.2.1]; exact hJ)
  · simp [Set.indicator, ht]

end Pin

def StepTermVanishG : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u →
      ∀ ν, Pinned X u u ν → ∀ t ∈ (Y.tO u u).genSet, J2of Y u u ν (ptPN t) = 0 → (Y.tO u u).vec t = 0

def StepLocGenPinnedG : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C1 C0n : ℕ, ∃ CSt : ℝ, 0 ≤ CSt ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u →
      ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
        (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ →
      ∀ (sd C Th : ℝ) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
        (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
        (vR : Formalism.L2.SG.TermDef.Term D u u F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u F0 what₂)
        (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (Irat Ire : ℝ),
        MassDataAdmissible X Y u u (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq) Irat Ire →
      ∀ ν, Pinned X u u ν →
      ∃ (s : X.B.I.Ginf → NNReal) (ng : PN.Pts D.host.E D.R.rS → ℝ) (e1 : ℝ),
        (∀ γ, Formalism.L2.SG.RealObj.RegX X u u γ → s γ = 1) ∧ (∀ γ, 0 < s γ) ∧
        (∀ γ, (s γ : ℝ) ^ 2 ≤ large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f)) ∧ 0 ≤ e1 ∧ e1 ≤ 2 ∧
        LocalInputG (genT (Y.tO u u)) (NOfG Y u (sc s ν) ν ng) C1 C0n ∧
        PN.GenMassInput (genT (Y.tO u u)) (NOfG Y u (sc s ν) ν ng)
          (PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq).AA) e1

def StepThmBPinnedG : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∀ A : ℕ, ∃ CB : ℝ, 0 ≤ CB ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u →
      ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
        (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ →
      ∀ (sd C Th : ℝ) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
        (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
        (vR : Formalism.L2.SG.TermDef.Term D u u F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u F0 what₂)
        (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (Irat Ire : ℝ),
        MassDataAdmissible X Y u u (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq) Irat Ire →
      ∀ ν, Pinned X u u ν → ∀ (νL : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ),
        PN.PointSumInput (genT (Y.tO u u)) (NOfG Y u νL ν ng) (A * (D.R.rS + 1) ^ 2)
          (Real.exp (CB * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5 * D.R.f * Real.log large₂.sc.b) * Ire)

end Formalism.L2.SG.Pf.MainEqAna

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.MainEqAna

/- English proof (translation)
Introduce `Cg cb Cw cT CT C0`. Take `⟨C1, C0n, hA1⟩` from `hA Cg cb Cw cT CT C0`. Take `⟨k₀, l₀, hB2⟩` from `hB Cg cb Cw cT CT C0`. Take `⟨m₀, n₀, hT2⟩` from `hTi Cg cb Cw cT CT C0`. Use `⟨C1, C0n, fun A => ?_⟩` and prove the remaining obligations.

Take `⟨CB, CSt, h1, h2, a₀, b₀, hA2⟩` from `hA1 A`. Use `⟨CB, CSt, h1, h2, max a₀ (max k₀ m₀), max b₀ (max l₀ n₀), fun C' Cl e1 e2 D large₂ X Y u hc => ?_⟩` and prove the remaining obligations. Take `⟨hb, X0, ψ, hT⟩` from `hT2 C' Cl (le_trans (by simp) e1) (le_trans (by simp) e2) D large₂ X Y u u hc`. Take `⟨sd, C, Th, F0, what₂, vR, Q, i0, i0', νq, Irat, Ire, hBk⟩` from `hB2 C' Cl (le_trans (by simp) e1) (le_trans (by simp) e2) D large₂ X Y u u hc hb X0 ψ hT`. Establish `hBk'` using `massDataValid_unscale (kapU_pos D) hBk`.

Take `⟨νL, νB, ng, cSt, e, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩` from `hA2 C' Cl (le_trans (by simp) e1) (le_trans (by simp) e2) D large₂ X Y u hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq (Irat * kapU D) (Ire * kapU D) hBk'`. Conclude with `⟨_, inferInstance, _, Irat * kapU D, Ire * kapU D, νL, νB, ng, cSt, e, hBk', a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩`.
-/
theorem stepAnalyticG_of (hTi : TieOfCtx) (hB : StepChoiceConstantsC) (hA : StepAnalyticCG) : StepAnalyticG := by
  intro Cg cb Cw cT CT C0
  obtain ⟨C1, C0n, hA1⟩ := hA Cg cb Cw cT CT C0
  obtain ⟨k₀, l₀, hB2⟩ := hB Cg cb Cw cT CT C0
  obtain ⟨m₀, n₀, hT2⟩ := hTi Cg cb Cw cT CT C0
  refine ⟨C1, C0n, fun A => ?_⟩
  obtain ⟨CB, CSt, h1, h2, a₀, b₀, hA2⟩ := hA1 A
  refine ⟨CB, CSt, h1, h2, max a₀ (max k₀ m₀), max b₀ (max l₀ n₀), fun C' Cl e1 e2 D large₂ X Y u hc => ?_⟩
  obtain ⟨hb, X0, ψ, hT⟩ := hT2 C' Cl (le_trans (by simp) e1) (le_trans (by simp) e2) D large₂ X Y u u hc
  obtain ⟨sd, C, Th, F0, what₂, vR, Q, i0, i0', νq, Irat, Ire, hBk⟩ :=
    hB2 C' Cl (le_trans (by simp) e1) (le_trans (by simp) e2) D large₂ X Y u u hc hb X0 ψ hT
  have hBk' := massDataValid_unscale (kapU_pos D) hBk
  obtain ⟨νL, νB, ng, cSt, e, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ :=
    hA2 C' Cl (le_trans (by simp) e1) (le_trans (by simp) e2) D large₂ X Y u hc hb X0 ψ hT sd C Th
      F0 what₂ vR Q i0 i0' νq (Irat * kapU D) (Ire * kapU D) hBk'
  exact ⟨_, inferInstance, _, Irat * kapU D, Ire * kapU D, νL, νB, ng, cSt, e, hBk', a1, a2, a3, a4, a5, a6, a7,
    a8, a9, a10, a11⟩

/- English proof (translation)
Introduce `γ`. Take `⟨h1, μR, hH, hQ⟩` from `h γ`. Use `⟨fun hr => ?_, (s γ)⁻¹ • μR, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [sc, hreg γ hr, ENNReal.coe_one, one_smul]`. Conclude with `h1 hr`.

Take `⟨hσ, h0, hc, hm⟩` from `hH`. Use `⟨inferInstance, smul_ne_zero (inv_ne_zero (hs γ).ne') h0, ?_, ?_⟩` and prove the remaining obligations. Simplify using `[hc]`. Introduce `g hg`. Rewrite using `[Measure.map_smul, hm g hg]`.

Introduce `f hf`. Rewrite using `[hQ f hf]`. Simplify using `only [sc, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]`. Rewrite using `[lintegral_const_mul' _ _ ENNReal.coe_ne_top, ← mul_assoc, ← ENNReal.coe_mul, mul_inv_cancel₀ (hs γ).ne', ENNReal.coe_one, one_mul]`.
-/
private theorem nuQOK_sc_of_eq_one_on_regX {D : D7} {X : HidaSetting D} (u : D.what₂.Word) (s : X.B.I.Ginf → NNReal)
    (hs : ∀ γ, 0 < s γ) (ν : X.B.I.Ginf → Measure X.B.I.Ginf)
    (hreg : ∀ γ, Formalism.L2.SG.RealObj.RegX X u u γ → s γ = 1) (h : Formalism.L2.SG.RealObj.NuQOK X u u ν) :
    Formalism.L2.SG.RealObj.NuQOK X u u (sc s ν) := by
  intro γ
  obtain ⟨h1, μR, hH, hQ⟩ := h γ
  refine ⟨fun hr => ?_, (s γ)⁻¹ • μR, ?_, ?_⟩
  · simp only [sc, hreg γ hr, ENNReal.coe_one, one_smul]
    exact h1 hr
  · obtain ⟨hσ, h0, hc, hm⟩ := hH
    refine ⟨inferInstance, smul_ne_zero (inv_ne_zero (hs γ).ne') h0, ?_, ?_⟩
    · simp [hc]
    · intro g hg
      rw [Measure.map_smul, hm g hg]
  · intro f hf
    rw [hQ f hf]
    simp only [sc, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
    rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, ← mul_assoc, ← ENNReal.coe_mul,
      mul_inv_cancel₀ (hs γ).ne', ENNReal.coe_one, one_mul]

/- English proof (translation)
Introduce `Cg cb Cw cT CT C0`. Take `⟨aE, bE, hE'⟩` from `hE Cg cb Cw cT CT C0`. Take `⟨aV, bV, hV'⟩` from `hV Cg cb Cw cT CT C0`. Take `⟨C1, C0n, CSt, hCSt, aL, bL, hL'⟩` from `hL Cg cb Cw cT CT C0`. Use `⟨C1, C0n, fun A => ?_⟩` and prove the remaining obligations.

Take `⟨CB, hCB, aT, bT, hT'⟩` from `hB Cg cb Cw cT CT C0 A`. Use `⟨CB, CSt, hCB, hCSt, max (max aE aV) (max aL aT), max (max bE bV) (max bL bT), ?_⟩` and prove the remaining obligations. Introduce `C' Cl hC' hCl D large₂ X Y u hctx hb X0 ψ htie sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hok`. Establish `hE1 : aE ≤ C'` using `le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hC'`. Establish `hE2 : bE ≤ Cl` using `le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hCl`.

Establish `hV1 : aV ≤ C'` using `le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hC'`. Establish `hV2 : bV ≤ Cl` using `le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hCl`. Establish `hL1 : aL ≤ C'` using `le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC'`. Establish `hL2 : bL ≤ Cl` using `le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCl`. Establish `hT1 : aT ≤ C'` using `le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC'`.

Establish `hT2 : bT ≤ Cl` using `le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCl`. Take `⟨ν, hν⟩` from `hE' C' Cl hE1 hE2 D large₂ X Y u u hctx`. Take `⟨s, ng, e1, hreg, hpos, hsq, he0, he2, hloc, hmass⟩` from `hL' C' Cl hL1 hL2 D large₂ X Y u hctx hb X0 ψ htie sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hok ν hν`. Establish `hpt` using `hT' C' Cl hT1 hT2 D large₂ X Y u hctx hb X0 ψ htie sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hok ν hν (sc s ν) ng`. Establish `hvan` using `hV' C' Cl hV1 hV2 D large₂ X Y u hctx ν hν`.

Use `⟨sc s ν, ν, ng, large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f), e1, nuQOK_sc_of_eq_one_on_regX u s hpos ν hreg hν.1, hν.1, le_trans (sq_nonneg _) (hsq 1), le_rfl, he0, he2, ampVanishG_sc Y u s hpos ν (ampVanishG_of_term Y u ν hvan), hloc, hmass, measureInputG_sc Y u …` and prove the remaining obligations.
-/
theorem stepAnalyticCG_of_pin_vanish_loc_thm (hE : StepPinExists) (hV : StepTermVanishG) (hL : StepLocGenPinnedG)
    (hB : StepThmBPinnedG) : StepAnalyticCG := by
  intro Cg cb Cw cT CT C0
  obtain ⟨aE, bE, hE'⟩ := hE Cg cb Cw cT CT C0
  obtain ⟨aV, bV, hV'⟩ := hV Cg cb Cw cT CT C0
  obtain ⟨C1, C0n, CSt, hCSt, aL, bL, hL'⟩ := hL Cg cb Cw cT CT C0
  refine ⟨C1, C0n, fun A => ?_⟩
  obtain ⟨CB, hCB, aT, bT, hT'⟩ := hB Cg cb Cw cT CT C0 A
  refine ⟨CB, CSt, hCB, hCSt, max (max aE aV) (max aL aT), max (max bE bV) (max bL bT), ?_⟩
  intro C' Cl hC' hCl D large₂ X Y u hctx hb X0 ψ htie sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hok
  have hE1 : aE ≤ C' := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hC'
  have hE2 : bE ≤ Cl := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hCl
  have hV1 : aV ≤ C' := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hC'
  have hV2 : bV ≤ Cl := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hCl
  have hL1 : aL ≤ C' := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC'
  have hL2 : bL ≤ Cl := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCl
  have hT1 : aT ≤ C' := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC'
  have hT2 : bT ≤ Cl := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCl
  obtain ⟨ν, hν⟩ := hE' C' Cl hE1 hE2 D large₂ X Y u u hctx
  obtain ⟨s, ng, e1, hreg, hpos, hsq, he0, he2, hloc, hmass⟩ :=
    hL' C' Cl hL1 hL2 D large₂ X Y u hctx hb X0 ψ htie sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hok ν hν
  have hpt := hT' C' Cl hT1 hT2 D large₂ X Y u hctx hb X0 ψ htie sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hok ν hν
    (sc s ν) ng
  have hvan := hV' C' Cl hV1 hV2 D large₂ X Y u hctx ν hν
  refine ⟨sc s ν, ν, ng, large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f), e1,
    nuQOK_sc_of_eq_one_on_regX u s hpos ν hreg hν.1, hν.1, le_trans (sq_nonneg _) (hsq 1), le_rfl, he0, he2,
    ampVanishG_sc Y u s hpos ν (ampVanishG_of_term Y u ν hvan), hloc, hmass,
    measureInputG_sc Y u s ν _ hsq ng, hpt⟩

/- English proof (translation)
The claim follows from `rowMainEqC_of_steps2 hCh hC hN hP hO (stepAnalyticG_of hTi hB (stepAnalyticCG_of_pin_vanish_loc_thm hE hV hL hT))`.
-/
theorem rowMainEqC_of_pinned (hCh : PN.NGChain) (hC : StepClassG) (hN : StepNormalsG) (hP : StepPointsG)
    (hO : StepNormOneG) (hTi : TieOfCtx) (hB : StepChoiceConstantsC) (hE : StepPinExists) (hV : StepTermVanishG)
    (hL : StepLocGenPinnedG) (hT : StepThmBPinnedG) : RowMainEqC :=
  rowMainEqC_of_steps2 hCh hC hN hP hO (stepAnalyticG_of hTi hB (stepAnalyticCG_of_pin_vanish_loc_thm hE hV hL hT))

end Formalism.L2.SG.Pf
