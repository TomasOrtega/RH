import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqFam
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc
  Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqFam Formalism.MainNotions.S.LocNG GlobalTheory.SnFam

namespace GlobalTheory.SnFam.Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Use function extensionality and compare the values at `d`. Unfold `ampQ ampG`. Rewrite using `[Finset.sum_eq_single_of_mem ∅ (by simp)]`. Simplify using the standard rewrite rules. Introduce `A hA hne`.

Simplify using `only [Finset.mem_filter, Finset.not_nonempty_iff_eq_empty] at hA`. Conclude with `absurd hA.2 hne`.
-/
private theorem ampQ_not_eq_ampG' {Cl Nu : Type} (L : PN.LocalNG Cl Nu) : ampQ Not L = ampG L := by
  funext d
  unfold ampQ ampG
  rw [Finset.sum_eq_single_of_mem ∅ (by simp)]
  · simp
  · intro A hA hne
    simp only [Finset.mem_filter, Finset.not_nonempty_iff_eq_empty] at hA
    exact absurd hA.2 hne

/- English proof (translation)
Take `⟨c, ν, t, ht, hv, -, hpt, -⟩` from `h`. Use `⟨t, ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify `ht` using `[genT, PB.Terms.ngSet, PB.Terms.genSet]`. Simplify `hv` using `[genT]`. Simplify `hpt` using `[NOfG]`.
-/
private theorem hasPt_of_isPtG {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word)
    (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ) (γ : PN.Pts D.host.E D.R.rS)
    (h : PN.IsPt (genT (Y.tO u u)) (NOfG Y u νL νB ng) γ) : HasPt Y u u (Y.tO u u).genSet γ := by
  obtain ⟨c, ν, t, ht, hv, -, hpt, -⟩ := h
  refine ⟨t, ?_, ?_, ?_⟩
  · simpa [genT, PB.Terms.ngSet, PB.Terms.genSet] using ht
  · simpa [genT] using hv
  · simpa [NOfG] using hpt

/- English proof (translation)
Introduce `hG6 hH hGen hG5 hW hG4 hE Cg cb Cw cT CT C0`. Take `⟨aH, bH, hH'⟩` from `hH Cg cb Cw cT CT C0`. Take `⟨aF, bF, hF'⟩` from `hGen Cg cb Cw cT CT C0`. Take `⟨a5, b5, h5⟩` from `hG5 Cg cb Cw cT CT C0`. Take `⟨aW, bW, hW'⟩` from `hW Cg cb Cw cT CT C0`.

Take `⟨CSt, hCSt, a4, b4, h4⟩` from `hG4 Cg cb Cw cT CT C0`. Take `⟨aE, bE, hE'⟩` from `hE Cg cb Cw cT CT C0`. Use `⟨9, CSt, hCSt, max aH (max aF (max a5 (max aW (max a4 aE)))), max bH (max bF (max b5 (max bW (max b4 bE)))), ?_⟩` and prove the remaining obligations. Introduce `C' Cl hC' hCl D large₂ X Y u hc hb X0 ψ hbt sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hbk ν hpin`. Simplify using `only [max_le_iff] at hC' hCl`.

Take `⟨s, hs1, hs2, hs3, hs4⟩` from `h4 C' Cl hC'.2.2.2.2.1 hCl.2.2.2.2.1 D large₂ X Y u u hc hb X0 ψ hbt sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hbk ν hpin`. Use `⟨s, hs1, hs2, hs3, ?_⟩` and prove the remaining obligations. Introduce `γ hγ S`. Establish `hQ` using `hF' C' Cl hC'.2.1 hCl.2.1 D large₂ X Y u u hc`. Establish `hP` using `hasPt_of_isPtG Y u (sc s ν) ν (fun _ => 0) γ hγ`.

Take `⟨Fm, hT, hRel, hTerm, hDs, hrw⟩` from `hE' C' Cl hC'.2.2.2.2.2 hCl.2.2.2.2.2 D large₂ X Y u u hc _ Not _ _ hQ γ hP`. Establish `h5' : OrbitFamilyIdentityAt Fm Fm.V0` using `Formalism.L2.SG.FamDefs.orbitFamilyIdentity_at_volume hT (h5 C' Cl hC'.2.2.1 hCl.2.2.1 D large₂ X Y u u hc _ Not _ _ hQ γ hP Fm hT)`. Take `⟨hWpos, hWle⟩` from `hW' C' Cl hC'.2.2.2.1 hCl.2.2.2.1 D large₂ X Y u u hc hb X0 ψ hbt sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hbk _ Not _ _ hQ γ hP Fm hT hRel hTerm h5'`. Establish `hHt` using `hH' C' Cl hC'.1 hCl.1 D large₂ X Y u u hc _ _ _ γ Fm hT`. Use `⟨Fm, Formalism.L2.SG.FamDefs.famOKS_of (NOfG Y u (sc s ν) ν (fun _ => 0)) γ S (PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq).AA) (fun L => ampG L) Fm hT hRel hTerm hDs hrw (hG6 D (Formalism.L2.SG.FamDefs.four_rank_add_seven_le_k hc)) …` and prove the remaining obligations.

Simplify `hHt` using `[NOfG]`. Simplify `hWle` using `[NOfG]`. Introduce `x _`. Establish `h` using `hs4 _ Not _ _ hQ γ hP Fm hT x.1 x.2`. Rewrite `h` using `[ampQ_not_eq_ampG']`.

Rewrite using `[← h]`. Both sides reduce to the same expression.
-/
theorem stepFamG_of_fam : (∀ D : D7, 4 * D.R.rS + 7 ≤ D.R.k → Formalism.L2.SG.FamDefs.LocalLowerBoundAllCosets D.R.k D.R.rS 9) →
    Formalism.L2.SG.FamDefs.HTie → FamGen → FamilyWeightSumUnfoldingIdentity → WeightsFam → FamilyGroupSumFactorsWeightAmplitude → ExistFam →
    Formalism.L2.SG.Pf.MainEqFam.StepFamG := by
  intro hG6 hH hGen hG5 hW hG4 hE Cg cb Cw cT CT C0
  obtain ⟨aH, bH, hH'⟩ := hH Cg cb Cw cT CT C0
  obtain ⟨aF, bF, hF'⟩ := hGen Cg cb Cw cT CT C0
  obtain ⟨a5, b5, h5⟩ := hG5 Cg cb Cw cT CT C0
  obtain ⟨aW, bW, hW'⟩ := hW Cg cb Cw cT CT C0
  obtain ⟨CSt, hCSt, a4, b4, h4⟩ := hG4 Cg cb Cw cT CT C0
  obtain ⟨aE, bE, hE'⟩ := hE Cg cb Cw cT CT C0
  refine ⟨9, CSt, hCSt, max aH (max aF (max a5 (max aW (max a4 aE)))),
    max bH (max bF (max b5 (max bW (max b4 bE)))), ?_⟩
  intro C' Cl hC' hCl D large₂ X Y u hc hb X0 ψ hbt sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hbk ν hpin
  simp only [max_le_iff] at hC' hCl
  obtain ⟨s, hs1, hs2, hs3, hs4⟩ := h4 C' Cl hC'.2.2.2.2.1 hCl.2.2.2.2.1 D large₂ X Y u u hc hb X0 ψ hbt sd C Th F0
    what₂ vR Q i0 i0' νq Irat Ire hbk ν hpin
  refine ⟨s, hs1, hs2, hs3, ?_⟩
  intro γ hγ S
  have hQ := hF' C' Cl hC'.2.1 hCl.2.1 D large₂ X Y u u hc
  have hP := hasPt_of_isPtG Y u (sc s ν) ν (fun _ => 0) γ hγ
  obtain ⟨Fm, hT, hRel, hTerm, hDs, hrw⟩ :=
    hE' C' Cl hC'.2.2.2.2.2 hCl.2.2.2.2.2 D large₂ X Y u u hc _ Not _ _ hQ γ hP
  have h5' : OrbitFamilyIdentityAt Fm Fm.V0 := Formalism.L2.SG.FamDefs.orbitFamilyIdentity_at_volume hT (h5 C' Cl hC'.2.2.1 hCl.2.2.1 D large₂ X Y u u hc _ Not _ _ hQ γ hP Fm hT)
  obtain ⟨hWpos, hWle⟩ := hW' C' Cl hC'.2.2.2.1 hCl.2.2.2.1 D large₂ X Y u u hc hb X0 ψ hbt sd C Th F0 what₂ vR Q i0 i0' νq
    Irat Ire hbk _ Not _ _ hQ γ hP Fm hT hRel hTerm h5'
  have hHt := hH' C' Cl hC'.1 hCl.1 D large₂ X Y u u hc _ _ _ γ Fm hT
  refine ⟨Fm, Formalism.L2.SG.FamDefs.famOKS_of (NOfG Y u (sc s ν) ν (fun _ => 0)) γ S
    (PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq).AA) (fun L => ampG L) Fm hT hRel hTerm
    hDs hrw (hG6 D (Formalism.L2.SG.FamDefs.four_rank_add_seven_le_k hc)) h5' ?_ hWpos ?_ ?_⟩
  · simpa [NOfG] using hHt
  · simpa [NOfG] using hWle
  · intro x _
    have h := hs4 _ Not _ _ hQ γ hP Fm hT x.1 x.2
    rw [ampQ_not_eq_ampG'] at h
    rw [← h]
    rfl

end GlobalTheory.SnFam.Gen
