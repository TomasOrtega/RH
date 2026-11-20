import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarLprExistA
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarLprExistB
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarLprPfD
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ScalRelRepFree
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ScalEquivGen

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace LprEx

variable {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

/- English proof (translation)
Take `⟨hE, γ', ⟨pr, hp1, hp2, hps, hpsc⟩, h3, h3e⟩` from `hP`. Take `⟨h2, h2e⟩` from `starRepF_rep γ`. Establish `hGF : Gval (lf D F0) F'' ≠ 0` using `hE.1.2.2`. Take `⟨lam, mem, cls⟩` from `γ`. Take `⟨lam', mem', cls'⟩` from `γ'`.

Take `⟨lp, mp, p1, p2, gp1, gp2, bp, ip⟩` from `pr`. Simplify using `only [Formalism.L2.SG.Corank.Pair.pfst, Formalism.L2.SG.Corank.Pair.psnd] at hp1 hp2`. Take `⟨rfl, hc1⟩` from `hp1`. Take `⟨rfl, hc2⟩` from `hp2`. Conclude with `scal_move (hrows.1 _ mp) ⟨p1, gp1⟩ ⟨p2, gp2⟩ ⟨⟨repF _, h2⟩, hGr⟩ ⟨⟨F'', h3⟩, hGF⟩ h2e.symm h3e.symm ⟨bp, ip, hps, hpsc⟩`.
-/
theorem scal_rep (hrows : IsRowReps D F0 what₂) (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D)
    (F'' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (hP : IsPartner γ Z F'')
    (hGr : Gval (lf D F0) (repF γ) ≠ 0) :
    ∃ β, IsPair γ.lam (lf D F0) (repF γ) F'' β (gS D) ∧ s0 γ.lam (lf D F0) (repF γ) F'' β D.R.k = 1 ∧
      IsScalar γ.lam (lf D F0) (repF γ) F'' β := by
  obtain ⟨hE, γ', ⟨pr, hp1, hp2, hps, hpsc⟩, h3, h3e⟩ := hP
  obtain ⟨h2, h2e⟩ := starRepF_rep γ
  have hGF : Gval (lf D F0) F'' ≠ 0 := hE.1.2.2
  obtain ⟨lam, mem, cls⟩ := γ
  obtain ⟨lam', mem', cls'⟩ := γ'
  obtain ⟨lp, mp, p1, p2, gp1, gp2, bp, ip⟩ := pr
  simp only [Formalism.L2.SG.Corank.Pair.pfst, Formalism.L2.SG.Corank.Pair.psnd] at hp1 hp2
  obtain ⟨rfl, hc1⟩ := hp1
  obtain ⟨rfl, hc2⟩ := hp2
  exact scal_move (hrows.1 _ mp) ⟨p1, gp1⟩ ⟨p2, gp2⟩ ⟨⟨repF _, h2⟩, hGr⟩ ⟨⟨F'', h3⟩, hGF⟩ h2e.symm h3e.symm
    ⟨bp, ip, hps, hpsc⟩

variable (Zd : LocDat D)

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `hrows γ Z hC F'' hP p`. Take `⟨w, hγ, -⟩` from `hC`. Establish `hR : IsRowLat D F0 γ.lam` using `hrows.1 γ.lam γ.mem`. Establish `hF : FixedHyp D γ.lam (lf D F0)` using `hR.2.1`. Take `⟨h2, h2e⟩` from `starRepF_rep γ`.

Establish `hGr : Gval (lf D F0) (repF γ) ≠ 0` using `gval_repF γ w hγ`. Establish `hgenR : IsGeneric γ.lam (gS D) (lf D F0) (repF γ)`. Take `⟨hgen, -⟩` from `hγ.1`. Take `⟨F', ⟨h1, h1e⟩, hF'⟩` from `hgen`. Establish `hrel` using `(Formalism.L2.SG.Pf.double_coset_equivalence γ.lam (lf D F0) (PD D γ.lam (lf D F0) u') ⟨F', h1⟩ ⟨repF γ, h2⟩).1 (h1e.trans h2e.symm)`.

Conclude with `(PI.TermAttrConst.UnitaryGroupMassFormula.genericity_constant_double_cosets D u u' F0 γ.lam hR ⟨F', h1⟩ ⟨repF γ, h2⟩ hrel).1 hF'`. Establish `hE` using `hP.1`. Take `⟨β, hPair, hs, hsc⟩` from `scal_rep hrows γ Z F'' hP hGr`. Establish `hT : ((Tu D u : ℕ) : D.host.E) ≠ 0` using `Formalism.L2.SG.Corank.tu_ne_zero u`. Establish `hT' : ((Tu D u' : ℕ) : D.host.E) ≠ 0` using `Formalism.L2.SG.Corank.tu_ne_zero u'`.

Establish `hG` using `Formalism.L2.SG.Pf.ScalarFramePf.gfacts_of γ.lam (lf D F0) (repF γ) F'' β hF h2.1 hE.1.1 h2.2.2.1 hE.2.2.2.1.1 hPair hs hsc hGr hE.1.2.2 hT hT'`. Establish `hIo` using `hI D Zd γ.lam (lf D F0) (repF γ) F'' β hF h2.1 hE.1.1 h2.2.2.1 hE.2.2.2.1.1 h2.2.1 hE.1.2.1 hPair hgenR hE.2.2.1 hs hsc hGr hE.1.2.2 hT hT' p`. Establish `hξ` using `admissibility_witness_unitriangular γ.lam (lf D F0) F''`. Establish `hG2` using `gfacts_frameAct (admXi D γ.lam (lf D F0) F'') hξ.1 hξ.2 hG`. Establish `hI2` using `iotaEl_frameAct Zd p (admXi D γ.lam (lf D F0) F'') hξ.1 hξ.2 hIo`.

Take `⟨hId, hRe⟩` from `Formalism.L2.SG.Pf.ScalarFramePf.identResp_lt Zd p γ.lam (frame (lf D F0)) _ (frame F'') β (Tu D u) (Tu D u') hG2 hI2`. Conclude with `⟨Formalism.L2.SG.Pf.ScalarFramePf.phiP Zd p γ.lam (frame (lf D F0)) _ (frame F'') β hG2, hId, hRe.2.2.2.1, hRe.2.2.1, hRe.2.2.2.2⟩`.
-/
theorem lprExist_of (hI : Formalism.L2.SG.Pf.ScalarFramePf.IotaStep) : LprExist Zd u u' F0 what₂ := by
  intro hrows γ Z hC F'' hP p
  obtain ⟨w, hγ, -⟩ := hC
  have hR : IsRowLat D F0 γ.lam := hrows.1 γ.lam γ.mem
  have hF : FixedHyp D γ.lam (lf D F0) := hR.2.1
  obtain ⟨h2, h2e⟩ := starRepF_rep γ
  have hGr : Gval (lf D F0) (repF γ) ≠ 0 := gval_repF γ w hγ
  have hgenR : IsGeneric γ.lam (gS D) (lf D F0) (repF γ) := by
    obtain ⟨hgen, -⟩ := hγ.1
    obtain ⟨F', ⟨h1, h1e⟩, hF'⟩ := hgen
    have hrel := (Formalism.L2.SG.Pf.double_coset_equivalence γ.lam (lf D F0) (PD D γ.lam (lf D F0) u') ⟨F', h1⟩ ⟨repF γ, h2⟩).1
      (h1e.trans h2e.symm)
    exact (PI.TermAttrConst.UnitaryGroupMassFormula.genericity_constant_double_cosets D u u' F0 γ.lam hR ⟨F', h1⟩ ⟨repF γ, h2⟩ hrel).1 hF'
  have hE := hP.1
  obtain ⟨β, hPair, hs, hsc⟩ := scal_rep hrows γ Z F'' hP hGr
  have hT : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Formalism.L2.SG.Corank.tu_ne_zero u
  have hT' : ((Tu D u' : ℕ) : D.host.E) ≠ 0 := Formalism.L2.SG.Corank.tu_ne_zero u'
  have hG := Formalism.L2.SG.Pf.ScalarFramePf.gfacts_of γ.lam (lf D F0) (repF γ) F'' β hF h2.1 hE.1.1 h2.2.2.1
    hE.2.2.2.1.1 hPair hs hsc hGr hE.1.2.2 hT hT'
  have hIo := hI D Zd γ.lam (lf D F0) (repF γ) F'' β hF h2.1 hE.1.1 h2.2.2.1 hE.2.2.2.1.1 h2.2.1 hE.1.2.1 hPair
    hgenR hE.2.2.1 hs hsc hGr hE.1.2.2 hT hT' p
  have hξ := admissibility_witness_unitriangular γ.lam (lf D F0) F''
  have hG2 := gfacts_frameAct (admXi D γ.lam (lf D F0) F'') hξ.1 hξ.2 hG
  have hI2 := iotaEl_frameAct Zd p (admXi D γ.lam (lf D F0) F'') hξ.1 hξ.2 hIo
  obtain ⟨hId, hRe⟩ := Formalism.L2.SG.Pf.ScalarFramePf.identResp_lt Zd p γ.lam (frame (lf D F0)) _ (frame F'') β
    (Tu D u) (Tu D u') hG2 hI2
  exact ⟨Formalism.L2.SG.Pf.ScalarFramePf.phiP Zd p γ.lam (frame (lf D F0)) _ (frame F'') β hG2, hId, hRe.2.2.2.1,
    hRe.2.2.1, hRe.2.2.2.2⟩

/- English proof (translation)
The claim follows from `lprPart_of' Zd (lprExist_of Zd hI)`.
-/
theorem lprPart_of_iota (hI : Formalism.L2.SG.Pf.ScalarFramePf.IotaStep) : LprPart Zd u u' F0 what₂ :=
  lprPart_of' Zd (lprExist_of Zd hI)

end LprEx

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
