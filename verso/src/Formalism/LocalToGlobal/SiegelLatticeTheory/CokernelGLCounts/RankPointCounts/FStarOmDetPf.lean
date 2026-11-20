import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarOmLocPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalSplitTypeMixedSecond

noncomputable section

open scoped Classical
open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Matrix

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

open OmP OmL

namespace OmD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (p : PlF D)

/- English proof (translation)
Conclude with `Matrix.ext fun a b => Formalism.L2.SG.Pf.AtPt.brS_frameAct (lf D F0) F' ξ a b`.
-/
theorem mat_frameAct {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T')
    (ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E)) :
    (Matrix.of fun a b => (VS D).hT (F0.fvec a) (frameAct (frame F') ξ b)) =
      Zhat F0 F'.fl * ξ.map (algebraMap (𝓞 D.host.E) D.host.E) := by
  exact Matrix.ext fun a b => Formalism.L2.SG.Pf.AtPt.brS_frameAct (lf D F0) F' ξ a b

/- English proof (translation)
The claim follows from `(RingHom.map_det _ _).symm`.
-/
theorem map_det_eq {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (G : Fin (D.R.rS + 1) → (VS D).V) :
    ((Matrix.of fun a b => (VS D).hT (F0.fvec a) (G b)).map (D.s.atP p).ιE).det =
      (D.s.atP p).ιE (Matrix.of fun a b => (VS D).hT (F0.fvec a) (G b)).det := (RingHom.map_det _ _).symm

/- English proof (translation)
Introduce `h0`. Rewrite `h` using `[zhat_fg, Matrix.det_mul, Matrix.det_mul, map_det_eq, h0, map_zero, mul_zero, zero_mul]`. Conclude with `not_isUnit_zero h`.
-/
theorem det_ne_of_unit {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (G : Fin (D.R.rS + 1) → (VS D).V)
    (h : IsUnit ((locH Zd p).Zhat (fL Zd p F0) (gL Zd p G)).det) :
    (Matrix.of fun a b => (VS D).hT (F0.fvec a) (G b)).det ≠ 0 := by
  intro h0
  rw [zhat_fg, Matrix.det_mul, Matrix.det_mul, map_det_eq, h0, map_zero, mul_zero, zero_mul] at h
  exact not_isUnit_zero h

/- English proof (translation)
Unfold `Formalism.L2.SG.Pf.ScalarFramePf.GDl Formalism.MainNotions.S.Dl leadMinorE`. Apply the tactic sequence `split_ifs <;> rfl`.
-/
theorem gdl_eq {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : FlagG (VS D) D.R.rS T') (l : ℕ) :
    Formalism.L2.SG.Pf.ScalarFramePf.GDl F0.fvec F'.fvec l = Formalism.MainNotions.S.Dl F0 F' l := by
  unfold Formalism.L2.SG.Pf.ScalarFramePf.GDl Formalism.MainNotions.S.Dl leadMinorE
  split_ifs <;> rfl

end OmD

open OmD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (u u' F0 what₂)

/- English proof (translation)
Introduce `_ γ Z _ F'₂ φ φ' hS F' hP`. Take `⟨p⟩` from `Formalism.L2.SG.Pf.LocModel.plF_nonempty D`. Establish `hT2` using `hS.2.1 p`. Establish `hunγ` using `hT2.1.1.2.2.2.1`. Rewrite `hunγ` using `[dl_last]`.

Establish `hdγ : (ZhatL (lf D F0) (repF γ)).det ≠ 0`. Establish `h1` using `det_ne_of_unit Zd p F0 (frameAct (frame (repF γ)) (admXi D γ.lam (lf D F0) (repF γ))⁻¹) hunγ`. Rewrite `h1` using `[mat_frameAct, Matrix.det_mul]`. Conclude with `left_ne_zero_of_mul h1`. Use `⟨hdγ, fun hZ => ?_⟩` and prove the remaining obligations.

Establish `hZ2 : (Matrix.of fun a b => (VS D).hT (F0.fvec a) (F'₂.fl.fvec b)) = Z` using `hS.1`. Establish `hD2 : (locH Zd p).Dl (fL Zd p F0) (gL Zd p F'₂.fl.fvec) (D.R.rS + 1) = 0`. Rewrite using `[dl_last, zhat_fg, Matrix.det_mul, Matrix.det_mul, map_det_eq, hZ2, hZ, map_zero, mul_zero, zero_mul]`. Establish `hId : (locH Zd p).Dl (tLoc Zd p γ).f (tLoc Zd p γ).f' D.R.rS * (locH Zd p).Dl (fL Zd p F0) (gL Zd p F'₂.fl.fvec) (D.R.rS + 1) = (locH Zd p).Dl (fL Zd p F0) (gL Zd p F'₂.fl.fvec) D.R.rS * (locH Zd p).Dl (tLoc Zd p γ).f (tLoc Zd p γ).f' (D.R.rS + 1)` using `hT2.2.2.2.1.2.2.2.2.2`. Rewrite `hId` using `[hD2, mul_zero]`.

Take `⟨uγ, huγ⟩` from `hT2.1.1.2.2.2.1`. Rewrite `hId` using `[← huγ]`. Establish `hDr` using `(Units.mul_left_eq_zero uγ).1 hId.symm`. Establish `e` using `Formalism.L2.SG.Pf.ScalarFramePf.dl_loc Zd p F0.fvec F'₂.fl.fvec (Formalism.L2.SG.Pf.ScalarFramePf.sF Zd p) (Formalism.L2.SG.Pf.ScalarFramePf.sF' Zd p) D.R.rS (Nat.le_succ _)`. Rewrite `hDr` using `[show (locH Zd p).Dl (fL Zd p F0) (gL Zd p F'₂.fl.fvec) D.R.rS = _ from e]`.

Establish `hu1 : IsUnit (∏ i : Fin D.R.rS, (Zd.M p).L.cj (Formalism.L2.SG.Pf.ScalarFramePf.sF Zd p (Fin.castLE (Nat.le_succ _) i)))` using `IsUnit.prod_univ_iff.2 fun i => (Formalism.L2.SG.Pf.ScalarFramePf.isUnit_sF Zd p _).map _`. Establish `hu2 : IsUnit (∏ i : Fin D.R.rS, Formalism.L2.SG.Pf.ScalarFramePf.sF' Zd p (Fin.castLE (Nat.le_succ _) i))` using `IsUnit.prod_univ_iff.2 fun i => Formalism.L2.SG.Pf.ScalarFramePf.isUnit_sF' Zd p _`. Establish `hg` using `(hu1.mul hu2).mul_right_eq_zero.1 hDr`. Rewrite `hg` using `[map_eq_zero_iff _ (D.s.atP p).ιE.injective, gdl_eq]`. Establish `hG` using `hP.1.1.2.2`.

Rewrite `hG` using `[fwdCut_gval_congr (lf D F0) F' F'₂ (hP.1.2.2.2.2.trans hS.1.symm)]`. Apply `hG` to reduce the goal to its premises. Use `show Formalism.MainNotions.S.Gflag F0 F'₂.fl = 0`. Unfold `Formalism.MainNotions.S.Gflag`. Rewrite using `[PI.UnitaryGroupMassFormula.BetaLUniq.GN.Dl_succ, hg, show Zhat F0 F'₂.fl = Z from hS.1, hZ]`.

Simplify using the standard rewrite rules.
-/
theorem modeMatrixDet_eq_adjointDet : OmDet Zd u u' F0 what₂ := by
  intro _ γ Z _ F'₂ φ φ' hS F' hP
  obtain ⟨p⟩ := Formalism.L2.SG.Pf.LocModel.plF_nonempty D
  have hT2 := hS.2.1 p
  have hunγ := hT2.1.1.2.2.2.1
  rw [dl_last] at hunγ
  have hdγ : (ZhatL (lf D F0) (repF γ)).det ≠ 0 := by
    have h1 := det_ne_of_unit Zd p F0
      (frameAct (frame (repF γ)) (admXi D γ.lam (lf D F0) (repF γ))⁻¹) hunγ
    rw [mat_frameAct, Matrix.det_mul] at h1
    exact left_ne_zero_of_mul h1
  refine ⟨hdγ, fun hZ => ?_⟩
  have hZ2 : (Matrix.of fun a b => (VS D).hT (F0.fvec a) (F'₂.fl.fvec b)) = Z := hS.1
  have hD2 : (locH Zd p).Dl (fL Zd p F0) (gL Zd p F'₂.fl.fvec) (D.R.rS + 1) = 0 := by
    rw [dl_last, zhat_fg, Matrix.det_mul, Matrix.det_mul, map_det_eq, hZ2, hZ, map_zero, mul_zero, zero_mul]
  have hId : (locH Zd p).Dl (tLoc Zd p γ).f (tLoc Zd p γ).f' D.R.rS *
      (locH Zd p).Dl (fL Zd p F0) (gL Zd p F'₂.fl.fvec) (D.R.rS + 1) =
      (locH Zd p).Dl (fL Zd p F0) (gL Zd p F'₂.fl.fvec) D.R.rS *
        (locH Zd p).Dl (tLoc Zd p γ).f (tLoc Zd p γ).f' (D.R.rS + 1) := hT2.2.2.2.1.2.2.2.2.2
  rw [hD2, mul_zero] at hId
  obtain ⟨uγ, huγ⟩ := hT2.1.1.2.2.2.1
  rw [← huγ] at hId
  have hDr := (Units.mul_left_eq_zero uγ).1 hId.symm
  have e := Formalism.L2.SG.Pf.ScalarFramePf.dl_loc Zd p F0.fvec F'₂.fl.fvec (Formalism.L2.SG.Pf.ScalarFramePf.sF Zd p)
    (Formalism.L2.SG.Pf.ScalarFramePf.sF' Zd p) D.R.rS (Nat.le_succ _)
  rw [show (locH Zd p).Dl (fL Zd p F0) (gL Zd p F'₂.fl.fvec) D.R.rS = _ from e] at hDr
  have hu1 : IsUnit (∏ i : Fin D.R.rS, (Zd.M p).L.cj
      (Formalism.L2.SG.Pf.ScalarFramePf.sF Zd p (Fin.castLE (Nat.le_succ _) i))) :=
    IsUnit.prod_univ_iff.2 fun i => (Formalism.L2.SG.Pf.ScalarFramePf.isUnit_sF Zd p _).map _
  have hu2 : IsUnit (∏ i : Fin D.R.rS, Formalism.L2.SG.Pf.ScalarFramePf.sF' Zd p (Fin.castLE (Nat.le_succ _) i)) :=
    IsUnit.prod_univ_iff.2 fun i => Formalism.L2.SG.Pf.ScalarFramePf.isUnit_sF' Zd p _
  have hg := (hu1.mul hu2).mul_right_eq_zero.1 hDr
  rw [map_eq_zero_iff _ (D.s.atP p).ιE.injective, gdl_eq] at hg
  have hG := hP.1.1.2.2
  rw [fwdCut_gval_congr (lf D F0) F' F'₂ (hP.1.2.2.2.2.trans hS.1.symm)] at hG
  apply hG
  show Formalism.MainNotions.S.Gflag F0 F'₂.fl = 0
  unfold Formalism.MainNotions.S.Gflag
  rw [PI.UnitaryGroupMassFormula.BetaLUniq.GN.Dl_succ, hg, show Zhat F0 F'₂.fl = Z from hS.1, hZ]
  simp

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
