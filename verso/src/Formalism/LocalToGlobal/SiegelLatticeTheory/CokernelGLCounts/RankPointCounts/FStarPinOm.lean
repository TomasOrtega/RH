import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SendsB
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfG
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarMinors

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open BwdCut BwdBetaCut BwdNP BetaI

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (u u' F0 what₂)

/- English proof (translation)
Establish `key : (a * d₂ * k) • A = (a * d₂ * k) • C`. Rewrite using `[h1]`. Combine the equalities or inequalities in the displayed calculation. Take `⟨v, hv⟩` from `(ha.mul hd).mul hk`. Use `congrArg (fun w => ((v⁻¹ : Rˣ) : R) • w) key` as an intermediate fact.

Simplify using `only [← hv, smul_smul, Units.inv_mul, one_smul] at this`. Conclude with `this`.
-/
theorem pinOm_cancel {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W] {a k d₁ d₂ : R} {A B C : W}
    (ha : IsUnit a) (hk : IsUnit k) (hd : IsUnit d₂) (h1 : (a * d₂ * k) • A = (a * d₁ * k) • B)
    (h2 : d₂ • C = d₁ • B) : A = C := by
  have key : (a * d₂ * k) • A = (a * d₂ * k) • C := by
    rw [h1]
    calc (a * d₁ * k) • B = (a * k) • (d₁ • B) := by rw [smul_smul]; congr 1; ring
      _ = (a * k) • (d₂ • C) := by rw [h2]
      _ = (a * d₂ * k) • C := by rw [smul_smul]; congr 1; ring
  obtain ⟨v, hv⟩ := (ha.mul hd).mul hk
  have := congrArg (fun w => ((v⁻¹ : Rˣ) : R) • w) key
  simp only [← hv, smul_smul, Units.inv_mul, one_smul] at this
  exact this

set_option maxHeartbeats 4000000 in

/- English proof (translation)
Introduce `γ Z F'₂ φ φ' Λ₂ hB β₀ hβ hfr hW hO p hm hm₂`. Take `⟨hC, hCtx, hS, -, -, hTH, hPD, hGv⟩` from `hB`. Take `⟨hZd, -, -⟩` from `starMinors_holds u u' F0 what₂ γ Z hCtx`. Establish `hT2` using `hS.2.1 p`. Take `⟨hξ1, hξ2⟩` from `inv_unitri _ (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).1 (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).2`.

Take `⟨K, hK⟩ : ∃ K : (D.s.atP p).Ep, K = (Zd.M p).L.cj (∏ j ∈ Finset.univ.erase (Fin.last D.R.rS), sF' Zd p j) * ∏ j, sF Zd p j` from `⟨_, rfl⟩`. Take `⟨P, hP⟩ : ∃ P : (D.s.atP p).Ep, P = (∏ i : Fin (D.R.rS + 1), (Zd.M p).L.cj (sF Zd p (Fin.castLE le_rfl i))) * (∏ i : Fin (D.R.rS + 1), sF' Zd p (Fin.castLE le_rfl i))` from `⟨_, rfl⟩`. Establish `ho1 : (locH Zd p).om (tLoc Zd p γ).f (tLoc Zd p γ).f' = K • baseChange₂ D p (Gom (frame (lf D F0)) (frame (repF γ)))`. Establish `e` using `om_loc Zd p (frame (lf D F0)) (frameAct (frame (repF γ)) (admXi D γ.lam (lf D F0) (repF γ))⁻¹) (sF Zd p) (sF' Zd p)`. Rewrite `e` using `[Gom_frameAct (frame (lf D F0)) (frame (repF γ)) _ hξ1 hξ2, ← hK]`.

Conclude with `e`. Establish `ho2 : (locH Zd p).om (tLoc Zd p γ).f (locF' Zd p F'₂) = K • baseChange₂ D p (Gom (frame (lf D F0)) (frame F'₂))`. Establish `e` using `om_loc Zd p (frame (lf D F0)) (frame F'₂) (sF Zd p) (sF' Zd p)`. Rewrite `e` using `[← hK]`. Conclude with `e`.

Establish `hd1 : (locH Zd p).Dl (tLoc Zd p γ).f (tLoc Zd p γ).f' (D.R.rS + 1) = P * (D.s.atP p).ιE (GDl (frame (lf D F0)) (frame (repF γ)) (D.R.rS + 1))`. Establish `e` using `dl_loc Zd p (frame (lf D F0)) (frameAct (frame (repF γ)) (admXi D γ.lam (lf D F0) (repF γ))⁻¹) (sF Zd p) (sF' Zd p) (D.R.rS + 1) le_rfl`. Rewrite `e` using `[GDl_frameAct_top (frame (lf D F0)) (frame (repF γ)) _ hξ1 hξ2, ← hP]`. Conclude with `e`. Establish `hd2 : (locH Zd p).Dl (tLoc Zd p γ).f (locF' Zd p F'₂) (D.R.rS + 1) = P * (D.s.atP p).ιE (GDl (frame (lf D F0)) (frame F'₂) (D.R.rS + 1))`.

Establish `e` using `dl_loc Zd p (frame (lf D F0)) (frame F'₂) (sF Zd p) (sF' Zd p) (D.R.rS + 1) le_rfl`. Rewrite `e` using `[← hP]`. Conclude with `e`. Establish `hid` using `hT2.2.2.2.1`. Establish `hs` using `hid.2.2.2.2.1`.

Simplify using `only at hs`. Rewrite `hs` using `[ho1, ho2, hd1, hd2]`. Establish `hω₂ : baseChange₂ D p (Gom (frame (lf D F0)) (frame F'₂)) ∈ (locH Zd p).perp ((locH Zd p).X (locF' Zd p F'₂))` using `baseChangeAt_perp' Zd p F'₂ (Gom_orth (lf D F0) F'₂)`. Establish `h1` using `hs (K • ⟨_, hm⟩) (K • ⟨_, hω₂⟩) rfl rfl`. Establish `e1` using `((locH Zd p).mkW (tLoc Zd p γ).f').map_smul K ⟨_, hm⟩`.

Establish `e2` using `((locH Zd p).mkW (locF' Zd p F'₂)).map_smul K ⟨_, hω₂⟩`. Establish `e3` using `((φ' p).toLinearMap).map_smul K ((locH Zd p).mkW (tLoc Zd p γ).f' ⟨_, hm⟩)`. Rewrite `h1` using `[e1, e2, e3, smul_smul, smul_smul]`. Establish `hD2 : GDl (frame (lf D F0)) (frame F'₂) (D.R.rS + 1) ≠ 0`. Rewrite using `[GDl_top']`.

Establish `e : GZ (frame (lf D F0)) (frame F'₂) = Z` using `hS.1`. Rewrite using `[e]`. Conclude with `hZd`. Establish `hOp : (D.s.atP p).ιE (star (GDl (frame (lf D F0)) (frame F'₂) (D.R.rS + 1))) • baseChange₂ D p (β₀ (Gom (frame (lf D F0)) (frame (repF γ)))) - (D.s.atP p).ιE (star (GDl (frame (lf D F0)) (frame (repF γ)) (D.R.rS + 1))) • baseChange₂ D p (Gom (frame (lf D F0)) (frame F'₂)) ∈ (locH …`. Use `bcP_X' Zd p (liftF F'₂) hO` as an intermediate fact.

Rewrite `this` using `[map_sub, Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂, Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂]`. Conclude with `this`. Establish `hcls : (D.s.atP p).ιE (star (GDl (frame (lf D F0)) (frame F'₂) (D.R.rS + 1))) • (locH Zd p).mkW (locF' Zd p F'₂) ⟨_, hm₂⟩ = (D.s.atP p).ιE (star (GDl (frame (lf D F0)) (frame (repF γ)) (D.R.rS + 1))) • (locH Zd p).mkW (locF' Zd p F'₂) ⟨_, hω₂⟩`. Rewrite using `[← LinearMap.map_smul, ← LinearMap.map_smul]`. Apply `(Submodule.Quotient.eq _).2` to reduce the goal to its premises.

Conclude with `hOp`. Rewrite `h1` using `[map_mul, map_mul, cj_iota (Zd.hcj p), cj_iota (Zd.hcj p)]`. Establish `hPu : IsUnit P`. Rewrite using `[hP]`. Conclude with `(IsUnit.prod_univ_iff.2 fun i => (isUnit_sF Zd p _).map _).mul (IsUnit.prod_univ_iff.2 fun i => isUnit_sF' Zd p _)`.

Establish `hKu : IsUnit K`. Rewrite using `[hK]`. Conclude with `((IsUnit.prod_iff.2 fun j _ => isUnit_sF' Zd p j).map _).mul (IsUnit.prod_univ_iff.2 fun j => isUnit_sF Zd p j)`. Establish `hDu : IsUnit ((D.s.atP p).ιE (star (GDl (frame (lf D F0)) (frame F'₂) (D.R.rS + 1))))` using `(isUnit_iff_ne_zero.2 (star_ne_zero.2 hD2)).map _`. Conclude with `pinOm_cancel (hPu.map _) hKu hDu h1 hcls`.
-/
theorem pinOm_holds : PinOm Zd u u' F0 what₂ := by
  intro γ Z F'₂ φ φ' Λ₂ hB β₀ hβ hfr hW hO p hm hm₂
  obtain ⟨hC, hCtx, hS, -, -, hTH, hPD, hGv⟩ := hB
  obtain ⟨hZd, -, -⟩ := starMinors_holds u u' F0 what₂ γ Z hCtx
  have hT2 := hS.2.1 p
  obtain ⟨hξ1, hξ2⟩ := inv_unitri _ (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).1 (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).2
  obtain ⟨K, hK⟩ : ∃ K : (D.s.atP p).Ep, K = (Zd.M p).L.cj (∏ j ∈ Finset.univ.erase (Fin.last D.R.rS), sF' Zd p j) *
      ∏ j, sF Zd p j := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : (D.s.atP p).Ep, P = (∏ i : Fin (D.R.rS + 1), (Zd.M p).L.cj (sF Zd p (Fin.castLE le_rfl i))) *
      (∏ i : Fin (D.R.rS + 1), sF' Zd p (Fin.castLE le_rfl i)) := ⟨_, rfl⟩
  have ho1 : (locH Zd p).om (tLoc Zd p γ).f (tLoc Zd p γ).f' = K • baseChange₂ D p (Gom (frame (lf D F0)) (frame (repF γ))) := by
    have e := om_loc Zd p (frame (lf D F0)) (frameAct (frame (repF γ)) (admXi D γ.lam (lf D F0) (repF γ))⁻¹)
      (sF Zd p) (sF' Zd p)
    rw [Gom_frameAct (frame (lf D F0)) (frame (repF γ)) _ hξ1 hξ2, ← hK] at e
    exact e
  have ho2 : (locH Zd p).om (tLoc Zd p γ).f (locF' Zd p F'₂) = K • baseChange₂ D p (Gom (frame (lf D F0)) (frame F'₂)) := by
    have e := om_loc Zd p (frame (lf D F0)) (frame F'₂) (sF Zd p) (sF' Zd p)
    rw [← hK] at e
    exact e
  have hd1 : (locH Zd p).Dl (tLoc Zd p γ).f (tLoc Zd p γ).f' (D.R.rS + 1) =
      P * (D.s.atP p).ιE (GDl (frame (lf D F0)) (frame (repF γ)) (D.R.rS + 1)) := by
    have e := dl_loc Zd p (frame (lf D F0)) (frameAct (frame (repF γ)) (admXi D γ.lam (lf D F0) (repF γ))⁻¹)
      (sF Zd p) (sF' Zd p) (D.R.rS + 1) le_rfl
    rw [GDl_frameAct_top (frame (lf D F0)) (frame (repF γ)) _ hξ1 hξ2, ← hP] at e
    exact e
  have hd2 : (locH Zd p).Dl (tLoc Zd p γ).f (locF' Zd p F'₂) (D.R.rS + 1) =
      P * (D.s.atP p).ιE (GDl (frame (lf D F0)) (frame F'₂) (D.R.rS + 1)) := by
    have e := dl_loc Zd p (frame (lf D F0)) (frame F'₂) (sF Zd p) (sF' Zd p) (D.R.rS + 1) le_rfl
    rw [← hP] at e
    exact e
  have hid := hT2.2.2.2.1
  have hs := hid.2.2.2.2.1
  dsimp only at hs
  rw [ho1, ho2, hd1, hd2] at hs
  have hω₂ : baseChange₂ D p (Gom (frame (lf D F0)) (frame F'₂)) ∈ (locH Zd p).perp ((locH Zd p).X (locF' Zd p F'₂)) :=
    baseChangeAt_perp' Zd p F'₂ (Gom_orth (lf D F0) F'₂)
  have h1 := hs (K • ⟨_, hm⟩) (K • ⟨_, hω₂⟩) rfl rfl
  have e1 := ((locH Zd p).mkW (tLoc Zd p γ).f').map_smul K ⟨_, hm⟩
  have e2 := ((locH Zd p).mkW (locF' Zd p F'₂)).map_smul K ⟨_, hω₂⟩
  have e3 := ((φ' p).toLinearMap).map_smul K ((locH Zd p).mkW (tLoc Zd p γ).f' ⟨_, hm⟩)
  rw [e1, e2, e3, smul_smul, smul_smul] at h1
  have hD2 : GDl (frame (lf D F0)) (frame F'₂) (D.R.rS + 1) ≠ 0 := by
    rw [GDl_top']
    have e : GZ (frame (lf D F0)) (frame F'₂) = Z := hS.1
    rw [e]; exact hZd
  have hOp : (D.s.atP p).ιE (star (GDl (frame (lf D F0)) (frame F'₂) (D.R.rS + 1))) •
        baseChange₂ D p (β₀ (Gom (frame (lf D F0)) (frame (repF γ)))) -
      (D.s.atP p).ιE (star (GDl (frame (lf D F0)) (frame (repF γ)) (D.R.rS + 1))) •
        baseChange₂ D p (Gom (frame (lf D F0)) (frame F'₂)) ∈ (locH Zd p).X (locF' Zd p F'₂) := by
    have := bcP_X' Zd p (liftF F'₂) hO
    rw [map_sub, Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂, Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂] at this
    exact this
  have hcls : (D.s.atP p).ιE (star (GDl (frame (lf D F0)) (frame F'₂) (D.R.rS + 1))) •
        (locH Zd p).mkW (locF' Zd p F'₂) ⟨_, hm₂⟩ =
      (D.s.atP p).ιE (star (GDl (frame (lf D F0)) (frame (repF γ)) (D.R.rS + 1))) •
        (locH Zd p).mkW (locF' Zd p F'₂) ⟨_, hω₂⟩ := by
    rw [← LinearMap.map_smul, ← LinearMap.map_smul]
    apply (Submodule.Quotient.eq _).2
    exact hOp
  rw [map_mul, map_mul, cj_iota (Zd.hcj p), cj_iota (Zd.hcj p)] at h1
  have hPu : IsUnit P := by
    rw [hP]
    exact (IsUnit.prod_univ_iff.2 fun i => (isUnit_sF Zd p _).map _).mul
      (IsUnit.prod_univ_iff.2 fun i => isUnit_sF' Zd p _)
  have hKu : IsUnit K := by
    rw [hK]
    exact ((IsUnit.prod_iff.2 fun j _ => isUnit_sF' Zd p j).map _).mul
      (IsUnit.prod_univ_iff.2 fun j => isUnit_sF Zd p j)
  have hDu : IsUnit ((D.s.atP p).ιE (star (GDl (frame (lf D F0)) (frame F'₂) (D.R.rS + 1)))) :=
    (isUnit_iff_ne_zero.2 (star_ne_zero.2 hD2)).map _
  exact pinOm_cancel (hPu.map _) hKu hDu h1 hcls

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
