import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.OrbitFinR
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RepresentationIndependence.FrameOKMap

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000 in
open PI.RepsIndep.Tr in
/- English proof (translation)
Establish `hlf : lf D (mapF β hβ F0) = mapL β hβ (lf D F0)` using `lflag_ext rfl rfl`. Unfold `EZ at h ⊢`. Rewrite `h`, the goal using `[Set.mem_setOf_eq]`. Rewrite using `[hlf]`. Take `⟨⟨hL, ⟨ξ, hξ⟩, hG⟩, hA, hGen, hF, hZ⟩` from `h`.

Establish `hG' : Gval (mapL β hβ (lf D F0)) (mapL β hβ F') ≠ 0` using `by show Formalism.MainNotions.S.Gflag (mapF β hβ F0) (mapF β hβ F'.fl) ≠ 0`. Simplify using `only [Formalism.MainNotions.S.Gflag, Formalism.MainNotions.S.Dl, Zhat_mapF hβ]`. Conclude with `hG`. Establish `hZ' : ZhatL (mapL β hβ (lf D F0)) (mapL β hβ F') = Z` using `by show Formalism.MainNotions.S.Zhat (mapF β hβ F0) (mapF β hβ F'.fl) = Z`. Rewrite using `[Zhat_mapF hβ]`.

Conclude with `hZ`. Conclude with `⟨⟨IsLift_map hβ hL, ⟨ξ, AdmWit_map hβ hξ⟩, hG'⟩, AdmWit_map hβ hA, IsGeneric_map hβ hGen, FrameOK_map hβ hF, hZ'⟩`.
-/
theorem ci_EZ_map {D : Formalism.BasicNotions.D7} {β : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hβ : β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    {T T' : D.host.E} {F0 : FlagG (VS D) D.R.rS T} {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    {Z : MatZ D} {F' : LFlag (VS D) D.R.rS T'} (h : F' ∈ EZ T' F0 Λ Z) :
    mapL β hβ F' ∈ EZ T' (mapF β hβ F0) (Formalism.HermitianLatticesTheory.gmap β Λ) Z := by
  have hlf : lf D (mapF β hβ F0) = mapL β hβ (lf D F0) := lflag_ext rfl rfl
  unfold EZ at h ⊢
  rw [Set.mem_setOf_eq] at h ⊢
  rw [hlf]
  obtain ⟨⟨hL, ⟨ξ, hξ⟩, hG⟩, hA, hGen, hF, hZ⟩ := h
  have hG' : Gval (mapL β hβ (lf D F0)) (mapL β hβ F') ≠ 0 := by
    show Formalism.MainNotions.S.Gflag (mapF β hβ F0) (mapF β hβ F'.fl) ≠ 0
    simp only [Formalism.MainNotions.S.Gflag, Formalism.MainNotions.S.Dl, Zhat_mapF hβ]
    exact hG
  have hZ' : ZhatL (mapL β hβ (lf D F0)) (mapL β hβ F') = Z := by
    show Formalism.MainNotions.S.Zhat (mapF β hβ F0) (mapF β hβ F'.fl) = Z
    rw [Zhat_mapF hβ]
    exact hZ
  exact ⟨⟨IsLift_map hβ hL, ⟨ξ, AdmWit_map hβ hξ⟩, hG'⟩, AdmWit_map hβ hA, IsGeneric_map hβ hGen,
    FrameOK_map hβ hF, hZ'⟩

set_option maxHeartbeats 2000000 in
open PI.RepsIndep.Tr in
/- English proof (translation)
Establish `hlf : lf D (mapF β hβ F0) = mapL β hβ (lf D F0)` using `lflag_ext rfl rfl`. Take `⟨n, ⟨hnL, hne, hnz⟩, h1, h2⟩` from `h`. Establish `hN : conj β n ∈ NLam (Formalism.HermitianLatticesTheory.gmap β Λ) (lf D (mapF β hβ F0))`. Rewrite using `[hlf]`. Conclude with `NLam_conj hβ hnL`.

Use `⟨conj β n, ⟨hN, fun a => ?_, ?_⟩, fun a => ?_, ?_⟩` and prove the remaining obligations. Use `show β (n (β.symm (β (F0.e a)))) = β (F0.e a)`. Rewrite using `[LinearEquiv.symm_apply_apply, hne]`. Use `show β (n (β.symm (β F0.z))) = β F0.z`. Rewrite using `[LinearEquiv.symm_apply_apply, hnz]`.

Use `show β (n (β.symm (β (F'.fl.e a)))) = β (F''.fl.e a)`. Rewrite using `[LinearEquiv.symm_apply_apply, h1]`. Use `show β (n (β.symm (β F'.fl.z))) = β F''.fl.z`. Rewrite using `[LinearEquiv.symm_apply_apply, h2]`.
-/
theorem ci_rel_map {D : Formalism.BasicNotions.D7} {β : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hβ : β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    {T T' : D.host.E} {F0 : FlagG (VS D) D.R.rS T} {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    {F' F'' : LFlag (VS D) D.R.rS T'} (h : NilradicalFlagMoved F0 Λ F' F'') :
    NilradicalFlagMoved (mapF β hβ F0) (Formalism.HermitianLatticesTheory.gmap β Λ) (mapL β hβ F') (mapL β hβ F'') := by
  have hlf : lf D (mapF β hβ F0) = mapL β hβ (lf D F0) := lflag_ext rfl rfl
  obtain ⟨n, ⟨hnL, hne, hnz⟩, h1, h2⟩ := h
  have hN : conj β n ∈ NLam (Formalism.HermitianLatticesTheory.gmap β Λ) (lf D (mapF β hβ F0)) := by
    rw [hlf]; exact NLam_conj hβ hnL
  refine ⟨conj β n, ⟨hN, fun a => ?_, ?_⟩, fun a => ?_, ?_⟩
  · show β (n (β.symm (β (F0.e a)))) = β (F0.e a)
    rw [LinearEquiv.symm_apply_apply, hne]
  · show β (n (β.symm (β F0.z))) = β F0.z
    rw [LinearEquiv.symm_apply_apply, hnz]
  · show β (n (β.symm (β (F'.fl.e a)))) = β (F''.fl.e a)
    rw [LinearEquiv.symm_apply_apply, h1]
  · show β (n (β.symm (β F'.fl.z))) = β F''.fl.z
    rw [LinearEquiv.symm_apply_apply, h2]

open PI.RepsIndep.Tr in
/- English proof (translation)
The claim follows from `flag_ext (funext fun a => LinearEquiv.symm_apply_apply β (F0.e a)) (LinearEquiv.symm_apply_apply β F0.z)`.
-/
theorem ci_mapF_symm {D : Formalism.BasicNotions.D7} {β : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hβ : β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) : mapF β.symm (iso_symm hβ) (mapF β hβ F0) = F0 :=
  flag_ext (funext fun a => LinearEquiv.symm_apply_apply β (F0.e a)) (LinearEquiv.symm_apply_apply β F0.z)

open PI.RepsIndep.Tr in
/- English proof (translation)
Introduce `D β hβ T T' F0 Λ Z`. Establish `hβ'` using `iso_symm hβ`. Establish `hΛ : Formalism.HermitianLatticesTheory.gmap β.symm (Formalism.HermitianLatticesTheory.gmap β Λ) = Λ` using `gmap_symm_gmap β Λ`. Establish `hF : Formalism.L2.SG.Saturated.mapFlag β hβ F0 = mapF β hβ F0` using `flag_ext rfl rfl`. Rewrite using `[hF]`.

Use `show Formalism.MainNotions.S.Cnt.cntCl (EZ T' (mapF β hβ F0) (Formalism.HermitianLatticesTheory.gmap β Λ) Z) (NilradicalFlagMoved (mapF β hβ F0) (Formalism.HermitianLatticesTheory.gmap β Λ)) = Formalism.MainNotions.S.Cnt.cntCl (EZ T' F0 Λ Z) (NilradicalFlagMoved F0 Λ)`. Use `cntCl_equiv (mapL β hβ) (mapL β.symm hβ') (mapL_symm hβ) (mapL_symm' hβ hβ') _ _ _ _ (fun F' => ⟨fun h => ?_, fun h => ci_EZ_map hβ h⟩) (fun F' F'' => ⟨fun h => ?_, fun h => ci_rel_map hβ h⟩)` and prove the remaining obligations. Establish `e` using `ci_EZ_map hβ' h`. Rewrite `e` using `[mapL_symm hβ, ci_mapF_symm hβ, hΛ]`. Conclude with `e`.

Establish `e` using `ci_rel_map hβ' h`. Rewrite `e` using `[mapL_symm hβ, mapL_symm hβ, ci_mapF_symm hβ, hΛ]`. Conclude with `e`.
-/
theorem counting_iso_inverse : CntIsoInv := by
  intro D β hβ T T' F0 Λ Z
  have hβ' := iso_symm hβ
  have hΛ : Formalism.HermitianLatticesTheory.gmap β.symm (Formalism.HermitianLatticesTheory.gmap β Λ) = Λ := gmap_symm_gmap β Λ
  have hF : Formalism.L2.SG.Saturated.mapFlag β hβ F0 = mapF β hβ F0 := flag_ext rfl rfl
  rw [hF]
  show Formalism.MainNotions.S.Cnt.cntCl (EZ T' (mapF β hβ F0) (Formalism.HermitianLatticesTheory.gmap β Λ) Z) (NilradicalFlagMoved (mapF β hβ F0) (Formalism.HermitianLatticesTheory.gmap β Λ)) =
    Formalism.MainNotions.S.Cnt.cntCl (EZ T' F0 Λ Z) (NilradicalFlagMoved F0 Λ)
  refine cntCl_equiv (mapL β hβ) (mapL β.symm hβ') (mapL_symm hβ) (mapL_symm' hβ hβ') _ _ _ _
    (fun F' => ⟨fun h => ?_, fun h => ci_EZ_map hβ h⟩) (fun F' F'' => ⟨fun h => ?_, fun h => ci_rel_map hβ h⟩)
  · have e := ci_EZ_map hβ' h
    rw [mapL_symm hβ, ci_mapF_symm hβ, hΛ] at e
    exact e
  · have e := ci_rel_map hβ' h
    rw [mapL_symm hβ, mapL_symm hβ, ci_mapF_symm hβ, hΛ] at e
    exact e

end Formalism.L2.SG.Pf.Cnt
