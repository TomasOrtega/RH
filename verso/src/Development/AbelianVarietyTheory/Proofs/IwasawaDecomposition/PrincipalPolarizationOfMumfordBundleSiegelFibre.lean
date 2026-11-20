import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsPrincipalPolarizationSymmetricSquareRoot
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsTwoTorsionTranslateSameLambdaBundle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj

noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory
open MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.SiegFibrePol

/- English proof (translation)
Introduce `o _ ζ g n F K _ y B _ α α₂ hpb hsq L hL hrig hsym hΛ`. Use `open GlobalTheory.CechPic GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.AbLaw in`. Establish `hB : IsAbelianScheme B` using `GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback F.univ.ab hpb`. Use `hB.comm` as an intermediate fact. Establish `laws : Out.Laws` using `GlobalTheory.allSixLaws.1`.

Use `haveI : IsProper F.univ.A.hom := F.univ.ab.proper`. Establish `hP' : (F.univ.P.pull α₂).IsLB` using `pull_isLB F.univ.isLB α₂`. Establish `hrefl : LBIso (F.univ.P.pull α₂) (F.univ.P.pull α₂)` using `(GlobalTheory.CechPic.cls_eq_iff hP' hP').1 rfl`. Establish `hn` using `GlobalTheory.SiegelPull.nondeg_pull hpb hsq F.univ.isLB hP' hrefl F.princ.2`. Establish `hM0 : (F.univ.diag.pull α).IsLB` using `pull_isLB (pull_isLB F.univ.isLB _) α`.

Establish `hamp0 : Out.RelAmple B (F.univ.diag.pull α)` using `GlobalTheory.AmpleBaseChange.relAmple_of_isPullback (pull_isLB F.univ.isLB _) F.princ.1 hpb.1`. Establish `hd : ((F.univ.P.pull α₂).pull (lift (𝟙 B) (𝟙 B)).left).IsLB` using `pull_isLB hP' _`. Establish `hdiag` using `GlobalTheory.SiegelPull.diag_iso hsq hrefl`. Establish `eM0 : GlobalTheory.CechPic.cls _ hM0 = GlobalTheory.CechPic.cls _ hd` using `((GlobalTheory.CechPic.cls_eq_iff hd hM0).2 hdiag).symm`. Establish `hp : IsProjBy B.hom` using `(GlobalTheory.AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral _ B _ hB hM0 hamp0 K (𝟙 _) _ (𝟙 _) B.hom (IsPullback.of_horiz_isIso ⟨by simp⟩)).1`.

Establish `hΘ` using `GlobalTheory.AbLaw.CubeAffine.triv_theta_of_isProjBy laws K B hB hp L hL`. Establish `s₁` using `GlobalTheory.SameLam.pull_inv_cls hL hsym`. Establish `e₀ : GlobalTheory.CechPic.cls _ hP' = GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) (fst B B) (snd B B)` using `((GlobalTheory.CechPic.cls_eq_iff (LB.isLB_linComb hL _ _) hP').2 hΛ).symm.trans (GlobalTheory.CechPic.cls_cube_two hL _ _ (LB.isLB_linComb hL _ _))`. Establish `hη : GlobalTheory.CechPic.pull (η[B] : 𝟙_ _ ⟶ B).left (GlobalTheory.CechPic.cls L hL) = 0`. Rewrite using `[← GlobalTheory.CechPic.cls_pull hL _ (pull_isLB hL _)]`.

Conclude with `(GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hL _)).2 hrig`. Establish `h1 : GlobalTheory.CechPic.pull (1 : B ⟶ B).left (GlobalTheory.CechPic.cls L hL) = 0`. Rewrite using `[Hom.one_def, Over.comp_left, GlobalTheory.CechPic.pull_comp, hη, map_zero]`. Establish `e₃ : GlobalTheory.CechPic.cls _ hd = 2 • GlobalTheory.CechPic.cls L hL`. Use `(GlobalTheory.CechPic.cls_pull hP' _ _).trans ?_` and prove the remaining obligations.

Rewrite using `[e₀, GlobalTheory.CechPic.pull_lam, lift_fst, lift_snd, GlobalTheory.SymRoot.lam_diag hL hΘ s₁, GlobalTheory.SymRoot.rigCls, h1, sub_zero]`. Establish `f : IsFinite (𝟙 B : B ⟶ B).left` using `by rw [Over.id_left]; infer_instance`. Establish `iso : LBIso (F.univ.diag.pull α) (lbPow L 2)` using `(GlobalTheory.CechPic.cls_eq_iff hM0 (isLB_lbPow hL 2)).1 (eM0.trans (e₃.trans (cls_lbPow hL 2 _).symm))`. Establish `hamp : Out.RelAmple B L` using `(GlobalTheory.relAmple_finite_pow_iso _ B B (𝟙 _) L 2 two_pos hB hB hL f).2.1.1 ((GlobalTheory.relAmple_finite_pow_iso _ B B (𝟙 _) _ 2 two_pos hB hB hM0 f).2.2.2 _ (isLB_lbPow hL 2) iso hamp0)`. Conclude with `⟨hB, hamp, GlobalTheory.ThetaExtend.kTriv_of_lam hL hP' e₀ hn⟩`.
-/
theorem polAV_of_lam_univ : ∀ (o : Type) [CommRing o] (ζ : o) (g n : ℕ) (F : SFam g n ζ) (K : Type) [Field K] (y : Sp K ⟶ F.X) (B : Over (Sp K)) [GrpObj B] (α : B.left ⟶ F.univ.A.left) (α₂ : (G2 B).left ⟶ (G2 F.univ.A).left), IsGrpPullback B F.univ.A y α → IsSquare α α₂ → ∀ L : LB B.left, L.IsLB → Rigidified B L → Out.Sym B L → LBIso (abelian₂ B L) (F.univ.P.pull α₂) → IsAbelianScheme B ∧ RelAmple B L ∧ KTriv B L := by
  intro o _ ζ g n F K _ y B _ α α₂ hpb hsq L hL hrig hsym hΛ
  open GlobalTheory.CechPic GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.AbLaw in
  have hB : IsAbelianScheme B := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback F.univ.ab hpb
  have := hB.comm
  have laws : Out.Laws := GlobalTheory.allSixLaws.1
  haveI : IsProper F.univ.A.hom := F.univ.ab.proper
  have hP' : (F.univ.P.pull α₂).IsLB := pull_isLB F.univ.isLB α₂
  have hrefl : LBIso (F.univ.P.pull α₂) (F.univ.P.pull α₂) := (GlobalTheory.CechPic.cls_eq_iff hP' hP').1 rfl
  have hn := GlobalTheory.SiegelPull.nondeg_pull hpb hsq F.univ.isLB hP' hrefl F.princ.2
  have hM0 : (F.univ.diag.pull α).IsLB := pull_isLB (pull_isLB F.univ.isLB _) α
  have hamp0 : Out.RelAmple B (F.univ.diag.pull α) :=
    GlobalTheory.AmpleBaseChange.relAmple_of_isPullback (pull_isLB F.univ.isLB _) F.princ.1 hpb.1
  have hd : ((F.univ.P.pull α₂).pull (lift (𝟙 B) (𝟙 B)).left).IsLB := pull_isLB hP' _
  have hdiag := GlobalTheory.SiegelPull.diag_iso hsq hrefl
  have eM0 : GlobalTheory.CechPic.cls _ hM0 = GlobalTheory.CechPic.cls _ hd := ((GlobalTheory.CechPic.cls_eq_iff hd hM0).2 hdiag).symm
  have hp : IsProjBy B.hom :=
    (GlobalTheory.AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral _ B _ hB hM0 hamp0 K (𝟙 _) _ (𝟙 _) B.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)).1
  have hΘ := GlobalTheory.AbLaw.CubeAffine.triv_theta_of_isProjBy laws K B hB hp L hL
  have s₁ := GlobalTheory.SameLam.pull_inv_cls hL hsym
  have e₀ : GlobalTheory.CechPic.cls _ hP' = GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) (fst B B) (snd B B) :=
    ((GlobalTheory.CechPic.cls_eq_iff (LB.isLB_linComb hL _ _) hP').2 hΛ).symm.trans
      (GlobalTheory.CechPic.cls_cube_two hL _ _ (LB.isLB_linComb hL _ _))
  have hη : GlobalTheory.CechPic.pull (η[B] : 𝟙_ _ ⟶ B).left (GlobalTheory.CechPic.cls L hL) = 0 := by
    rw [← GlobalTheory.CechPic.cls_pull hL _ (pull_isLB hL _)]
    exact (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hL _)).2 hrig
  have h1 : GlobalTheory.CechPic.pull (1 : B ⟶ B).left (GlobalTheory.CechPic.cls L hL) = 0 := by
    rw [Hom.one_def, Over.comp_left, GlobalTheory.CechPic.pull_comp, hη, map_zero]
  have e₃ : GlobalTheory.CechPic.cls _ hd = 2 • GlobalTheory.CechPic.cls L hL := by
    refine (GlobalTheory.CechPic.cls_pull hP' _ _).trans ?_
    rw [e₀, GlobalTheory.CechPic.pull_lam, lift_fst, lift_snd, GlobalTheory.SymRoot.lam_diag hL hΘ s₁, GlobalTheory.SymRoot.rigCls, h1, sub_zero]
  have f : IsFinite (𝟙 B : B ⟶ B).left := by rw [Over.id_left]; infer_instance
  have iso : LBIso (F.univ.diag.pull α) (lbPow L 2) :=
    (GlobalTheory.CechPic.cls_eq_iff hM0 (isLB_lbPow hL 2)).1 (eM0.trans (e₃.trans (cls_lbPow hL 2 _).symm))
  have hamp : Out.RelAmple B L :=
    (GlobalTheory.relAmple_finite_pow_iso _ B B (𝟙 _) L 2 two_pos hB hB hL f).2.1.1
      ((GlobalTheory.relAmple_finite_pow_iso _ B B (𝟙 _) _ 2 two_pos hB hB hM0 f).2.2.2 _ (isLB_lbPow hL 2) iso hamp0)
  exact ⟨hB, hamp, GlobalTheory.ThetaExtend.kTriv_of_lam hL hP' e₀ hn⟩

end GlobalTheory.SiegFibrePol
