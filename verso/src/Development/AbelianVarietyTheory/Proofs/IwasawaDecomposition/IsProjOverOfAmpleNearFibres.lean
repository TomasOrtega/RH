import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SecondChernDegreeVanishesTrueSurfaces
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfAmpleGeometricFibresAbelianScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointPrimitiveBundleEqTranslatePpav
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenThetaAbelianVariety
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsLocalRingQuotientPow
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivPullCompIff
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic

namespace GlobalTheory.DiagonalAmple

/- English proof (translation)
Use `hB.comm` as an intermediate fact. Establish `hΘ` using `AbLaw.CubeProj.exists_gen_theta_of_isProjBy globalFns_holds K B hB (WtTower.isProjBy_of_relAmple B hL hA) L hL`. Establish `h₁` using `lam_mul_left hL hΘ (𝟙 B) (𝟙 B)⁻¹ (𝟙 B)`. Rewrite `h₁` using `[mul_inv_cancel, lam_one_left]`. Establish `h₀ : pull (1 : B ⟶ B).left (cls L hL) = 0`.

Establish `: (1 : B ⟶ B).left = B.hom ≫ η[B].left` using `rfl`. Rewrite using `[this, pull_comp, PrimitiveOverField.pic_field (pull η[B].left (cls L hL)), map_zero]`. Establish `h₂ : lam (cls L hL) (𝟙 B)⁻¹ (𝟙 B) = -(pull ((𝟙 B)⁻¹).left (cls L hL)) - cls L hL`. Rewrite using `[lam, inv_mul_cancel, h₀, Over.id_left, pull_id]`. Normalize the expressions using the abelian group laws.

Establish `hi : IsIso ((𝟙 B)⁻¹ : B ⟶ B)`. Establish `: ((𝟙 B)⁻¹ : B ⟶ B) = GrpObj.inv` using `Category.id_comp _`. Rewrite using `[this]`. Use `infer_instance`. Establish `: IsIso ((𝟙 B)⁻¹ : B ⟶ B).left` using `inferInstanceAs (IsIso ((Over.forget _).map ((𝟙 B)⁻¹ : B ⟶ B)))`.

Establish `hL'` using `isAmpleLB_of_relAmple_of_isAffine B hL hA`. Establish `hP : IsAmpleLB (L.pull ((𝟙 B)⁻¹).left)` using `hL'.pull_of_isAffineHom _`. Use `hL'.tensor hP hN ((cls_eq_zero_iff (LB.isLB_div (LB.isLB_div hN hL) hP.isLB)).1 ?_)` and prove the remaining obligations. Rewrite using `[cls_div (LB.isLB_div hN hL) hP.isLB, cls_div hN hL, cls_pull hL, e, eq_neg_of_add_eq_zero_left h₁.symm, h₂]`. Normalize the expressions using the abelian group laws.
-/
theorem isAmpleLB_of_cls_eq_lam {K : Type} [Field K] (B : Over (Sp K)) [GrpObj B] (hB : IsAbelianScheme B)
    {L N : LB B.left} (hL : L.IsLB) (hA : Out.RelAmple B L) (hN : N.IsLB)
    (e : cls N hN = lam (cls L hL) (𝟙 B) (𝟙 B)) : IsAmpleLB N := by
  have := hB.comm
  have hΘ := AbLaw.CubeProj.exists_gen_theta_of_isProjBy globalFns_holds K B hB
    (WtTower.isProjBy_of_relAmple B hL hA) L hL
  have h₁ := lam_mul_left hL hΘ (𝟙 B) (𝟙 B)⁻¹ (𝟙 B)
  rw [mul_inv_cancel, lam_one_left] at h₁
  have h₀ : pull (1 : B ⟶ B).left (cls L hL) = 0 := by
    have : (1 : B ⟶ B).left = B.hom ≫ η[B].left := rfl
    rw [this, pull_comp, PrimitiveOverField.pic_field (pull η[B].left (cls L hL)), map_zero]
  have h₂ : lam (cls L hL) (𝟙 B)⁻¹ (𝟙 B) = -(pull ((𝟙 B)⁻¹).left (cls L hL)) - cls L hL := by
    rw [lam, inv_mul_cancel, h₀, Over.id_left, pull_id]
    abel
  have hi : IsIso ((𝟙 B)⁻¹ : B ⟶ B) := by
    have : ((𝟙 B)⁻¹ : B ⟶ B) = GrpObj.inv := Category.id_comp _
    rw [this]; infer_instance
  have : IsIso ((𝟙 B)⁻¹ : B ⟶ B).left := inferInstanceAs (IsIso ((Over.forget _).map ((𝟙 B)⁻¹ : B ⟶ B)))
  have hL' := isAmpleLB_of_relAmple_of_isAffine B hL hA
  have hP : IsAmpleLB (L.pull ((𝟙 B)⁻¹).left) := hL'.pull_of_isAffineHom _
  refine hL'.tensor hP hN ((cls_eq_zero_iff (LB.isLB_div (LB.isLB_div hN hL) hP.isLB)).1 ?_)
  rw [cls_div (LB.isLB_div hN hL) hP.isLB, cls_div hN hL, cls_pull hL, e, eq_neg_of_add_eq_zero_left h₁.symm, h₂]
  abel

variable {S : Scheme.{0}}

/- English proof (translation)
Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify using `[IndefiniteRowSideFullHecke.ZeroSectionBase.sqToBase, IndefiniteRowSideFullHecke.ZeroSectionBase.toBase] erw [pullback.lift_fst, pullback.lift_fst, pullback.lift_fst_assoc]`. Simplify using the standard rewrite rules. Simplify using `[IndefiniteRowSideFullHecke.ZeroSectionBase.sqToBase, IndefiniteRowSideFullHecke.ZeroSectionBase.toBase] erw [pullback.lift_snd, pullback.lift_snd, pullback.lift_snd_assoc]`. Simplify using the standard rewrite rules.
-/
theorem diag_sqToBase (A : Over S) {S' : Scheme.{0}} (s : S' ⟶ S) :
    (lift (𝟙 ((Over.pullback s).obj A)) (𝟙 _)).left ≫ IndefiniteRowSideFullHecke.ZeroSectionBase.sqToBase A s =
      pullback.fst A.hom s ≫ (lift (𝟙 A) (𝟙 A)).left := by
  apply pullback.hom_ext
  · simp [IndefiniteRowSideFullHecke.ZeroSectionBase.sqToBase, IndefiniteRowSideFullHecke.ZeroSectionBase.toBase]
    erw [pullback.lift_fst, pullback.lift_fst, pullback.lift_fst_assoc]
    simp
  · simp [IndefiniteRowSideFullHecke.ZeroSectionBase.sqToBase, IndefiniteRowSideFullHecke.ZeroSectionBase.toBase]
    erw [pullback.lift_snd, pullback.lift_snd, pullback.lift_snd_assoc]
    simp

/- English proof (translation)
Take `⟨L, hL, hA, -, hc⟩` from `P.isPol.2.2 Ω s`. Use `isAmpleLB_of_cls_eq_lam ((Over.pullback s).obj P.A) (AbLaw.CubeGen.isAb_baseChange P.isAb s) hL hA (LB.isLB_pull hM _) ?_` and prove the remaining obligations. Establish `h` using `congrArg (pull (lift (𝟙 ((Over.pullback s).obj P.A)) (𝟙 _)).left) hc`. Rewrite `h` using `[pull_lam, lift_fst, lift_snd, ← pull_comp, diag_sqToBase, pull_comp, ← e]`. Conclude with `h`.
-/
theorem isAmpleLB_geometricFibre (P : PPAS S) {M : LB P.A.left} (hM : M.IsLB)
    (e : cls M hM = pull (lift (𝟙 P.A) (𝟙 P.A)).left P.c) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (s : Sp Ω ⟶ S) :
    IsAmpleLB (M.pull (pullback.fst P.A.hom s)) := by
  obtain ⟨L, hL, hA, -, hc⟩ := P.isPol.2.2 Ω s
  refine isAmpleLB_of_cls_eq_lam ((Over.pullback s).obj P.A) (AbLaw.CubeGen.isAb_baseChange P.isAb s) hL hA
    (LB.isLB_pull hM _) ?_
  have h := congrArg (pull (lift (𝟙 ((Over.pullback s).obj P.A)) (𝟙 _)).left) hc
  rw [pull_lam, lift_fst, lift_snd, ← pull_comp, diag_sqToBase, pull_comp, ← e] at h
  exact h

/- English proof (translation)
Take `⟨hp, H, hH⟩` from `isProper_and_exists_isAmpleLB_of_isProjOver hS`. Establish `hA : Out.RelAmple A M` using `AmpleLocal.relAmple_of_locally S A M hM inferInstance inferInstance fun y => by`. Take `⟨U, hU, hy, ha⟩` from `h y`. Establish `: IsAffine U` using `hU`. Establish `: IsProper (Over.mk (A.hom ∣_ U)).hom` using `inferInstanceAs (IsProper (A.hom ∣_ U))`.

Conclude with `⟨U, hy, (relAmple_iff_isAmpleLB_of_isAffine (Over.mk (A.hom ∣_ U)) ha.isLB).2 ha⟩`. Take `⟨-, N, hN⟩` from `RelAmpleQProj.isProper_and_exists_isAmpleLB A hM hA hH`. Establish `e : ShFam.Pad.toSpZ A.left = A.hom ≫ ShFam.Pad.toSpZ S` using `specZIsTerminal.hom_ext _ _`. Establish `: IsProper (ShFam.Pad.toSpZ A.left)` using `by rw [e]; infer_instance`. Conclude with `hN.isProjOver _`.
-/
theorem isProjOver_of_locally (A : Over S) [IsProper A.hom] {M : LB A.left} (hM : M.IsLB)
    (h : ∀ y : S, ∃ U : S.Opens, IsAffineOpen U ∧ y ∈ U ∧ IsAmpleLB (M.pull (A.hom ⁻¹ᵁ U).ι))
    (hS : IsProjOver (ShFam.Pad.toSpZ S)) : IsProjOver (ShFam.Pad.toSpZ A.left) := by
  obtain ⟨hp, H, hH⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hS
  have hA : Out.RelAmple A M := AmpleLocal.relAmple_of_locally S A M hM inferInstance inferInstance fun y => by
    obtain ⟨U, hU, hy, ha⟩ := h y
    have : IsAffine U := hU
    have : IsProper (Over.mk (A.hom ∣_ U)).hom := inferInstanceAs (IsProper (A.hom ∣_ U))
    exact ⟨U, hy, (relAmple_iff_isAmpleLB_of_isAffine (Over.mk (A.hom ∣_ U)) ha.isLB).2 ha⟩
  obtain ⟨-, N, hN⟩ := RelAmpleQProj.isProper_and_exists_isAmpleLB A hM hA hH
  have e : ShFam.Pad.toSpZ A.left = A.hom ≫ ShFam.Pad.toSpZ S := specZIsTerminal.hom_ext _ _
  have : IsProper (ShFam.Pad.toSpZ A.left) := by rw [e]; infer_instance
  exact hN.isProjOver _

end GlobalTheory.DiagonalAmple
