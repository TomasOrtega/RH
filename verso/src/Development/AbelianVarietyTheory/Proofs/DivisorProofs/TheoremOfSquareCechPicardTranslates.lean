import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfTrivAxes

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SquareSym

/- English proof (translation)
Take `⟨L, hL, rfl⟩` from `cls_surj c`. Establish `hP : (abelian₂ A L).IsLB` using `LB.isLB_linComb hL _ _`. Establish `e : ∀ (Y : Over S) (a b : Y ⟶ A), evc hP a b = lam (cls L hL) a b` using `fun Y a b ↦ by`. Rewrite using `[evc, show cls _ hP = lam (cls L hL) (fst A A) (snd A A) from cls_cube_two hL _ _ hP, pull_lam, lift_fst, lift_snd]`. Establish `h` using `GlobalTheory.CubeNoeth.isAdditive_of_triv_axes hA hA hP (by rw [triv_ev_iff hP, e, lam_one_left]) (by rw [triv_ev_iff hP, e, lam_one_right])`.

Simplify `(isAdditive_iff hP).1 h Y a a' x` using `only [e]`.
-/
theorem lam_mul_left {S : Scheme.{0}} [IsLocallyNoetherian S] {A : Over S} [GrpObj A] (hA : IsAbelianScheme A)
    (c : Pic A.left) {Y : Over S} (a a' x : Y ⟶ A) : lam c (a * a') x = lam c a x + lam c a' x := by
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  have hP : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  have e : ∀ (Y : Over S) (a b : Y ⟶ A), evc hP a b = lam (cls L hL) a b := fun Y a b ↦ by
    rw [evc, show cls _ hP = lam (cls L hL) (fst A A) (snd A A) from cls_cube_two hL _ _ hP, pull_lam, lift_fst,
      lift_snd]
  have h := GlobalTheory.CubeNoeth.isAdditive_of_triv_axes hA hA hP
    (by rw [triv_ev_iff hP, e, lam_one_left]) (by rw [triv_ev_iff hP, e, lam_one_right])
  simpa only [e] using (isAdditive_iff hP).1 h Y a a' x

/- English proof (translation)
Introduce `S _ A _ hA c Y x a`. Use `haveI := hA.comm`. Establish `h` using `lam_mul_left hA c a a⁻¹ x`. Rewrite `h` using `[mul_inv_cancel, lam_one_left, lam_comm c a x, lam_comm c a⁻¹ x, lam, lam]`. Rewrite using `[← sub_eq_zero, h]`.

Normalize the expressions using the abelian group laws.
-/
theorem pull_mul_add_pull_mul_inv : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (c : Pic A.left) (Y : Over S) (x a : Y ⟶ A), GlobalTheory.CechPic.pull (x * a).left c + GlobalTheory.CechPic.pull (x * a⁻¹).left c = 2 • GlobalTheory.CechPic.pull (x).left c + GlobalTheory.CechPic.pull (a).left c + GlobalTheory.CechPic.pull (a⁻¹).left c - 2 • GlobalTheory.CechPic.pull ((1 : Y ⟶ A)).left c := by
  intro S _ A _ hA c Y x a
  haveI := hA.comm
  have h := lam_mul_left hA c a a⁻¹ x
  rw [mul_inv_cancel, lam_one_left, lam_comm c a x, lam_comm c a⁻¹ x, lam, lam] at h
  rw [← sub_eq_zero, h]
  abel

end GlobalTheory.SquareSym
