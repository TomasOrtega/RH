import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOrderSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeTheoremPicardGroup
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsGenThetaOfIsAbelianScheme
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AmpleRigid
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.AmpleCube

open GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.CubeThm

section
attribute [local instance] CategoryTheory.Hom.group

variable {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsCommMonObj B]

/- English proof (translation)
Use `set c := GlobalTheory.CechPic.cls L hL`. Establish `hT : (Theta B L).IsLB` using `LB.isLB_linComb hL _ _`. Establish `h0 : GlobalTheory.CechPic.cls (Theta B L) hT = 0` using `(GlobalTheory.CechPic.cls_eq_zero_iff hT).2 hΘ`. Establish `h1 : (∑ I : ULift.{0} (Finset (Fin 3)), ((-1 : ℤ) ^ (3 - I.down.card)) • GlobalTheory.CechPic.pull (psum B (x3 B) I.down).left c) = 0` using `(GlobalTheory.CechPic.cls_linComb hL (fun I : ULift.{0} (Finset (Fin 3)) => (psum B (x3 B) I.down).left) (fun I => (-1 : ℤ) ^ (3 - I.down.card)) hT).symm.trans h0`. Establish `h2` using `congrArg (GlobalTheory.CechPic.pull (lift x (lift y z)).left) h1`.

Rewrite `h2` using `[map_sum, map_zero]`. Simplify using `only [map_zsmul, ← GlobalTheory.CechPic.pull_comp, ← Over.comp_left, comp_psum, lift_comp_cubeCoordinates] at h2`. Rewrite `h2` using `[← Equiv.ulift.symm.sum_comp]`. Simplify using `only [Equiv.ulift_symm_down] at h2`. Rewrite `h2` using `[show (Finset.univ : Finset (Finset (Fin 3))) = {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} by decide]`.

Rewrite `h2` using `[Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]`. Establish `e0 : psum B ![x, y, z] ∅ = 1` using `rfl`. Establish `e1 : psum B ![x, y, z] {0} = x` using `(show _ = x * 1 from rfl).trans (mul_one x)`. Establish `e2 : psum B ![x, y, z] {1} = y` using `(show _ = y * 1 from rfl).trans (mul_one y)`. Establish `e3 : psum B ![x, y, z] {2} = z` using `(show _ = z * 1 from rfl).trans (mul_one z)`.

Establish `e4 : psum B ![x, y, z] {0, 1} = x * y` using `(show _ = x * (y * 1) from rfl).trans (congrArg (x * ·) (mul_one y))`. Establish `e5 : psum B ![x, y, z] {0, 2} = x * z` using `(show _ = x * (z * 1) from rfl).trans (congrArg (x * ·) (mul_one z))`. Establish `e6 : psum B ![x, y, z] {1, 2} = y * z` using `(show _ = y * (z * 1) from rfl).trans (congrArg (y * ·) (mul_one z))`. Establish `e7 : psum B ![x, y, z] {0, 1, 2} = x * y * z` using `(show _ = x * (y * (z * 1)) from rfl).trans ((congrArg (x * ·) (congrArg (y * ·) (mul_one z))).trans (mul_assoc x y z).symm)`. Rewrite `h2` using `[e0, e1, e2, e3, e4, e5, e6, e7]`.

Establish `c0 : (∅ : Finset (Fin 3)).card = 0` using `rfl`. Establish `c1 : ({0} : Finset (Fin 3)).card = 1` using `rfl`. Establish `c2 : ({1} : Finset (Fin 3)).card = 1` using `rfl`. Establish `c3 : ({2} : Finset (Fin 3)).card = 1` using `rfl`. Establish `c4 : ({0, 1} : Finset (Fin 3)).card = 2` using `rfl`.

Establish `c5 : ({0, 2} : Finset (Fin 3)).card = 2` using `rfl`. Establish `c6 : ({1, 2} : Finset (Fin 3)).card = 2` using `rfl`. Establish `c7 : ({0, 1, 2} : Finset (Fin 3)).card = 3` using `rfl`. Rewrite `h2` using `[c0, c1, c2, c3, c4, c5, c6, c7]`. Evaluate the numerical expressions using `at h2`.

Rewrite using `[← sub_eq_zero]`. Rewrite using `[← h2]`. Normalize the expressions using the abelian group laws.
-/
theorem cube_pic_of_gen (L : LB B.left) (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta B L), t.IsGen)
    (x y z : B ⟶ B) :
    GlobalTheory.CechPic.pull (x * y * z).left (GlobalTheory.CechPic.cls L hL) +
                 GlobalTheory.CechPic.pull x.left (GlobalTheory.CechPic.cls L hL) +
                 GlobalTheory.CechPic.pull y.left (GlobalTheory.CechPic.cls L hL) +
                 GlobalTheory.CechPic.pull z.left (GlobalTheory.CechPic.cls L hL) =
      GlobalTheory.CechPic.pull (x * y).left (GlobalTheory.CechPic.cls L hL) +
        GlobalTheory.CechPic.pull (x * z).left (GlobalTheory.CechPic.cls L hL) +
        GlobalTheory.CechPic.pull (y * z).left (GlobalTheory.CechPic.cls L hL) +
        GlobalTheory.CechPic.pull (1 : B ⟶ B).left (GlobalTheory.CechPic.cls L hL) := by
  set c := GlobalTheory.CechPic.cls L hL
  have hT : (Theta B L).IsLB := LB.isLB_linComb hL _ _
  have h0 : GlobalTheory.CechPic.cls (Theta B L) hT = 0 := (GlobalTheory.CechPic.cls_eq_zero_iff hT).2 hΘ
  have h1 : (∑ I : ULift.{0} (Finset (Fin 3)),
      ((-1 : ℤ) ^ (3 - I.down.card)) • GlobalTheory.CechPic.pull (psum B (x3 B) I.down).left c) = 0 :=
    (GlobalTheory.CechPic.cls_linComb hL (fun I : ULift.{0} (Finset (Fin 3)) => (psum B (x3 B) I.down).left)
      (fun I => (-1 : ℤ) ^ (3 - I.down.card)) hT).symm.trans h0
  have h2 := congrArg (GlobalTheory.CechPic.pull (lift x (lift y z)).left) h1
  rw [map_sum, map_zero] at h2
  simp only [map_zsmul, ← GlobalTheory.CechPic.pull_comp, ← Over.comp_left, comp_psum, lift_comp_cubeCoordinates] at h2
  rw [← Equiv.ulift.symm.sum_comp] at h2
  simp only [Equiv.ulift_symm_down] at h2
  rw [show (Finset.univ : Finset (Finset (Fin 3))) =
      {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} by decide] at h2
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton] at h2
  have e0 : psum B ![x, y, z] ∅ = 1 := rfl
  have e1 : psum B ![x, y, z] {0} = x := (show _ = x * 1 from rfl).trans (mul_one x)
  have e2 : psum B ![x, y, z] {1} = y := (show _ = y * 1 from rfl).trans (mul_one y)
  have e3 : psum B ![x, y, z] {2} = z := (show _ = z * 1 from rfl).trans (mul_one z)
  have e4 : psum B ![x, y, z] {0, 1} = x * y :=
    (show _ = x * (y * 1) from rfl).trans (congrArg (x * ·) (mul_one y))
  have e5 : psum B ![x, y, z] {0, 2} = x * z :=
    (show _ = x * (z * 1) from rfl).trans (congrArg (x * ·) (mul_one z))
  have e6 : psum B ![x, y, z] {1, 2} = y * z :=
    (show _ = y * (z * 1) from rfl).trans (congrArg (y * ·) (mul_one z))
  have e7 : psum B ![x, y, z] {0, 1, 2} = x * y * z :=
    (show _ = x * (y * (z * 1)) from rfl).trans
      ((congrArg (x * ·) (congrArg (y * ·) (mul_one z))).trans (mul_assoc x y z).symm)
  rw [e0, e1, e2, e3, e4, e5, e6, e7] at h2
  have c0 : (∅ : Finset (Fin 3)).card = 0 := rfl
  have c1 : ({0} : Finset (Fin 3)).card = 1 := rfl
  have c2 : ({1} : Finset (Fin 3)).card = 1 := rfl
  have c3 : ({2} : Finset (Fin 3)).card = 1 := rfl
  have c4 : ({0, 1} : Finset (Fin 3)).card = 2 := rfl
  have c5 : ({0, 2} : Finset (Fin 3)).card = 2 := rfl
  have c6 : ({1, 2} : Finset (Fin 3)).card = 2 := rfl
  have c7 : ({0, 1, 2} : Finset (Fin 3)).card = 3 := rfl
  rw [c0, c1, c2, c3, c4, c5, c6, c7] at h2
  norm_num at h2
  rw [← sub_eq_zero]
  rw [← h2]
  abel

end

/- English proof (translation)
Introduce `K _ _ A _ _ hA L hL hamp c x y z`. Take `⟨M, hM, rfl⟩` from `GlobalTheory.CechPic.cls_surj c`. Conclude with `cube_pic_of_gen A M hM (GlobalTheory.exists_gen_theta_of_isAbelianScheme K A hA M hM) x y z`.
-/
theorem cubeSt : CubeSt := by
  intro K _ _ A _ _ hA L hL hamp c x y z
  obtain ⟨M, hM, rfl⟩ := GlobalTheory.CechPic.cls_surj c
  exact cube_pic_of_gen A M hM (GlobalTheory.exists_gen_theta_of_isAbelianScheme K A hA M hM) x y z

end GlobalTheory.AmpleCube
