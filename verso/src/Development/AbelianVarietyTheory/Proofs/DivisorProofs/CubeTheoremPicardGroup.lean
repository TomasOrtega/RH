import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffOfSec
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

noncomputable section
namespace GlobalTheory.CubeThm

variable {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsCommMonObj B]

/- English proof (translation)
Unfold `psum`. Proceed by induction on `((List.finRange n).filter (· ∈ I)) with`. Consider the case `nil => simp [pzero]`. Consider the case `cons a l ih`. Rewrite using `[List.foldr_cons, List.foldr_cons, ← ih]`.

Simplify using `only [padd]`. Rewrite using `[← Category.assoc, comp_lift]`.
-/
theorem comp_psum {T T' : Over S} {n : ℕ} (f : T' ⟶ T) (v : Fin n → (T ⟶ B)) (I : Finset (Fin n)) :
    f ≫ psum B v I = psum B (fun i => f ≫ v i) I := by
  unfold psum
  induction ((List.finRange n).filter (· ∈ I)) with
  | nil => simp [pzero]
  | cons a l ih =>
    rw [List.foldr_cons, List.foldr_cons, ← ih]
    simp only [padd]
    rw [← Category.assoc, comp_lift]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> simp [x3]`.
-/
theorem lift_comp_cubeCoordinates (x y z : B ⟶ B) :
    (fun i => lift x (lift y z) ≫ x3 B i) = ![x, y, z] := by
  funext i
  fin_cases i <;> simp [x3]

/- English proof (translation)
Use `set c := GlobalTheory.CechPic.cls M.L.L M.L.isLB`. Establish `hT : (Theta B M.L.L).IsLB` using `LB.isLB_linComb M.L.isLB _ _`. Establish `h0 : GlobalTheory.CechPic.cls (Theta B M.L.L) hT = 0` using `(GlobalTheory.CechPic.cls_eq_zero_iff hT).2 ⟨M.c.t, M.c.isGen⟩`. Establish `h1 : (∑ I : ULift.{0} (Finset (Fin 3)), ((-1 : ℤ) ^ (3 - I.down.card)) • GlobalTheory.CechPic.pull (psum B (x3 B) I.down).left c) = 0` using `(GlobalTheory.CechPic.cls_linComb M.L.isLB (fun I : ULift.{0} (Finset (Fin 3)) => (psum B (x3 B) I.down).left) (fun I => (-1 : ℤ) ^ (3 - I.down.card)) hT).symm.trans h0`. Establish `h2` using `congrArg (GlobalTheory.CechPic.pull (lift x (lift y z)).left) h1`.

Rewrite `h2` using `[map_sum, map_zero]`. Simplify using `only [map_zsmul, ← GlobalTheory.CechPic.pull_comp, ← Over.comp_left, comp_psum, lift_comp_cubeCoordinates] at h2`. Rewrite `h2` using `[← Equiv.ulift.symm.sum_comp]`. Simplify using `only [Equiv.ulift_symm_down] at h2`. Rewrite `h2` using `[show (Finset.univ : Finset (Finset (Fin 3))) = {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} by decide]`.

Rewrite `h2` using `[Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]`. Establish `e0 : psum B ![x, y, z] ∅ = 1` using `rfl`. Establish `e1 : psum B ![x, y, z] {0} = x` using `(show _ = x * 1 from rfl).trans (mul_one x)`. Establish `e2 : psum B ![x, y, z] {1} = y` using `(show _ = y * 1 from rfl).trans (mul_one y)`. Establish `e3 : psum B ![x, y, z] {2} = z` using `(show _ = z * 1 from rfl).trans (mul_one z)`.

Establish `e4 : psum B ![x, y, z] {0, 1} = x * y` using `(show _ = x * (y * 1) from rfl).trans (congrArg (x * ·) (mul_one y))`. Establish `e5 : psum B ![x, y, z] {0, 2} = x * z` using `(show _ = x * (z * 1) from rfl).trans (congrArg (x * ·) (mul_one z))`. Establish `e6 : psum B ![x, y, z] {1, 2} = y * z` using `(show _ = y * (z * 1) from rfl).trans (congrArg (y * ·) (mul_one z))`. Establish `e7 : psum B ![x, y, z] {0, 1, 2} = x * y * z` using `(show _ = x * (y * (z * 1)) from rfl).trans ((congrArg (x * ·) (congrArg (y * ·) (mul_one z))).trans (mul_assoc x y z).symm)`. Rewrite `h2` using `[e0, e1, e2, e3, e4, e5, e6, e7]`.

Establish `c0 : (∅ : Finset (Fin 3)).card = 0` using `rfl`. Establish `c1 : ({0} : Finset (Fin 3)).card = 1` using `rfl`. Establish `c2 : ({1} : Finset (Fin 3)).card = 1` using `rfl`. Establish `c3 : ({2} : Finset (Fin 3)).card = 1` using `rfl`. Establish `c4 : ({0, 1} : Finset (Fin 3)).card = 2` using `rfl`.

Establish `c5 : ({0, 2} : Finset (Fin 3)).card = 2` using `rfl`. Establish `c6 : ({1, 2} : Finset (Fin 3)).card = 2` using `rfl`. Establish `c7 : ({0, 1, 2} : Finset (Fin 3)).card = 3` using `rfl`. Rewrite `h2` using `[c0, c1, c2, c3, c4, c5, c6, c7]`. Evaluate the numerical expressions using `at h2`.

Rewrite using `[← sub_eq_zero]`. Rewrite using `[← h2]`. Normalize the expressions using the abelian group laws.
-/
theorem cube_pic (M : GlobalTheory.UU.CP B) (x y z : B ⟶ B) :
    GlobalTheory.CechPic.pull (x * y * z).left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) +
                 GlobalTheory.CechPic.pull x.left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) +
                 GlobalTheory.CechPic.pull y.left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) +
                 GlobalTheory.CechPic.pull z.left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) =
      GlobalTheory.CechPic.pull (x * y).left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) +
        GlobalTheory.CechPic.pull (x * z).left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) +
        GlobalTheory.CechPic.pull (y * z).left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) +
        GlobalTheory.CechPic.pull (1 : B ⟶ B).left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) := by
  set c := GlobalTheory.CechPic.cls M.L.L M.L.isLB
  have hT : (Theta B M.L.L).IsLB := LB.isLB_linComb M.L.isLB _ _
  have h0 : GlobalTheory.CechPic.cls (Theta B M.L.L) hT = 0 :=
    (GlobalTheory.CechPic.cls_eq_zero_iff hT).2 ⟨M.c.t, M.c.isGen⟩
  have h1 : (∑ I : ULift.{0} (Finset (Fin 3)),
      ((-1 : ℤ) ^ (3 - I.down.card)) • GlobalTheory.CechPic.pull (psum B (x3 B) I.down).left c) = 0 :=
    (GlobalTheory.CechPic.cls_linComb M.L.isLB (fun I : ULift.{0} (Finset (Fin 3)) => (psum B (x3 B) I.down).left)
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

end GlobalTheory.CubeThm
