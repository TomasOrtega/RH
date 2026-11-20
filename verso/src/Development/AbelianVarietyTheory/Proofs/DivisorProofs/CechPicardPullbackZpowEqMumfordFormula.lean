import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiMapFst
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulPullOfRigOfSym
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfQuasiAffine

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PowPull

/- English proof (translation)
Unfold `tri`. Establish `: (n + 1) * (n + 1) + (n + 1) = n * n + n + (n + 1) * 2` using `by ring`. Rewrite using `[this, Int.add_mul_ediv_right _ _ two_ne_zero]`.
-/
theorem tri_succ (n : ℤ) : tri (n + 1) = tri n + (n + 1) := by
  unfold tri
  have : (n + 1) * (n + 1) + (n + 1) = n * n + n + (n + 1) * 2 := by ring
  rw [this, Int.add_mul_ediv_right _ _ two_ne_zero]

/- English proof (translation)
Unfold `tri`. Establish `: n * n + n = -n * -n + -n + n * 2` using `by ring`. Rewrite using `[this, Int.add_mul_ediv_right _ _ two_ne_zero]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tri_neg (n : ℤ) : tri (-n) = tri n - n := by
  unfold tri
  have : n * n + n = -n * -n + -n + n * 2 := by ring
  rw [this, Int.add_mul_ediv_right _ _ two_ne_zero]
  ring

/- English proof (translation)
Establish `step : ∀ n : ℤ, tri (-(n + 1)) = tri (-n) + n` using `fun n => by`. Rewrite using `[tri_neg, tri_neg, tri_succ]`. Expand and normalize the polynomial expressions, which then agree. Proceed by induction on `n using Int.induction_on with`. Consider the case `zero => simp [h0, tri]`.

Consider the case `succ n ih => rw [hs, ih, step]`. Use `module`. Consider the case `pred n ih`. Establish `h` using `hs (-(n : ℤ) - 1)`. Establish `h'` using `step (-(n : ℤ) - 1)`.

Rewrite `h`, `h'` using `[sub_add_cancel]`. Rewrite `h` using `[ih, h']`. Rewrite using `[eq_sub_of_add_eq (eq_sub_of_add_eq h.symm)]`. Use `module`.
-/
theorem eq_of_rec {M : Type*} [AddCommGroup M] (f : ℤ → M) (a l : M) (h0 : f 0 = 0)
    (hs : ∀ n, f (n + 1) = f n + a + n • l) (n : ℤ) : f n = n • a + tri (-n) • l := by
  have step : ∀ n : ℤ, tri (-(n + 1)) = tri (-n) + n := fun n => by
    rw [tri_neg, tri_neg, tri_succ]; ring
  induction n using Int.induction_on with
  | zero => simp [h0, tri]
  | succ n ih => rw [hs, ih, step]; module
  | pred n ih =>
    have h := hs (-(n : ℤ) - 1)
    have h' := step (-(n : ℤ) - 1)
    rw [sub_add_cancel] at h h'
    rw [ih, h'] at h
    rw [eq_sub_of_add_eq (eq_sub_of_add_eq h.symm)]
    module

open GlobalTheory.CechPic in

/- English proof (translation)
Introduce `K _ A _ hA L hL T z n`. Use `hA.comm` as an intermediate fact. Establish `hΘ : ∃ t : LB.Gen (Theta A L), t.IsGen` using `GlobalTheory.SymMulPull.hasGen_theta GlobalTheory.CubeTop.cubeTheorem hA hL`. Establish `h1 : pull (1 : T ⟶ A).left (cls L hL) = 0`. Rewrite using `[Hom.one_def, Over.comp_left, pull_comp, GlobalTheory.AmpleStabFinite.pull_spec_local, map_zero]`.

Set `φ : (T ⟶ A) →* Multiplicative (Pic T.left)` to `MonoidHom.mk' (fun x => Multiplicative.ofAdd (lam (cls L hL) x z)) fun x y => by`. Rewrite using `[lam_mul_left hL hΘ, ofAdd_add]`. Establish `hz : ∀ m : ℤ, lam (cls L hL) (z ^ m) z = m • lam (cls L hL) z z` using `fun m => congrArg Multiplicative.toAdd (map_zpow φ z m)`. Establish `key` using `eq_of_rec (fun m => pull (z ^ m).left (cls L hL)) (pull z.left (cls L hL)) (lam (cls L hL) z z) (by rw [zpow_zero, h1]) (fun m => by`. Rewrite using `[← hz, zpow_add_one, lam, h1]`.

Use the proof step `abel)`. Establish `k1` using `key (-1)`. Establish `t1 : tri (- -1) = 1` using `by decide`. Rewrite `k1` using `[zpow_neg_one, t1]`. Rewrite using `[key n, k1, tri_neg]`.

Use `module`.
-/
theorem pull_zpow : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (hL : L.IsLB) (T : Over (Sp K)) (z : T ⟶ A) (n : ℤ), GlobalTheory.CechPic.pull (z ^ n).left (GlobalTheory.CechPic.cls L hL) = tri n • GlobalTheory.CechPic.pull z.left (GlobalTheory.CechPic.cls L hL) + tri (-n) • GlobalTheory.CechPic.pull (z⁻¹).left (GlobalTheory.CechPic.cls L hL) := by
  intro K _ A _ hA L hL T z n
  have := hA.comm
  have hΘ : ∃ t : LB.Gen (Theta A L), t.IsGen :=
    GlobalTheory.SymMulPull.hasGen_theta GlobalTheory.CubeTop.cubeTheorem hA hL
  have h1 : pull (1 : T ⟶ A).left (cls L hL) = 0 := by
    rw [Hom.one_def, Over.comp_left, pull_comp, GlobalTheory.AmpleStabFinite.pull_spec_local, map_zero]
  let φ : (T ⟶ A) →* Multiplicative (Pic T.left) :=
    MonoidHom.mk' (fun x => Multiplicative.ofAdd (lam (cls L hL) x z)) fun x y => by
      rw [lam_mul_left hL hΘ, ofAdd_add]
  have hz : ∀ m : ℤ, lam (cls L hL) (z ^ m) z = m • lam (cls L hL) z z := fun m =>
    congrArg Multiplicative.toAdd (map_zpow φ z m)
  have key := eq_of_rec (fun m => pull (z ^ m).left (cls L hL)) (pull z.left (cls L hL)) (lam (cls L hL) z z)
    (by rw [zpow_zero, h1]) (fun m => by
      rw [← hz, zpow_add_one, lam, h1]; abel)
  have k1 := key (-1)
  have t1 : tri (- -1) = 1 := by decide
  rw [zpow_neg_one, t1] at k1
  rw [key n, k1, tri_neg]
  module

end GlobalTheory.PowPull
