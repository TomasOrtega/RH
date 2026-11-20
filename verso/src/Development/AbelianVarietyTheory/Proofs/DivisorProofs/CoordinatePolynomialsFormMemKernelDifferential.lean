import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecOfSpec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

namespace GlobalTheory.FormsLocus

/- English proof (translation)
Establish `n2 : (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) Rg))).inv (MvPolynomial.C r) = (affπ Rg n).appTop ((Scheme.ΓSpecIso (CommRingCat.of Rg)).inv r)`. Rewrite using `[← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]`. Both sides reduce to the same expression. Simplify using `only [cstT, ringOf, RingHom.coe_comp, Function.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]`. Rewrite using `[n2]`.
-/
theorem cstT_comp_affπ {Rg : Type} [CommRing Rg] {T : Scheme.{0}} {n : ℕ}
    (g : T ⟶ Sp (MvPolynomial (Fin n) Rg)) (r : Rg) :
    cstT (g ≫ affπ Rg n) r = ringOf g (MvPolynomial.C r) := by
  have n2 : (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) Rg))).inv (MvPolynomial.C r) =
      (affπ Rg n).appTop ((Scheme.ΓSpecIso (CommRingCat.of Rg)).inv r) := by
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]; rfl
  simp only [cstT, ringOf, RingHom.coe_comp, Function.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
  rw [n2]

/- English proof (translation)
Introduce `Rg _ A₀ T f N mA mB Q a g d F`. Establish `hC : ((Q d).D₀.map MvPolynomial.C).mulVec (fun k => polys Q a d F k) = 0`. Use function extensionality and compare the values at `l`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.map_apply, polys, Finset.mul_sum, Pi.zero_apply]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_eq_zero fun ν _ => ?_` and prove the remaining obligations. Establish `h0` using `congrFun (vecOf_ker (Q d) (monSec a d ν)) l`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.map_apply, RingHom.id_apply, Pi.zero_apply] at h0`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_sum, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = 0 := by rw [h0, map_zero, mul_zero]`. Establish `hm : (Q d).D₀.map (cstT (g ≫ affπ Rg (mA * mB))) = ((Q d).D₀.map MvPolynomial.C).map (ringOf g)`.

Rewrite using `[Matrix.map_map]`. Use `congr 1`. Use function extensionality and compare the values at `r`. Conclude with `cstT_comp_affπ g r`. Rewrite using `[hm]`.

Use function extensionality and compare the values at `l`. Establish `e` using `RingHom.map_mulVec (ringOf g) ((Q d).D₀.map MvPolynomial.C) (fun k => polys Q a d F k) l`. Rewrite `e` using `[hC]`. Simplify using `only [Pi.zero_apply, map_zero] at e`. Conclude with `e.symm`.
-/
theorem polys_ker : ∀ (Rg : Type) [CommRing Rg] (A₀ T : Scheme.{0}) (f : A₀ ⟶ Sp Rg) (N : LB A₀) (mA mB : ℕ) (Q : ∀ d : ℕ, GlobalTheory.AbLaw.Perf f (GlobalTheory.AbLaw.pw N (d : ℤ))) (a : Fin mA → LB.Sec N) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) (d : ℕ) (F : MvPolynomial (Fin mB) Rg), ((Q d).D₀.map (GlobalTheory.FormsLocus.cstT (g ≫ affπ Rg (mA * mB)))).mulVec (fun k => GlobalTheory.FormsLocus.ringOf g (GlobalTheory.FormsLocus.polys Q a d F k)) = 0 := by
  intro Rg _ A₀ T f N mA mB Q a g d F
  have hC : ((Q d).D₀.map MvPolynomial.C).mulVec (fun k => polys Q a d F k) = 0 := by
    funext l
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, polys, Finset.mul_sum, Pi.zero_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun ν _ => ?_
    have h0 := congrFun (vecOf_ker (Q d) (monSec a d ν)) l
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, RingHom.id_apply, Pi.zero_apply] at h0
    calc ∑ k, MvPolynomial.C ((Q d).D₀ l k) * ((expand mA mB F).coeff ν * MvPolynomial.C (vecOf (Q d) (monSec a d ν) k))
        = (expand mA mB F).coeff ν * MvPolynomial.C (∑ k, (Q d).D₀ l k * vecOf (Q d) (monSec a d ν) k) := by
          rw [map_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [map_mul]; ring
      _ = 0 := by rw [h0, map_zero, mul_zero]
  have hm : (Q d).D₀.map (cstT (g ≫ affπ Rg (mA * mB))) = ((Q d).D₀.map MvPolynomial.C).map (ringOf g) := by
    rw [Matrix.map_map]; congr 1; funext r; exact cstT_comp_affπ g r
  rw [hm]
  funext l
  have e := RingHom.map_mulVec (ringOf g) ((Q d).D₀.map MvPolynomial.C) (fun k => polys Q a d F k) l
  rw [hC] at e
  simp only [Pi.zero_apply, map_zero] at e
  exact e.symm

end GlobalTheory.FormsLocus
