import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.MulPullSec

variable {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]

/- English proof (translation)
Rewrite using `[gs_eq r z U h]`. Use `(Z.mem_basicOpen (U := r ⁻¹ᵁ U) ((r.app U).hom a) z h).symm.trans ?_` and prove the remaining obligations. Rewrite using `[← Scheme.preimage_basicOpen]`. Both sides reduce to the same expression.
-/
theorem isUnit_gs_iff (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : r z ∈ U) (a : Γ(Y, U)) :
    IsUnit (gs r z U a) ↔ r z ∈ Y.basicOpen a := by
  rw [gs_eq r z U h]
  refine (Z.mem_basicOpen (U := r ⁻¹ᵁ U) ((r.app U).hom a) z h).symm.trans ?_
  rw [← Scheme.preimage_basicOpen]
  rfl

/- English proof (translation)
Establish `hm` using `hJ.mem φ r`. Use `Opens.mem_iSup.trans ⟨fun ⟨j, hj⟩ => ?_, fun h => ⟨_, (isUnit_gs_iff r z _ hm _).1 h⟩⟩` and prove the remaining obligations. Establish `hj' : r z ∈ LB.wchart L φ j` using `Y.basicOpen_le _ hj`. Establish `u` using `(isUnit_gs_iff r z _ hj' _).2 hj`. Rewrite `u` using `[sec_trans s r z hj' hm]`.

Conclude with `isUnit_of_mul_isUnit_right u`.
-/
theorem mem_nonzeroLocus_iff {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z)
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) : r z ∈ Out.nonzeroLocus s ↔ IsUnit (sval s r z J) := by
  have hm := hJ.mem φ r
  refine Opens.mem_iSup.trans ⟨fun ⟨j, hj⟩ => ?_, fun h => ⟨_, (isUnit_gs_iff r z _ hm _).1 h⟩⟩
  have hj' : r z ∈ LB.wchart L φ j := Y.basicOpen_le _ hj
  have u := (isUnit_gs_iff r z _ hj' _).2 hj
  rw [sec_trans s r z hj' hm] at u
  exact isUnit_of_mul_isUnit_right u

def powGen {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (N : ℕ) :
    LB.Gen (LB.LinComb L φ (fun k => ε k * N)) where
  s := fun j => t.s j ^ N

/- English proof (translation)
Introduce `i j`. Establish `e` using `congrArg (· ^ N) (ht i j)`. Simplify using `only [mul_pow] at e`. Use `(map_pow _ _ _).trans (e.trans (congrArg₂ (· * ·) ?_ (map_pow _ _ _).symm))` and prove the remaining obligations. Use `(Finset.prod_pow _ _ _).symm.trans (Finset.prod_congr rfl fun k _ => ?_)` and prove the remaining obligations.

Rewrite using `[zpow_mul, zpow_natCast]`. Both sides reduce to the same expression.
-/
theorem powGen_isGen {φ : K → (Y ⟶ X)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) (N : ℕ) :
    (powGen t N).IsGen := by
  intro i j
  have e := congrArg (· ^ N) (ht i j)
  simp only [mul_pow] at e
  refine (map_pow _ _ _).trans (e.trans (congrArg₂ (· * ·) ?_ (map_pow _ _ _).symm))
  refine (Finset.prod_pow _ _ _).symm.trans (Finset.prod_congr rfl fun k _ => ?_)
  rw [zpow_mul, zpow_natCast]
  rfl

/- English proof (translation)
Take `⟨h', hh'⟩` from `exists_sec hL (φ' := fun _ : PUnit => 𝟙 X) (ε' := fun _ => (M : ℤ)) (fun U _ q => by`. Simplify using `only [Fintype.prod_sum_type, Fintype.prod_unique, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr, Category.comp_id, Matrix.cons_val_zero, Matrix.cons_val_one, hM, neg_mul, one_mul, zpow_neg]`. Rewrite using `[mul_left_comm, mul_inv_cancel, mul_one])`. Use the proof step `(pullMulSec h f (powGen α N) (powGen_isGen hα N))`. Use `⟨h', Opens.ext (Set.ext fun y => ?_)⟩` and prove the remaining obligations.

Use `choose J hJ using fun χ : X ⟶ X => exists_chart hL (χ y)`. Establish `a` using `mem_nonzeroLocus_iff h' (𝟙 X) y hJ`. Establish `b` using `mem_nonzeroLocus_iff h (𝟙 X ≫ f) y hJ`. Rewrite `a` using `[hh' _ _ y J hJ, sval_pullMulSec h f _ _ _ y hJ, Units.isUnit_mul_units]`. Conclude with `a.trans b.symm`.
-/
theorem exists_pull_sec (hL : L.IsLB) (f : X ⟶ X) (m : ℤ) (N M : ℕ) (hM : (M : ℤ) = m * N)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![m, -1])) (hα : α.IsGen) (h : (lbPow L N).Sec) :
    ∃ h' : (lbPow L M).Sec, Out.nonzeroLocus h' = f ⁻¹ᵁ Out.nonzeroLocus h := by
  obtain ⟨h', hh'⟩ := exists_sec hL (φ' := fun _ : PUnit => 𝟙 X) (ε' := fun _ => (M : ℤ))
    (fun U _ q => by
      simp only [Fintype.prod_sum_type, Fintype.prod_unique, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr,
        Category.comp_id, Matrix.cons_val_zero, Matrix.cons_val_one, hM, neg_mul, one_mul, zpow_neg]
      rw [mul_left_comm, mul_inv_cancel, mul_one])
    (pullMulSec h f (powGen α N) (powGen_isGen hα N))
  refine ⟨h', Opens.ext (Set.ext fun y => ?_)⟩
  choose J hJ using fun χ : X ⟶ X => exists_chart hL (χ y)
  have a := mem_nonzeroLocus_iff h' (𝟙 X) y hJ
  have b := mem_nonzeroLocus_iff h (𝟙 X ≫ f) y hJ
  rw [hh' _ _ y J hJ, sval_pullMulSec h f _ _ _ y hJ, Units.isUnit_mul_units] at a
  exact a.trans b.symm

end GlobalTheory.MulPullSec

namespace GlobalTheory

/- English proof (translation)
Introduce `K _ _ P N k h`. Take `⟨α, hα⟩` from `H (Sp K) P k`. Conclude with `MulPullSec.exists_pull_sec P.isLB _ ((k : ℤ) ^ 2) N _ (by push_cast; ring) α hα h`.
-/
theorem exists_mulPull_sec (H : Out.MulPullSt) :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N k : ℕ) (h : (lbPow P.L N).Sec),
      ∃ h' : (lbPow P.L (N * k ^ 2)).Sec, Out.nonzeroLocus h' = (Out.mulA P.A k).left ⁻¹ᵁ Out.nonzeroLocus h := by
  intro K _ _ P N k h
  obtain ⟨α, hα⟩ := H (Sp K) P k
  exact MulPullSec.exists_pull_sec P.isLB _ ((k : ℤ) ^ 2) N _ (by push_cast; ring) α hα h

end GlobalTheory
