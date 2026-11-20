import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassCurvePointOfLatticeAddOfGeneric

open PeriodPair WeierstrassCurve

namespace GlobalTheory

/- English proof (translation)
Rewrite `h2`, the goal using `[two_mul z]`. Establish `hd : L.derivWeierstrassP z ≠ 0` using `(derivWeierstrassP_eq_zero_iff L hz).not.mpr h2`. Establish `hy : L.derivWeierstrassP z / 2 ≠ (latticeCurve L).toAffine.negY (L.weierstrassP z) (L.derivWeierstrassP z / 2)`. Introduce `h`. Apply `hd` to reduce the goal to its premises.

Simplify using `only [Affine.negY, latticeCurve] at h`. Take the linear combination `h`. Establish `h` using `latticePoint_add L z z`. Rewrite `h` using `[latticePoint_of_notMem L hz, latticePoint_of_notMem L h2, Affine.Point.add_self_of_Y_ne hy, Affine.Point.some.injEq]`. Establish `e` using `h.1`.

Rewrite `e` using `[Affine.slope_of_Y_ne rfl hy]`. Simplify using `only [Affine.negY, Affine.addX, latticeCurve] at e`. Establish `e2 : L.derivWeierstrassP z / 2 - (-(L.derivWeierstrassP z / 2) - 0 * L.weierstrassP z - 0) = L.derivWeierstrassP z` using `by ring`. Rewrite `e` using `[e2]`. Rewrite using `[e]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem weierstrassP_two_mul_mul_sq (L : PeriodPair) (z : ℂ) (hz : z ∉ L.lattice)
    (h2 : 2 * z ∉ L.lattice) :
    L.weierstrassP (2 * z) * L.derivWeierstrassP z ^ 2 =
      (6 * L.weierstrassP z ^ 2 - L.g₂ / 2) ^ 2 / 4 -
        2 * L.weierstrassP z * L.derivWeierstrassP z ^ 2 := by
  rw [two_mul z] at h2 ⊢
  have hd : L.derivWeierstrassP z ≠ 0 := (derivWeierstrassP_eq_zero_iff L hz).not.mpr h2
  have hy : L.derivWeierstrassP z / 2 ≠
      (latticeCurve L).toAffine.negY (L.weierstrassP z) (L.derivWeierstrassP z / 2) := by
    intro h
    apply hd
    simp only [Affine.negY, latticeCurve] at h
    linear_combination h
  have h := latticePoint_add L z z
  rw [latticePoint_of_notMem L hz, latticePoint_of_notMem L h2,
    Affine.Point.add_self_of_Y_ne hy, Affine.Point.some.injEq] at h
  have e := h.1
  rw [Affine.slope_of_Y_ne rfl hy] at e
  simp only [Affine.negY, Affine.addX, latticeCurve] at e
  have e2 : L.derivWeierstrassP z / 2 -
      (-(L.derivWeierstrassP z / 2) - 0 * L.weierstrassP z - 0) = L.derivWeierstrassP z := by ring
  rw [e2] at e
  rw [e]
  field_simp
  ring

end GlobalTheory
