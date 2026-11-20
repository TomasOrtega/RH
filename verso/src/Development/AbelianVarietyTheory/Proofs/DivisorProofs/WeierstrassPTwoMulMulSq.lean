import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassCurvePointOfLatticeAddOfGeneric

open PeriodPair WeierstrassCurve

namespace GlobalTheory

/- English proof (translation)
Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

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
