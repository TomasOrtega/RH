import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassCurvePointOfLatticeAddOfGeneric

namespace GlobalTheory

/- English proof (translation)
Establish `hne : L.weierstrassP z ≠ L.weierstrassP w`. Rewrite using `[Ne, weierstrassP_eq_iff L hz hw]`. The claim follows by propositional logic. Establish `e1` using `(weierstrassP_add L hz hw hne).1`. Establish `e2` using `(weierstrassP_add L (w := -w) hz (by simpa using hw) (by simpa using hne)).1`.

Rewrite `e2` using `[← sub_eq_add_neg, L.weierstrassP_neg, L.derivWeierstrassP_neg]`. Establish `hd : L.weierstrassP z - L.weierstrassP w ≠ 0` using `sub_ne_zero.mpr hne`. Rewrite using `[e1, e2]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem weierstrassP_add_sub_weierstrassP_sub (L : PeriodPair) (z w : ℂ) (hz : z ∉ L.lattice)
    (hw : w ∉ L.lattice) (h₁ : z - w ∉ L.lattice) (h₂ : z + w ∉ L.lattice) :
    (L.weierstrassP z - L.weierstrassP w) ^ 2 *
        (L.weierstrassP (z + w) - L.weierstrassP (z - w)) =
      -(L.derivWeierstrassP z * L.derivWeierstrassP w) := by
  have hne : L.weierstrassP z ≠ L.weierstrassP w := by
    rw [Ne, weierstrassP_eq_iff L hz hw]; tauto
  have e1 := (weierstrassP_add L hz hw hne).1
  have e2 := (weierstrassP_add L (w := -w) hz (by simpa using hw) (by simpa using hne)).1
  rw [← sub_eq_add_neg, L.weierstrassP_neg, L.derivWeierstrassP_neg] at e2
  have hd : L.weierstrassP z - L.weierstrassP w ≠ 0 := sub_ne_zero.mpr hne
  rw [e1, e2]
  field_simp
  ring

end GlobalTheory
