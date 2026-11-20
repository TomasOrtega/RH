import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FiniteInterClosedBallOfSeparated
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.LemmaS

namespace GlobalTheory

/- English proof (translation)
Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem _root_.GlobalTheory.packingCount : _root_.ReciprocityTheory.ChartRestriction.G.I2.Ext.PackingCount := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.Ext.PackingCount
  intro n P δ R hδ hR hP hsep
  have h1 := _root_.GlobalTheory.finset_card_le_of_separated P hδ (hδ.le.trans hR) 0
    (by simpa [dist_zero_right] using hP) (fun x hx y hy hxy => hsep x hx y hy hxy)
  rw [finrank_euclideanSpace_fin] at h1
  exact h1.trans (_root_.GlobalTheory.one_add_two_mul_div_pow_le hδ hR n)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem _root_.GlobalTheory.sup_le_l2_principal_torus : _root_.ReciprocityTheory.ChartRestriction.G.I2.GSupStatement := _root_.ReciprocityTheory.ChartRestriction.G.I2.gSup _root_.GlobalTheory.packingCount

end GlobalTheory
