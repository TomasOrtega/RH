import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.VdmSplit

open GlobalTheory.PsCo.PcEG

namespace GlobalTheory.PsCo.PcEG

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem numShift_holds : NumShift := by
  intro n ε m c t ht
  unfold ReciprocityTheory.ChartRestriction.TR.Weyl.numK
  have hfilt : (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ i, ε (σ i) = ε i)) =
      Finset.univ.filter (fun w : Equiv.Perm (Fin n) => ε ∘ w = ε) := by
    ext w; simp [funext_iff]
  rw [hfilt, Finset.sum_mul]
  refine Finset.sum_congr rfl fun w hw => ?_
  have hw' : ∀ i, ε (w i) = ε i := fun i => congrFun (Finset.mem_filter.1 hw).2 i
  rw [mul_assoc]
  congr 1
  have h1 : ∏ i, t (w i) ^ (m i - c (ε i)) =
      (∏ i, t (w i) ^ m i) * ∏ i, t (w i) ^ (-c (ε (w i))) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hw', sub_eq_add_neg, zpow_add₀ (ht _)]
  rw [h1]
  congr 1
  · have := Equiv.prod_comp w (fun a => t a ^ m (w.symm a))
    simpa using this
  · exact Equiv.prod_comp w (fun a => t a ^ (-c (ε a)))

end GlobalTheory.PsCo.PcEG
