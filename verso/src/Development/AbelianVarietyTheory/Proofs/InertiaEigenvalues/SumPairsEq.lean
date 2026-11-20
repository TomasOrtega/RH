import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocFacOfNeg
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside

namespace GlobalTheory.WeightSumSplit

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the equality to equality of the corresponding arguments. Use linear arithmetic over natural numbers and integers.
-/
theorem sum_above {N : ℕ} (i : Fin N) (c : ℤ) :
    (∑ j : Fin N, if i < j then c else 0) = ((N : ℤ) - 1 - (i : ℕ)) * c := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, Finset.filter_lt_eq_Ioi,
    Fin.card_Ioi, nsmul_eq_mul]
  have hi := i.isLt
  congr 1
  omega

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem sum_below {N : ℕ} (j : Fin N) (c : ℤ) :
    (∑ i : Fin N, if i < j then c else 0) = ((j : ℕ) : ℤ) * c := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, Finset.filter_gt_eq_Iio,
    Fin.card_Iio, nsmul_eq_mul]

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion repeatedly using the stated equalities. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion repeatedly using the stated equalities. Reduce the conclusion to the remaining proof obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_pairs_eq (N : ℕ) (a : Fin N → ℤ) :
    (∑ i : Fin N, ∑ j : Fin N, if i < j then a i - a j else 0)
      = ∑ i : Fin N, ((N : ℤ) - 1 - 2 * ((i : ℕ) : ℤ)) * a i := by
  have h1 : ∀ i j : Fin N, (if i < j then a i - a j else 0) =
      (if i < j then a i else 0) - (if i < j then a j else 0) := by
    intro i j
    split_ifs <;> simp
  simp_rw [h1, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun i j : Fin N => if i < j then a j else 0)]
  simp_rw [sum_above, sum_below, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem wtS_eq : ∀ (N : ℕ) (a : Fin N → ℤ),
    GlobalTheory.CellDec.wtS N a = ∑ i : Fin N, ((↑N : ℤ) - (1 : ℤ) - (2 : ℤ) * (↑(↑i : ℕ) : ℤ)) * a i := by
  intro N a
  unfold GlobalTheory.CellDec.wtS
  exact sum_pairs_eq N a

end GlobalTheory.WeightSumSplit
