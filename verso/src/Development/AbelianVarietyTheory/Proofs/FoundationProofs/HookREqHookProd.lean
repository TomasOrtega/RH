import Mathlib
import Formalism.SharpRestriction.Divisibility.PlaceRankTwoOne
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.ThetaLift

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory.LiftSizeCompare

open GlobalTheory.IndefiniteRowSideFullHecke.SchurTensorLattices

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem telescope (a k b : ℕ) (hb : b ≤ a) :
    (∏ c ∈ Finset.range b, (a - c - 1 + (k + 1) + 1)) * (a - b + k + 1) =
      (∏ c ∈ Finset.range b, (a - c - 1 + k + 1)) * (a + k + 1) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    have h1 : a - b - 1 + (k + 1) + 1 = a - b + k + 1 := by omega
    have h2 : a - (b + 1) + k + 1 = a - b - 1 + k + 1 := by omega
    rw [h1, h2, ih (by omega)]
    ring

/- English proof (translation)
Proceed by induction. Treat this case separately. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Use linear arithmetic over natural numbers and integers. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the indicated hypotheses using the stated equalities. Use linear arithmetic over natural numbers and integers. Treat this case separately. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
-/
theorem row_hook (ν : ℕ → ℕ) (r k : ℕ) (hν : ∀ x y, x ≤ y → y < r + 1 + k → ν y ≤ ν x) :
    (∏ c ∈ Finset.range (ν r),
        ((ν r - c - 1) + ((Finset.Ioo r (r + 1 + k)).filter (fun r' => c < ν r')).card + 1)) *
      ∏ l ∈ Finset.Ioo r (r + 1 + k), (ν r - ν l + (l - r)) = (ν r + k).factorial := by
  induction k with
  | zero =>
    have he : Finset.Ioo r (r + 1 + 0) = ∅ := by
      ext x
      simp only [Finset.mem_Ioo, Finset.notMem_empty, iff_false]
      omega
    rw [he, Finset.prod_empty, mul_one, Nat.add_zero]
    simp only [Finset.filter_empty, Finset.card_empty, add_zero]
    rw [← Finset.prod_range_add_one_eq_factorial, ← Finset.prod_range_reflect]
    refine Finset.prod_congr rfl fun c hc => ?_
    rw [Finset.mem_range] at hc
    omega
  | succ k ih =>
    have hν' : ∀ x y, x ≤ y → y < r + 1 + k → ν y ≤ ν x := fun x y hxy hy => hν x y hxy (by omega)
    have IH := ih hν'
    set m := r + 1 + k with hm
    have hIns : Finset.Ioo r (r + 1 + (k + 1)) = insert m (Finset.Ioo r m) := by
      ext x
      simp only [Finset.mem_Ioo, Finset.mem_insert]
      omega
    have hmn : m ∉ Finset.Ioo r m := by simp
    have hba : ν m ≤ ν r := hν r m (by omega) (by omega)
    have hcardIoo : (Finset.Ioo r m).card = k := by rw [Nat.card_Ioo]; omega
    rw [hIns, Finset.prod_insert hmn]
    rw [← Finset.prod_range_mul_prod_Ico _ hba] at IH ⊢
    have hlow : ∀ c ∈ Finset.range (ν m),
        ν r - c - 1 + ((insert m (Finset.Ioo r m)).filter (fun r' => c < ν r')).card + 1 =
          ν r - c - 1 + (k + 1) + 1 := by
      intro c hc
      rw [Finset.mem_range] at hc
      rw [Finset.filter_insert, if_pos hc, Finset.card_insert_of_notMem (by simp),
        Finset.filter_true_of_mem (fun l hl => ?_), hcardIoo]
      rw [Finset.mem_Ioo] at hl
      exact lt_of_lt_of_le hc (hν l m hl.2.le (by omega))
    have hlow' : ∀ c ∈ Finset.range (ν m),
        ν r - c - 1 + ((Finset.Ioo r m).filter (fun r' => c < ν r')).card + 1 =
          ν r - c - 1 + k + 1 := by
      intro c hc
      rw [Finset.mem_range] at hc
      rw [Finset.filter_true_of_mem (fun l hl => ?_), hcardIoo]
      rw [Finset.mem_Ioo] at hl
      exact lt_of_lt_of_le hc (hν l m hl.2.le (by omega))
    have hhigh : ∀ c ∈ Finset.Ico (ν m) (ν r),
        ν r - c - 1 + ((insert m (Finset.Ioo r m)).filter (fun r' => c < ν r')).card + 1 =
          ν r - c - 1 + ((Finset.Ioo r m).filter (fun r' => c < ν r')).card + 1 := by
      intro c hc
      rw [Finset.mem_Ico] at hc
      rw [Finset.filter_insert, if_neg (by omega)]
    rw [Finset.prod_congr rfl hlow, Finset.prod_congr rfl hhigh]
    rw [Finset.prod_congr rfl hlow'] at IH
    have hT := telescope (ν r) k (ν m) hba
    have hd : ν r - ν m + (m - r) = ν r - ν m + k + 1 := by omega
    rw [hd, show ν r + (k + 1) = (ν r + k) + 1 by ring, Nat.factorial_succ, ← IH]
    calc (∏ c ∈ Finset.range (ν m), (ν r - c - 1 + (k + 1) + 1)) *
          (∏ c ∈ Finset.Ico (ν m) (ν r),
            (ν r - c - 1 + ((Finset.Ioo r m).filter (fun r' => c < ν r')).card + 1)) *
          ((ν r - ν m + k + 1) * ∏ l ∈ Finset.Ioo r m, (ν r - ν l + (l - r)))
        = ((∏ c ∈ Finset.range (ν m), (ν r - c - 1 + (k + 1) + 1)) * (ν r - ν m + k + 1)) *
          (∏ c ∈ Finset.Ico (ν m) (ν r),
            (ν r - c - 1 + ((Finset.Ioo r m).filter (fun r' => c < ν r')).card + 1)) *
          ∏ l ∈ Finset.Ioo r m, (ν r - ν l + (l - r)) := by ring
      _ = _ := by rw [hT]; ring

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Use linear arithmetic over natural numbers and integers.
-/
theorem hookProd_mul (n : ℕ) (ν : ℕ → ℕ) (hν : ∀ x y, x ≤ y → y < n → ν y ≤ ν x) :
    hookProd n ν * ∏ r ∈ Finset.range n, ∏ l ∈ Finset.Ioo r n, (ν r - ν l + (l - r)) =
      ∏ r ∈ Finset.range n, (ν r + n - 1 - r).factorial := by
  unfold hookProd
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun r hr => ?_
  have hr' := Finset.mem_range.1 hr
  have e : r + 1 + (n - 1 - r) = n := by omega
  have h := row_hook ν r (n - 1 - r) (fun x y hxy hy => hν x y hxy (by omega))
  rw [e] at h
  rw [h]
  congr 1
  omega

variable (D : D7) (L : SizeData₂ D)

variable {eps : ℝ} (Fm : FamP eps)

end GlobalTheory.LiftSizeCompare

end
