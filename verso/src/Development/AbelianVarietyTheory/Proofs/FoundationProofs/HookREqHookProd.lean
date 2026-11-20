import Mathlib
import Formalism.SharpRestriction.Divisibility.PlaceRankTwoOne
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.ThetaLift

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory.LiftSizeCompare

open GlobalTheory.IndefiniteRowSideFullHecke.SchurTensorLattices

/- English proof (translation)
Proceed by induction on `b with`. Consider the case `zero => simp`. Consider the case `succ b ih`. Rewrite using `[Finset.prod_range_succ, Finset.prod_range_succ]`. Establish `h1 : a - b - 1 + (k + 1) + 1 = a - b + k + 1` using `by omega`.

Establish `h2 : a - (b + 1) + k + 1 = a - b - 1 + k + 1` using `by omega`. Rewrite using `[h1, h2, ih (by omega)]`. Expand and normalize the polynomial expressions, which then agree.
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
Proceed by induction on `k with`. Consider the case `zero`. Establish `he : Finset.Ioo r (r + 1 + 0) = ∅`. Use extensionality with `x`. Simplify using `only [Finset.mem_Ioo, Finset.notMem_empty, iff_false]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[he, Finset.prod_empty, mul_one, Nat.add_zero]`. Simplify using `only [Finset.filter_empty, Finset.card_empty, add_zero]`. Rewrite using `[← Finset.prod_range_add_one_eq_factorial, ← Finset.prod_range_reflect]`. Use `Finset.prod_congr rfl fun c hc => ?_` and prove the remaining obligations.

Rewrite `hc` using `[Finset.mem_range]`. Use linear arithmetic over natural numbers and integers. Consider the case `succ k ih`. Establish `hν' : ∀ x y, x ≤ y → y < r + 1 + k → ν y ≤ ν x` using `fun x y hxy hy => hν x y hxy (by omega)`. Establish `IH` using `ih hν'`.

Use `set m := r + 1 + k with hm`. Establish `hIns : Finset.Ioo r (r + 1 + (k + 1)) = insert m (Finset.Ioo r m)`. Use extensionality with `x`. Simplify using `only [Finset.mem_Ioo, Finset.mem_insert]`. Use linear arithmetic over natural numbers and integers.

Establish `hmn : m ∉ Finset.Ioo r m` using `by simp`. Establish `hba : ν m ≤ ν r` using `hν r m (by omega) (by omega)`. Establish `hcardIoo : (Finset.Ioo r m).card = k` using `by rw [Nat.card_Ioo]; omega`. Rewrite using `[hIns, Finset.prod_insert hmn]`. Rewrite `IH`, the goal using `[← Finset.prod_range_mul_prod_Ico _ hba]`.

Establish `hlow : ∀ c ∈ Finset.range (ν m), ν r - c - 1 + ((insert m (Finset.Ioo r m)).filter (fun r' => c < ν r')).card + 1 = ν r - c - 1 + (k + 1) + 1`. Introduce `c hc`. Rewrite `hc` using `[Finset.mem_range]`. Rewrite using `[Finset.filter_insert, if_pos hc, Finset.card_insert_of_notMem (by simp), Finset.filter_true_of_mem (fun l hl => ?_), hcardIoo]`. Rewrite `hl` using `[Finset.mem_Ioo]`.

Conclude with `lt_of_lt_of_le hc (hν l m hl.2.le (by omega))`. Establish `hlow' : ∀ c ∈ Finset.range (ν m), ν r - c - 1 + ((Finset.Ioo r m).filter (fun r' => c < ν r')).card + 1 = ν r - c - 1 + k + 1`. Introduce `c hc`. Rewrite `hc` using `[Finset.mem_range]`. Rewrite using `[Finset.filter_true_of_mem (fun l hl => ?_), hcardIoo]`.

Rewrite `hl` using `[Finset.mem_Ioo]`. Conclude with `lt_of_lt_of_le hc (hν l m hl.2.le (by omega))`. Establish `hhigh : ∀ c ∈ Finset.Ico (ν m) (ν r), ν r - c - 1 + ((insert m (Finset.Ioo r m)).filter (fun r' => c < ν r')).card + 1 = ν r - c - 1 + ((Finset.Ioo r m).filter (fun r' => c < ν r')).card + 1`. Introduce `c hc`. Rewrite `hc` using `[Finset.mem_Ico]`.

Rewrite using `[Finset.filter_insert, if_neg (by omega)]`. Rewrite using `[Finset.prod_congr rfl hlow, Finset.prod_congr rfl hhigh]`. Rewrite `IH` using `[Finset.prod_congr rfl hlow']`. Establish `hT` using `telescope (ν r) k (ν m) hba`. Establish `hd : ν r - ν m + (m - r) = ν r - ν m + k + 1` using `by omega`.

Rewrite using `[hd, show ν r + (k + 1) = (ν r + k) + 1 by ring, Nat.factorial_succ, ← IH]`. Combine the equalities or inequalities in the displayed calculation.
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
Unfold `hookProd`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun r hr => ?_` and prove the remaining obligations. Establish `hr'` using `Finset.mem_range.1 hr`. Establish `e : r + 1 + (n - 1 - r) = n` using `by omega`.

Establish `h` using `row_hook ν r (n - 1 - r) (fun x y hxy hy => hν x y hxy (by omega))`. Rewrite `h` using `[e]`. Rewrite using `[h]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.
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
