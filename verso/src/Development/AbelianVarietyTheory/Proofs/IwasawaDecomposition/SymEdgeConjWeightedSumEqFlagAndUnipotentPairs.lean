import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OtherInstanceCharacterEqPsiSymmetricArgument
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SymChar.Comb

def cw (ρ k : ℕ) (s : Bool) (i : ℕ) : ℤ :=
  if ρ ≤ i ∧ i + 1 ≠ ρ + k then (if i + 1 < ρ + k then (if s then 0 else -1) else if i = ρ + k then 1 else -1) else 0

/- English proof (translation)
Unfold `symEdge GlobalTheory.Mem.SymChar.wtB cw`. Simplify using `only [Int.cast_ite, Int.cast_zero, Int.cast_one, Int.cast_neg]`. Apply the tactic sequence `split_ifs <;> first | rfl | omega | (simp_all; done) | simp`.
-/
theorem term_eq {R : Type} [CommRing R] (ρ k : ℕ) (s : Bool) {r : ℕ} (M : Matrix (Fin r) (Fin r) R) (i j : Fin r) :
    (if symEdge ρ k i j then ((GlobalTheory.Mem.SymChar.wtB ρ k s i j : ℤ) : R) * M i j else 0) =
      if j.val = i.val + 1 then ((cw ρ k s i.val : ℤ) : R) * M i j else 0 := by
  unfold symEdge GlobalTheory.Mem.SymChar.wtB cw
  simp only [Int.cast_ite, Int.cast_zero, Int.cast_one, Int.cast_neg]
  split_ifs <;> first | rfl | omega | (simp_all; done) | simp

/- English proof (translation)
Distinguish the cases in `h : i.val + 1 < r`. Rewrite using `[dif_pos h]`. Establish `: ∀ j : Fin r, (j.val = i.val + 1) ↔ j = ⟨i.val + 1, h⟩` using `fun j => by simp [Fin.ext_iff]`. Simplify using `only [this]`. Rewrite using `[Finset.sum_ite_eq']`.

Simplify using the standard rewrite rules. Rewrite using `[dif_neg h, mul_zero]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Rewrite using `[if_neg]`. Use linear arithmetic over natural numbers and integers.
-/
theorem row_sum {R : Type} [CommRing R] {r : ℕ} (M : Matrix (Fin r) (Fin r) R) (c : R) (i : Fin r) :
    (∑ j : Fin r, if j.val = i.val + 1 then c * M i j else 0) =
      c * (if h : i.val + 1 < r then M i ⟨i.val + 1, h⟩ else 0) := by
  by_cases h : i.val + 1 < r
  · rw [dif_pos h]
    have : ∀ j : Fin r, (j.val = i.val + 1) ↔ j = ⟨i.val + 1, h⟩ := fun j => by simp [Fin.ext_iff]
    simp only [this]
    rw [Finset.sum_ite_eq']
    simp
  · rw [dif_neg h, mul_zero]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg]; omega

/- English proof (translation)
Rewrite using `[← Finset.sum_range_add_sum_Ico _ (show ρ + k ≤ 2 * ρ + k by omega), ← Finset.sum_range_add_sum_Ico _ (show ρ ≤ ρ + k by omega), Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]`. Establish `h0 : (∑ i ∈ Finset.range ρ, ((cw ρ k s i : ℤ) : R) * F i) = 0` using `Finset.sum_eq_zero fun i hi => by`. Simplify using `only [Finset.mem_range] at hi`. Simplify using `[cw, show ¬ ρ ≤ i by omega]`. Establish `h1 : (∑ t ∈ Finset.range (2 * ρ + k - (ρ + k)), ((cw ρ k s (ρ + k + t) : ℤ) : R) * F (ρ + k + t)) = ∑ a ∈ Finset.range ρ, if a + 1 < ρ then -F (2 * ρ + k - a - 1) else F (ρ + k)`.

Rewrite using `[show 2 * ρ + k - (ρ + k) = ρ by omega, ← Finset.sum_range_reflect]`. Use `Finset.sum_congr rfl fun t ht => ?_` and prove the remaining obligations. Simplify using `only [Finset.mem_range] at ht`. Unfold `cw`. Distinguish the cases in `h : t + 1 < ρ`.

Rewrite using `[if_pos h, if_pos (show ρ ≤ ρ + k + (ρ - 1 - t) ∧ ρ + k + (ρ - 1 - t) + 1 ≠ ρ + k by omega), if_neg (show ¬ (ρ + k + (ρ - 1 - t) + 1 < ρ + k) by omega), if_neg (show ¬ (ρ + k + (ρ - 1 - t) = ρ + k) by omega), show ρ + k + (ρ - 1 - t) = 2 * ρ + k - t - 1 by omega]`. Simplify using the standard rewrite rules. Rewrite using `[if_neg h, if_pos (show ρ ≤ ρ + k + (ρ - 1 - t) ∧ ρ + k + (ρ - 1 - t) + 1 ≠ ρ + k by omega), if_neg (show ¬ (ρ + k + (ρ - 1 - t) + 1 < ρ + k) by omega), if_pos (show ρ + k + (ρ - 1 - t) = ρ + k by omega), show ρ + k + (ρ - 1 - t) = ρ + k by omega]`. Simplify using the standard rewrite rules. Establish `h2 : (∑ t ∈ Finset.range (ρ + k - ρ), ((cw ρ k s (ρ + t) : ℤ) : R) * F (ρ + t)) = if s then 0 else ∑ i ∈ Finset.range k, if i + 1 < k then -F (ρ + k - 2 - i) else 0`.

Rewrite using `[show ρ + k - ρ = k by omega]`. Consider the cases of `s`. Simplify using `only [Bool.false_eq_true, if_false]`. Rewrite using `[← Finset.sum_range_reflect (fun i => if i + 1 < k then -F (ρ + k - 2 - i) else 0) k]`. Break down `Nat.eq_zero_or_pos k with hk | hk` into its components or cases.

Substitute `hk` using the available equality. Simplify using the standard rewrite rules. Take `⟨k', rfl⟩ : ∃ k', k = k' + 1` from `⟨k - 1, by omega⟩`. Rewrite using `[Finset.sum_range_succ, Finset.sum_range_succ']`. Establish `e1 : ((cw ρ (k' + 1) false (ρ + k') : ℤ) : R) * F (ρ + k') = 0`.

Unfold `cw; rw [if_neg (by omega)]; simp`. Establish `e2 : (if k' + 1 - 1 - 0 + 1 < k' + 1 then -F (ρ + (k' + 1) - 2 - (k' + 1 - 1 - 0)) else 0) = (0 : R)`. Rewrite using `[if_neg (by omega)]`. Rewrite using `[e1, e2, add_zero, add_zero]`. Use `Finset.sum_congr rfl fun t ht => ?_` and prove the remaining obligations.

Simplify using `only [Finset.mem_range] at ht`. Rewrite using `[if_pos (show k' + 1 - 1 - (t + 1) + 1 < k' + 1 by omega), show ρ + (k' + 1) - 2 - (k' + 1 - 1 - (t + 1)) = ρ + t by omega]`. Simplify using `[cw, show ρ ≤ ρ + t ∧ ρ + t + 1 ≠ ρ + (k' + 1) by omega, show ρ + t + 1 < ρ + (k' + 1) by omega]`. Simplify using `only [if_true]`. Use `Finset.sum_eq_zero fun t ht => ?_` and prove the remaining obligations.

Simplify using `only [Finset.mem_range] at ht`. Unfold `cw`. Apply the tactic sequence `split_ifs <;> first | omega | simp_all`. Rewrite using `[h0, h1, h2, zero_add, add_comm]`.
-/
theorem nat_id {R : Type} [CommRing R] (ρ k : ℕ) (s : Bool) (F : ℕ → R) :
    (∑ i ∈ Finset.range (2 * ρ + k), ((cw ρ k s i : ℤ) : R) * F i) =
      (∑ a ∈ Finset.range ρ, if a + 1 < ρ then -F (2 * ρ + k - a - 1) else F (ρ + k)) +
        (if s then 0 else ∑ i ∈ Finset.range k, if i + 1 < k then -F (ρ + k - 2 - i) else 0) := by
  rw [← Finset.sum_range_add_sum_Ico _ (show ρ + k ≤ 2 * ρ + k by omega),
    ← Finset.sum_range_add_sum_Ico _ (show ρ ≤ ρ + k by omega),
    Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
  have h0 : (∑ i ∈ Finset.range ρ, ((cw ρ k s i : ℤ) : R) * F i) = 0 :=
    Finset.sum_eq_zero fun i hi => by
      simp only [Finset.mem_range] at hi
      simp [cw, show ¬ ρ ≤ i by omega]
  have h1 : (∑ t ∈ Finset.range (2 * ρ + k - (ρ + k)), ((cw ρ k s (ρ + k + t) : ℤ) : R) * F (ρ + k + t)) =
      ∑ a ∈ Finset.range ρ, if a + 1 < ρ then -F (2 * ρ + k - a - 1) else F (ρ + k) := by
    rw [show 2 * ρ + k - (ρ + k) = ρ by omega, ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun t ht => ?_
    simp only [Finset.mem_range] at ht
    unfold cw
    by_cases h : t + 1 < ρ
    · rw [if_pos h, if_pos (show ρ ≤ ρ + k + (ρ - 1 - t) ∧ ρ + k + (ρ - 1 - t) + 1 ≠ ρ + k by omega),
        if_neg (show ¬ (ρ + k + (ρ - 1 - t) + 1 < ρ + k) by omega),
        if_neg (show ¬ (ρ + k + (ρ - 1 - t) = ρ + k) by omega),
        show ρ + k + (ρ - 1 - t) = 2 * ρ + k - t - 1 by omega]
      simp
    · rw [if_neg h, if_pos (show ρ ≤ ρ + k + (ρ - 1 - t) ∧ ρ + k + (ρ - 1 - t) + 1 ≠ ρ + k by omega),
        if_neg (show ¬ (ρ + k + (ρ - 1 - t) + 1 < ρ + k) by omega),
        if_pos (show ρ + k + (ρ - 1 - t) = ρ + k by omega),
        show ρ + k + (ρ - 1 - t) = ρ + k by omega]
      simp
  have h2 : (∑ t ∈ Finset.range (ρ + k - ρ), ((cw ρ k s (ρ + t) : ℤ) : R) * F (ρ + t)) =
      if s then 0 else ∑ i ∈ Finset.range k, if i + 1 < k then -F (ρ + k - 2 - i) else 0 := by
    rw [show ρ + k - ρ = k by omega]
    cases s
    · simp only [Bool.false_eq_true, if_false]
      rw [← Finset.sum_range_reflect (fun i => if i + 1 < k then -F (ρ + k - 2 - i) else 0) k]
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; simp
      · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        rw [Finset.sum_range_succ, Finset.sum_range_succ']
        have e1 : ((cw ρ (k' + 1) false (ρ + k') : ℤ) : R) * F (ρ + k') = 0 := by
          unfold cw; rw [if_neg (by omega)]; simp
        have e2 : (if k' + 1 - 1 - 0 + 1 < k' + 1 then -F (ρ + (k' + 1) - 2 - (k' + 1 - 1 - 0)) else 0) = (0 : R) := by
          rw [if_neg (by omega)]
        rw [e1, e2, add_zero, add_zero]
        refine Finset.sum_congr rfl fun t ht => ?_
        simp only [Finset.mem_range] at ht
        rw [if_pos (show k' + 1 - 1 - (t + 1) + 1 < k' + 1 by omega),
          show ρ + (k' + 1) - 2 - (k' + 1 - 1 - (t + 1)) = ρ + t by omega]
        simp [cw, show ρ ≤ ρ + t ∧ ρ + t + 1 ≠ ρ + (k' + 1) by omega, show ρ + t + 1 < ρ + (k' + 1) by omega]
    · simp only [if_true]
      refine Finset.sum_eq_zero fun t ht => ?_
      simp only [Finset.mem_range] at ht
      unfold cw
      split_ifs <;> first | omega | simp_all
  rw [h0, h1, h2, zero_add, add_comm]

/- English proof (translation)
Introduce `R _ ρ k r hr s M`. Substitute `hr` using the available equality. Set `F : ℕ → R` to `fun i => if h : i + 1 < 2 * ρ + k + 1 then M ⟨i, by omega⟩ ⟨i + 1, h⟩ else 0`. Establish `hFv : ∀ i j (hi : i < 2 * ρ + k + 1) (hj : j < 2 * ρ + k + 1), j = i + 1 → F i = M ⟨i, hi⟩ ⟨j, hj⟩`. Introduce `i j hi hj e`.

Substitute `e` using the available equality. Simplify using `only [F]`. Rewrite using `[dif_pos hj]`. Establish `hL : (∑ i : Fin (2 * ρ + k + 1), ∑ j : Fin (2 * ρ + k + 1), if symEdge ρ k i j then ((GlobalTheory.Mem.SymChar.wtB ρ k s i j : ℤ) : R) * M i j else 0) = ∑ i : Fin (2 * ρ + k + 1), ((cw ρ k s i.val : ℤ) : R) * F i.val`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Simplify using `only [term_eq]`. Rewrite using `[row_sum]`. Rewrite using `[hL, Fin.sum_univ_eq_sum_range (fun i => ((cw ρ k s i : ℤ) : R) * F i), Finset.sum_range_succ, show F (2 * ρ + k) = 0 from dif_neg (by omega), mul_zero, add_zero, nat_id]`. Use `congr 1`. Use `(Fin.sum_univ_eq_sum_range (fun a => if a + 1 < ρ then -F (2 * ρ + k - a - 1) else F (ρ + k)) ρ).symm.trans (Finset.sum_congr rfl fun a _ => ?_) beta_reduce split_ifs with h` and prove the remaining obligations.

Rewrite using `[hFv _ (2 * ρ + k - a.val) (by omega) (by omega) (by omega)]`. Rewrite using `[hFv _ (ρ + k + 1) (by omega) (by omega) (by omega)]`. Consider the cases of `s`. Simplify using `only [Bool.false_eq_true, if_false]`. Use `(Fin.sum_univ_eq_sum_range (fun i => if i + 1 < k then -F (ρ + k - 2 - i) else 0) k).symm.trans (Finset.sum_congr rfl fun i _ => ?_)` and prove the remaining obligations.

Use `beta_reduce`. Use `split_ifs with h`. Rewrite using `[hFv _ (ρ + k - 1 - i.val) (by omega) (by omega) (by omega)]`. Both sides reduce to the same expression. Both sides reduce to the same expression.
-/
theorem weighted_sum_eq : ∀ {R : Type} [CommRing R] (ρ k r : ℕ) (hr : r = 2 * ρ + k + 1) (s : Bool) (M : Matrix (Fin r) (Fin r) R), (∑ i, ∑ j, if symEdge ρ k i j then ((GlobalTheory.Mem.SymChar.wtB ρ k s i j : ℤ) : R) * M i j else 0) = (∑ a : Fin ρ, if h : a.val + 1 < ρ then -M ⟨2 * ρ + k - a.val - 1, by omega⟩ ⟨2 * ρ + k - a.val, by omega⟩ else M ⟨ρ + k, by omega⟩ ⟨ρ + k + 1, by omega⟩) + (if s then 0 else ∑ i : Fin k, if h : i.val + 1 < k then -M ⟨ρ + k - 2 - i.val, by omega⟩ ⟨ρ + k - 1 - i.val, by omega⟩ else 0) := by
  intro R _ ρ k r hr s M
  subst hr
  let F : ℕ → R := fun i => if h : i + 1 < 2 * ρ + k + 1 then M ⟨i, by omega⟩ ⟨i + 1, h⟩ else 0
  have hFv : ∀ i j (hi : i < 2 * ρ + k + 1) (hj : j < 2 * ρ + k + 1), j = i + 1 → F i = M ⟨i, hi⟩ ⟨j, hj⟩ := by
    intro i j hi hj e; subst e; simp only [F]; rw [dif_pos hj]
  have hL : (∑ i : Fin (2 * ρ + k + 1), ∑ j : Fin (2 * ρ + k + 1), if symEdge ρ k i j then
      ((GlobalTheory.Mem.SymChar.wtB ρ k s i j : ℤ) : R) * M i j else 0) =
      ∑ i : Fin (2 * ρ + k + 1), ((cw ρ k s i.val : ℤ) : R) * F i.val := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [term_eq]
    rw [row_sum]
  rw [hL, Fin.sum_univ_eq_sum_range (fun i => ((cw ρ k s i : ℤ) : R) * F i), Finset.sum_range_succ,
    show F (2 * ρ + k) = 0 from dif_neg (by omega), mul_zero, add_zero, nat_id]
  congr 1
  · refine (Fin.sum_univ_eq_sum_range (fun a => if a + 1 < ρ then -F (2 * ρ + k - a - 1) else F (ρ + k)) ρ).symm.trans
      (Finset.sum_congr rfl fun a _ => ?_)
    beta_reduce
    split_ifs with h
    · rw [hFv _ (2 * ρ + k - a.val) (by omega) (by omega) (by omega)]
    · rw [hFv _ (ρ + k + 1) (by omega) (by omega) (by omega)]
  · cases s
    · simp only [Bool.false_eq_true, if_false]
      refine (Fin.sum_univ_eq_sum_range (fun i => if i + 1 < k then -F (ρ + k - 2 - i) else 0) k).symm.trans
        (Finset.sum_congr rfl fun i _ => ?_)
      beta_reduce
      split_ifs with h
      · rw [hFv _ (ρ + k - 1 - i.val) (by omega) (by omega) (by omega)]
      · rfl
    · rfl

end GlobalTheory.Mem.SymChar.Comb
