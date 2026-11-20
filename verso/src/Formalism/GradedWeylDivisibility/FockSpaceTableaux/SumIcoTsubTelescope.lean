import Formalism.GradedWeylDivisibility.StatementA
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LBidetLemmas
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LBidetMinor

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

/- English proof (translation)
Introduce `d`. Proceed by induction on `d with`. Consider the case `zero`. Introduce `k hk`. Establish `hnk : n ≤ k` using `by omega`.

Rewrite using `[Finset.Ico_eq_empty_of_le hnk, Finset.sum_empty, hn k hnk]`. Consider the case `succ d ih`. Introduce `k hk`. Establish `hkn : k < n` using `by omega`. Rewrite using `[Finset.sum_eq_sum_Ico_succ_bot hkn, ih (k + 1) (by omega)]`.

Conclude with `Nat.sub_add_cancel (hg k)`.
-/
theorem sum_Ico_tsub_telescope (g : ℕ → ℕ) (n : ℕ) (hg : ∀ i, g (i + 1) ≤ g i)
    (hn : ∀ i, n ≤ i → g i = 0) :
    ∀ d k, n - k = d → ∑ i ∈ Finset.Ico k n, (g i - g (i + 1)) = g k := by
  intro d
  induction d with
  | zero =>
    intro k hk
    have hnk : n ≤ k := by omega
    rw [Finset.Ico_eq_empty_of_le hnk, Finset.sum_empty, hn k hnk]
  | succ d ih =>
    intro k hk
    have hkn : k < n := by omega
    rw [Finset.sum_eq_sum_Ico_succ_bot hkn, ih (k + 1) (by omega)]
    exact Nat.sub_add_cancel (hg k)

def extNu {n : ℕ} (ν : Fin n → ℕ) (k : ℕ) : ℕ := if h : k < n then ν ⟨k, h⟩ else 0

/- English proof (translation)
Establish `hg : ∀ i, extNu ν (i + 1) ≤ extNu ν i`. Introduce `i`. Unfold `extNu`. Distinguish the cases in `h1 : i + 1 < n`. Establish `h0 : i < n` using `by omega`.

Rewrite using `[dif_pos h1, dif_pos h0]`. Conclude with `hν (show (⟨i, h0⟩ : Fin n) ≤ ⟨i + 1, h1⟩ from Fin.mk_le_mk.mpr (Nat.le_succ i))`. Rewrite using `[dif_neg h1]`. Conclude with `Nat.zero_le _`. Establish `hz : ∀ i, n ≤ i → extNu ν i = 0`.

Introduce `i hi`. Establish `h0 : ¬ i < n` using `by omega`. Unfold `extNu`. Rewrite using `[dif_neg h0]`. Use function extensionality and compare the values at `t`.

Establish `key : ∀ s : Fin n, (ν s - nuNext ν s) * initW n (s.val + 1) t = (if t.val ≤ s.val then extNu ν s.val - extNu ν (s.val + 1) else 0)`. Introduce `s`. Establish `h1 : ν s = extNu ν s.val`. Unfold `extNu`. Rewrite using `[dif_pos s.isLt]`.

Establish `h2 : nuNext ν s = extNu ν (s.val + 1)` using `rfl`. Unfold `initW`. Rewrite using `[h1, h2]`. Distinguish the cases in `hts : t.val ≤ s.val`. Establish `h3 : t.val < s.val + 1` using `by omega`.

Simplify using `only [hts, h3, if_true, mul_one]`. Establish `h3 : ¬ t.val < s.val + 1` using `by omega`. Simplify using `only [hts, h3, if_false, mul_zero]`. Establish `hsum : ∑ s : Fin n, (ν s - nuNext ν s) * initW n (s.val + 1) t = ∑ i ∈ Finset.range n, (if t.val ≤ i then extNu ν i - extNu ν (i + 1) else 0)`. Rewrite using `[← Fin.sum_univ_eq_sum_range]`.

Conclude with `Finset.sum_congr rfl (fun s _ => key s)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_apply]`. Both sides reduce to the same expression. Use `_ = ∑ i ∈ Finset.range n, (if t.val ≤ i then extNu ν i - extNu ν (i + 1) else 0) := hsum`.

Use `_ = ∑ i ∈ Finset.range t.val, (if t.val ≤ i then extNu ν i - extNu ν (i + 1) else 0) + ∑ i ∈ Finset.Ico t.val n, (if t.val ≤ i then extNu ν i - extNu ν (i + 1) else 0) := (Finset.sum_range_add_sum_Ico (fun i => if t.val ≤ i then extNu ν i - extNu ν (i + 1) else 0) (le_of_lt t.isL …`. Use `_ = 0 + ∑ i ∈ Finset.Ico t.val n, (extNu ν i - extNu ν (i + 1)) := by`. Use `congr 1`. Use `Finset.sum_eq_zero (fun i hi => ?_)` and prove the remaining obligations. Rewrite `hi` using `[Finset.mem_range]`.

Establish `h0 : ¬ t.val ≤ i` using `by omega`. Conclude with `if_neg h0`. Conclude with `Finset.sum_congr rfl (fun i hi => if_pos (Finset.mem_Ico.mp hi).1)`. Use `_ = extNu ν t.val := by`. Rewrite using `[zero_add]`.

Conclude with `sum_Ico_tsub_telescope _ n hg hz (n - t.val) t.val rfl`. Use `_ = ν t := by`. Unfold `extNu`. Rewrite using `[dif_pos t.isLt]`.
-/
theorem hw_weight_eq {n : ℕ} (ν : Fin n → ℕ) (hν : Antitone ν) :
    (∑ s : Fin n, (ν s - nuNext ν s) • initW n (s.val + 1)) = ν := by
  have hg : ∀ i, extNu ν (i + 1) ≤ extNu ν i := by
    intro i
    unfold extNu
    by_cases h1 : i + 1 < n
    · have h0 : i < n := by omega
      rw [dif_pos h1, dif_pos h0]
      exact hν (show (⟨i, h0⟩ : Fin n) ≤ ⟨i + 1, h1⟩ from Fin.mk_le_mk.mpr (Nat.le_succ i))
    · rw [dif_neg h1]
      exact Nat.zero_le _
  have hz : ∀ i, n ≤ i → extNu ν i = 0 := by
    intro i hi
    have h0 : ¬ i < n := by omega
    unfold extNu
    rw [dif_neg h0]
  funext t
  have key : ∀ s : Fin n, (ν s - nuNext ν s) * initW n (s.val + 1) t =
      (if t.val ≤ s.val then extNu ν s.val - extNu ν (s.val + 1) else 0) := by
    intro s
    have h1 : ν s = extNu ν s.val := by
      unfold extNu
      rw [dif_pos s.isLt]
    have h2 : nuNext ν s = extNu ν (s.val + 1) := rfl
    unfold initW
    rw [h1, h2]
    by_cases hts : t.val ≤ s.val
    · have h3 : t.val < s.val + 1 := by omega
      simp only [hts, h3, if_true, mul_one]
    · have h3 : ¬ t.val < s.val + 1 := by omega
      simp only [hts, h3, if_false, mul_zero]
  have hsum : ∑ s : Fin n, (ν s - nuNext ν s) * initW n (s.val + 1) t
      = ∑ i ∈ Finset.range n,
          (if t.val ≤ i then extNu ν i - extNu ν (i + 1) else 0) := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl (fun s _ => key s)
  calc (∑ s : Fin n, (ν s - nuNext ν s) • initW n (s.val + 1)) t
      = ∑ s : Fin n, (ν s - nuNext ν s) * initW n (s.val + 1) t := by
        rw [Finset.sum_apply]
        rfl
    _ = ∑ i ∈ Finset.range n,
          (if t.val ≤ i then extNu ν i - extNu ν (i + 1) else 0) := hsum
    _ = ∑ i ∈ Finset.range t.val,
          (if t.val ≤ i then extNu ν i - extNu ν (i + 1) else 0) +
        ∑ i ∈ Finset.Ico t.val n,
          (if t.val ≤ i then extNu ν i - extNu ν (i + 1) else 0) :=
        (Finset.sum_range_add_sum_Ico
          (fun i => if t.val ≤ i then extNu ν i - extNu ν (i + 1) else 0)
          (le_of_lt t.isLt)).symm
    _ = 0 + ∑ i ∈ Finset.Ico t.val n, (extNu ν i - extNu ν (i + 1)) := by
        congr 1
        · refine Finset.sum_eq_zero (fun i hi => ?_)
          rw [Finset.mem_range] at hi
          have h0 : ¬ t.val ≤ i := by omega
          exact if_neg h0
        · exact Finset.sum_congr rfl (fun i hi => if_pos (Finset.mem_Ico.mp hi).1)
    _ = extNu ν t.val := by
        rw [zero_add]
        exact sum_Ico_tsub_telescope _ n hg hz (n - t.val) t.val rfl
    _ = ν t := by
        unfold extNu
        rw [dif_pos t.isLt]

/- English proof (translation)
Establish `h : lpMinor R s hr hn = initMinor R (Fin.castLE hr) hn` using `rfl`. Rewrite using `[h]`. Conclude with `initMinor_mem (Fin.castLE hr) hn`.
-/
theorem lpMinor_mem {R : Type*} [CommRing R] {r n : ℕ} (s : ℕ) (hr : s ≤ r) (hn : s ≤ n) :
    lpMinor R s hr hn ∈ dualWeyl R r n (initW n s) := by
  have h : lpMinor R s hr hn = initMinor R (Fin.castLE hr) hn := rfl
  rw [h]
  exact initMinor_mem (Fin.castLE hr) hn

/- English proof (translation)
Unfold `HWMem`. Introduce `R _ r n hn ν hν`. Unfold `hw`. Use `dualWeyl_of_eq ?_ (hw_weight_eq ν hν)` and prove the remaining obligations. Conclude with `dualWeyl_prod Finset.univ (fun s : Fin n => (ν s - nuNext ν s) • initW n (s.val + 1)) (fun s : Fin n => lpMinor R (s.val + 1) (by omega) (by omega) ^ (ν s - nuNext ν s)) (fun s _ => dualWeyl_pow (lpMinor_mem _ _ _) _)`.
-/
theorem highestWeightVectorMem : HWMem := by
  unfold HWMem
  intro R _ r n hn ν hν
  unfold hw
  refine dualWeyl_of_eq ?_ (hw_weight_eq ν hν)
  exact dualWeyl_prod Finset.univ
    (fun s : Fin n => (ν s - nuNext ν s) • initW n (s.val + 1))
    (fun s : Fin n =>
      lpMinor R (s.val + 1) (by omega) (by omega) ^ (ν s - nuNext ν s))
    (fun s _ => dualWeyl_pow (lpMinor_mem _ _ _) _)

end Formalism.GradedWeylDivisibility
