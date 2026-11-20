import Formalism.GradedWeylDivisibility.StatementA
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LHwrowLemmas

namespace Formalism.GradedWeylDivisibility

open MvPolynomial

def hwrowExtNu {n : ℕ} (ν : Fin n → ℕ) (i : ℕ) : ℕ := if h : i < n then ν ⟨i, h⟩ else 0

/- English proof (translation)
Unfold `hwrowExtNu`. Distinguish the cases in `hj : j < n`. Establish `hi : i < n` using `lt_of_le_of_lt hij hj`. Rewrite using `[dif_pos hj, dif_pos hi]`. Use `first`.

Consider the case `exact hν (Fin.mk_le_mk.2 hij)`. Consider the case `exact hν (show (⟨i, hi⟩ : Fin n) ≤ ⟨j, hj⟩ from hij)`. Rewrite using `[dif_neg hj]`. Conclude with `Nat.zero_le _`.
-/
theorem extNu_anti {n : ℕ} {ν : Fin n → ℕ} (hν : Antitone ν) {i j : ℕ} (hij : i ≤ j) :
    hwrowExtNu ν j ≤ hwrowExtNu ν i := by
  unfold hwrowExtNu
  by_cases hj : j < n
  · have hi : i < n := lt_of_le_of_lt hij hj
    rw [dif_pos hj, dif_pos hi]
    first
    | exact hν (Fin.mk_le_mk.2 hij)
    | exact hν (show (⟨i, hi⟩ : Fin n) ≤ ⟨j, hj⟩ from hij)
  · rw [dif_neg hj]
    exact Nat.zero_le _

/- English proof (translation)
The claim follows from `| 0 => by simp | m + 1 => by rw [Finset.sum_range_succ, sum_range_tsub_from g hg a m] have h1 := hg m (m + 1) (by omega) rcases lt_trichotomy a m with ham | ham | ham · have h2 := hg a m ham.le rw [if_pos ham, if_pos ham.le, if_pos (by omega)] omega · subst ham rw [if_neg (lt_irr …`.
-/
theorem sum_range_tsub_from (g : ℕ → ℕ) (hg : ∀ i j, i ≤ j → g j ≤ g i) (a : ℕ) :
    ∀ m, (∑ i ∈ Finset.range m, if a ≤ i then g i - g (i + 1) else 0) =
      if a < m then g a - g m else 0
  | 0 => by simp
  | m + 1 => by
    rw [Finset.sum_range_succ, sum_range_tsub_from g hg a m]
    have h1 := hg m (m + 1) (by omega)
    rcases lt_trichotomy a m with ham | ham | ham
    · have h2 := hg a m ham.le
      rw [if_pos ham, if_pos ham.le, if_pos (by omega)]
      omega
    · subst ham
      rw [if_neg (lt_irrefl _), if_pos le_rfl, if_pos (by omega)]
      omega
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => classical`. Rewrite using `[pow_zero, zero_smul]`. Introduce `d hd`.

Establish `hd0 : d = 0`. Assume the negation of the conclusion as `h`. Conclude with `hd (by rw [MvPolynomial.coeff_one, if_neg (Ne.symm h)])`. Rewrite using `[hd0, map_zero]`. Consider the case `succ k ih`.

Rewrite using `[pow_succ, succ_nsmul]`. Conclude with `ih.mul hφ`.
-/
private theorem pow_nsmul' {σ M S : Type*} [CommSemiring S] [AddCommMonoid M]
    {w : σ → M} {φ : MvPolynomial σ S} {m : M} (hφ : IsWeightedHomogeneous w φ m) :
    ∀ k : ℕ, IsWeightedHomogeneous w (φ ^ k) (k • m) := by
  intro k
  induction k with
  | zero =>
    classical
    rw [pow_zero, zero_smul]
    intro d hd
    have hd0 : d = 0 := by
      by_contra h
      exact hd (by rw [MvPolynomial.coeff_one, if_neg (Ne.symm h)])
    rw [hd0, map_zero]
  | succ k ih =>
    rw [pow_succ, succ_nsmul]
    exact ih.mul hφ

/- English proof (translation)
Introduce `R inst r n hn ν hν`. Establish `hg : ∀ i j, i ≤ j → hwrowExtNu ν j ≤ hwrowExtNu ν i` using `fun i j hij => extNu_anti hν hij`. Establish `key : (rowNu (r` using `r) ν) = ∑ s : Fin n, (ν s - nuNext ν s) • (fun b : Fin r => if b.val < s.val + 1 then (1 : ℕ) else 0) := by`. Use function extensionality and compare the values at `a`. Establish `hterm : ∀ s : Fin n, (ν s - nuNext ν s) * (if a.val < s.val + 1 then (1 : ℕ) else 0) = (fun i : ℕ => if a.val ≤ i then hwrowExtNu ν i - hwrowExtNu ν (i + 1) else 0) s.val`.

Introduce `s`. Establish `hs : hwrowExtNu ν s.val = ν s` using `by first`. Consider the case `simp [hwrowExtNu, s.isLt]`. Consider the case `(unfold hwrowExtNu; rw [dif_pos s.isLt])`. Establish `hs' : nuNext ν s = hwrowExtNu ν (s.val + 1)` using `rfl`.

Rewrite using `[hs', ← hs]`. Distinguish the cases in `h : a.val ≤ s.val`. Establish `h' : a.val < s.val + 1` using `by omega`. Simplify using `[h, h']`. Establish `h' : ¬ a.val < s.val + 1` using `by omega`.

Simplify using `[h, h']`. Establish `hsum : (∑ s : Fin n, (ν s - nuNext ν s) • (fun b : Fin r => if b.val < s.val + 1 then (1 : ℕ) else 0)) a = if a.val < n then hwrowExtNu ν a.val - hwrowExtNu ν n else 0` using `by first`. Consider the case `rw [Finset.sum_apply]`. Consider the case `simp only [Finset.sum_apply]`. Use `Eq.trans ?_ ((Fin.sum_univ_eq_sum_range (fun i : ℕ => if a.val ≤ i then hwrowExtNu ν i - hwrowExtNu ν (i + 1) else 0) n).trans (sum_range_tsub_from (hwrowExtNu ν) hg a.val n))` and prove the remaining obligations.

Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Conclude with `hterm s`. Use `Eq.trans ?_ hsum.symm` and prove the remaining obligations. Distinguish the cases in `ha : a.val < n`.

Establish `h0 : hwrowExtNu ν n = 0` using `by first`. Consider the case `simp [hwrowExtNu]`. Consider the case `(unfold hwrowExtNu; rw [dif_neg (lt_irrefl n)])`. Rewrite using `[if_pos ha, h0, Nat.sub_zero]`. Apply the tactic sequence `all_goals first | rfl | simp [rowNu, hwrowExtNu, ha]`.

Rewrite using `[if_neg ha]`. Simplify using `[rowNu, ha]`. Rewrite using `[key]`. Unfold `hw`. Apply `IsWeightedHomogeneous.prod` to reduce the goal to its premises.

Introduce `s _`. Conclude with `pow_nsmul' (lpMinor_rowHom R (s.val + 1) (Nat.succ_le_of_lt (lt_of_lt_of_le s.isLt hn)) (Nat.succ_le_of_lt s.isLt)) _`.
-/
theorem highestWeightVectorRowWeight : HWRowWeight := by
  intro R inst r n hn ν hν
  have hg : ∀ i j, i ≤ j → hwrowExtNu ν j ≤ hwrowExtNu ν i :=
    fun i j hij => extNu_anti hν hij
  have key : (rowNu (r := r) ν) =
      ∑ s : Fin n, (ν s - nuNext ν s) • (fun b : Fin r => if b.val < s.val + 1 then (1 : ℕ) else 0) := by
    funext a
    have hterm : ∀ s : Fin n, (ν s - nuNext ν s) * (if a.val < s.val + 1 then (1 : ℕ) else 0) =
        (fun i : ℕ => if a.val ≤ i then hwrowExtNu ν i - hwrowExtNu ν (i + 1) else 0) s.val := by
      intro s
      have hs : hwrowExtNu ν s.val = ν s := by
        first
        | simp [hwrowExtNu, s.isLt]
        | (unfold hwrowExtNu; rw [dif_pos s.isLt])
      have hs' : nuNext ν s = hwrowExtNu ν (s.val + 1) := rfl
      rw [hs', ← hs]
      by_cases h : a.val ≤ s.val
      · have h' : a.val < s.val + 1 := by omega
        simp [h, h']
      · have h' : ¬ a.val < s.val + 1 := by omega
        simp [h, h']
    have hsum : (∑ s : Fin n, (ν s - nuNext ν s) •
        (fun b : Fin r => if b.val < s.val + 1 then (1 : ℕ) else 0)) a =
        if a.val < n then hwrowExtNu ν a.val - hwrowExtNu ν n else 0 := by
      first
      | rw [Finset.sum_apply]
      | simp only [Finset.sum_apply]
      refine Eq.trans ?_ ((Fin.sum_univ_eq_sum_range
        (fun i : ℕ => if a.val ≤ i then hwrowExtNu ν i - hwrowExtNu ν (i + 1) else 0) n).trans
        (sum_range_tsub_from (hwrowExtNu ν) hg a.val n))
      refine Finset.sum_congr rfl fun s _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul]
      exact hterm s
    refine Eq.trans ?_ hsum.symm
    by_cases ha : a.val < n
    · have h0 : hwrowExtNu ν n = 0 := by
        first
        | simp [hwrowExtNu]
        | (unfold hwrowExtNu; rw [dif_neg (lt_irrefl n)])
      rw [if_pos ha, h0, Nat.sub_zero]
      all_goals first | rfl | simp [rowNu, hwrowExtNu, ha]
    · rw [if_neg ha]
      simp [rowNu, ha]
  rw [key]
  unfold hw
  apply IsWeightedHomogeneous.prod
  intro s _
  exact pow_nsmul'
    (lpMinor_rowHom R (s.val + 1)
      (Nat.succ_le_of_lt (lt_of_lt_of_le s.isLt hn)) (Nat.succ_le_of_lt s.isLt)) _

end Formalism.GradedWeylDivisibility
