import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.SpanCup

noncomputable section

namespace PositivityTheory.KB.SplitAffineSpectral.PrismSpan

open PositivityTheory.KB.SplitAffineSpectral

variable {P : Type} [Group P]

def levSum (t : P) (lev : P → ℤ) {n : ℕ} (w : (Fin (n + 1) → P) → ℝ) (y : Fin (n + 1) → P) : ℝ :=
  if 0 ≤ lev (y 0) then ∑ j ∈ Finset.range (lev (y 0)).toNat, w (fun i => t ^ (-((j : ℤ) + 1)) * y i)
  else -∑ j ∈ Finset.range (-lev (y 0)).toNat, w (fun i => t ^ (j : ℤ) * y i)

/- English proof (translation)
Unfold `levSum`. Establish `e : ∀ k : ℤ, (fun i => t ^ k * (t * y i)) = fun i => t ^ (k + 1) * y i`. Introduce `k`. Use function extensionality and compare the values at `i`. Rewrite using `[← mul_assoc, ← zpow_add_one]`.

Simplify using `only [hlev, e]`. Generalize the expression as in `lev (y 0) = a`. Break down `le_or_gt 0 a with h | h` into its components or cases. Take `⟨m, rfl⟩` from `Int.eq_ofNat_of_zero_le h`. Rewrite using `[if_pos (by omega), if_pos h]`.

Rewrite using `[show ((m : ℤ) + 1).toNat = m + 1 by omega, Int.toNat_natCast, Finset.sum_range_succ']`. Establish `ex : ∀ j : ℕ, -(((j + 1 : ℕ) : ℤ) + 1) + 1 = -((j : ℤ) + 1)`. Introduce `j`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [ex]`. Simplify using the standard rewrite rules. Take `⟨m, rfl⟩` from `Int.eq_negSucc_of_lt_zero h`. Break down `m with _ | k` into its components or cases. Rewrite using `[if_pos (by omega), if_neg (by omega)]`.

Simplify using the standard rewrite rules. Rewrite using `[if_neg (by omega), if_neg (by omega)]`. Rewrite using `[show (-(Int.negSucc (k + 1) + 1)).toNat = k + 1 by omega, show (-Int.negSucc (k + 1)).toNat = k + 1 + 1 by omega, Finset.sum_range_succ' _ (k + 1)]`. Establish `ex : ∀ j : ℕ, ((j : ℤ) + 1) = ((j + 1 : ℕ) : ℤ)`. Introduce `j`.

Use `push_cast`. Both sides reduce to the same expression. Simplify using `only [ex]`. Simplify using the standard rewrite rules.
-/
theorem levSum_spec (t : P) (lev : P → ℤ) (hlev : ∀ z, lev (t * z) = lev z + 1) {n : ℕ}
    (w : (Fin (n + 1) → P) → ℝ) (y : Fin (n + 1) → P) :
    levSum t lev w (fun i => t * y i) - levSum t lev w y = w y := by
  unfold levSum
  have e : ∀ k : ℤ, (fun i => t ^ k * (t * y i)) = fun i => t ^ (k + 1) * y i := by
    intro k
    funext i
    rw [← mul_assoc, ← zpow_add_one]
  simp only [hlev, e]
  generalize lev (y 0) = a
  rcases le_or_gt 0 a with h | h
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
    rw [if_pos (by omega), if_pos h]
    rw [show ((m : ℤ) + 1).toNat = m + 1 by omega, Int.toNat_natCast, Finset.sum_range_succ']
    have ex : ∀ j : ℕ, -(((j + 1 : ℕ) : ℤ) + 1) + 1 = -((j : ℤ) + 1) := by
      intro j
      push_cast
      ring
    simp only [ex]
    simp
  · obtain ⟨m, rfl⟩ := Int.eq_negSucc_of_lt_zero h
    rcases m with _ | k
    · rw [if_pos (by omega), if_neg (by omega)]
      simp
    · rw [if_neg (by omega), if_neg (by omega)]
      rw [show (-(Int.negSucc (k + 1) + 1)).toNat = k + 1 by omega,
        show (-Int.negSucc (k + 1)).toNat = k + 1 + 1 by omega, Finset.sum_range_succ' _ (k + 1)]
      have ex : ∀ j : ℕ, ((j : ℤ) + 1) = ((j + 1 : ℕ) : ℤ) := by
        intro j
        push_cast
        rfl
      simp only [ex]
      simp

/- English proof (translation)
Introduce `g hg y`. Unfold `levSum`. Simplify using `only [hS g hg]`. Establish `hk : ∀ k : ℤ, (fun i => t ^ k * (g * y i)) = fun i => g * (t ^ k * y i)`. Introduce `k`.

Use function extensionality and compare the values at `i`. Rewrite using `[← mul_assoc, ← mul_assoc, ((Commute.zpow_right (hc g hg) k)).eq]`. Simplify using `only [hk, hw g hg]`.
-/
theorem levSum_inv (t : P) (lev : P → ℤ) (S : Set P) (hS : ∀ g ∈ S, ∀ z, lev (g * z) = lev z)
    (hc : ∀ g ∈ S, g * t = t * g) {n : ℕ} (w : (Fin (n + 1) → P) → ℝ) (hw : InvS S w) :
    InvS S (levSum t lev w) := by
  intro g hg y
  unfold levSum
  simp only [hS g hg]
  have hk : ∀ k : ℤ, (fun i => t ^ k * (g * y i)) = fun i => g * (t ^ k * y i) := by
    intro k; funext i
    rw [← mul_assoc, ← mul_assoc, ((Commute.zpow_right (hc g hg) k)).eq]
  simp only [hk, hw g hg]

end PositivityTheory.KB.SplitAffineSpectral.PrismSpan

end
