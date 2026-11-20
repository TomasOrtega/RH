import Formalism.GaussJetBounds.GenLogInverse
import Formalism.GaussJetBounds.StatementD

noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

/- English proof (translation)
Introduce `l a hl ha`. Use `set L := Nat.log l a with hLdef`. Establish `hsub : (Finset.Icc (-(a : ℤ)) a).filter (fun j => Odd j ∧ l ^ j.natAbs ≤ a) ⊆ Finset.Icc (-(L : ℤ)) L`. Introduce `j hj`. Simplify using `only [Finset.mem_filter, Finset.mem_Icc] at hj ⊢`.

Establish `h1 : j.natAbs ≤ L` using `Nat.le_log_of_pow_le (by omega) hj.2.2`. Apply the tactic sequence `rcases Int.natAbs_eq j with h | h <;> omega`. Establish `hcard` using `Finset.card_le_card hsub`. Rewrite `hcard` using `[Int.card_Icc]`. Establish `h2 : ((L : ℤ) + 1 - -(L : ℤ)).toNat = 2 * L + 1` using `by omega`.

Rewrite `hcard` using `[h2]`. Establish `hL : (L : ℝ) ≤ Real.logb l a` using `Real.natLog_le_logb a l`. Establish `h3 : ((((Finset.Icc (-(a : ℤ)) a).filter (fun j => Odd j ∧ l ^ j.natAbs ≤ a)).card : ℕ) : ℝ) ≤ ((2 * L + 1 : ℕ) : ℝ)` using `by exact_mod_cast hcard`. Move the coercions through the operations in `at h3`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem oddExponentCount : JCount := by
  intro l a hl ha
  set L := Nat.log l a with hLdef
  have hsub : (Finset.Icc (-(a : ℤ)) a).filter (fun j => Odd j ∧ l ^ j.natAbs ≤ a) ⊆
      Finset.Icc (-(L : ℤ)) L := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_Icc] at hj ⊢
    have h1 : j.natAbs ≤ L := Nat.le_log_of_pow_le (by omega) hj.2.2
    rcases Int.natAbs_eq j with h | h <;> omega
  have hcard := Finset.card_le_card hsub
  rw [Int.card_Icc] at hcard
  have h2 : ((L : ℤ) + 1 - -(L : ℤ)).toNat = 2 * L + 1 := by omega
  rw [h2] at hcard
  have hL : (L : ℝ) ≤ Real.logb l a := Real.natLog_le_logb a l
  have h3 : ((((Finset.Icc (-(a : ℤ)) a).filter (fun j => Odd j ∧ l ^ j.natAbs ≤ a)).card : ℕ) : ℝ)
      ≤ ((2 * L + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
  push_cast at h3
  linarith

section DegProdSec

variable {σ κ : Type} [DecidableEq κ] (blk : σ → Option κ)

def bdeg (k : κ) (mono : σ →₀ ℕ) : ℕ := (mono.support.filter (fun v => blk v = some k)).sum mono

end DegProdSec

section BasisSec

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

/- English proof (translation)
Rewrite using `[Matrix.det_apply]`. Apply `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one` to reduce the goal to its premises. Introduce `p _`. Establish `hp : ‖∏ i, M (p i) i‖ ≤ 1`. Rewrite using `[norm_prod]`.

Conclude with `Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun i _ => h _ _)`. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign p) with hs | hs <;> rw [hs]`. Rewrite using `[one_smul]`. Conclude with `hp`. Rewrite using `[Units.neg_smul, one_smul, norm_neg]`.

Conclude with `hp`.
-/
lemma norm_det_le_one_of_entries {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n K)
    (h : ∀ i j, ‖M i j‖ ≤ 1) : ‖M.det‖ ≤ 1 := by
  rw [Matrix.det_apply]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
  intro p _
  have hp : ‖∏ i, M (p i) i‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun i _ => h _ _)
  rcases Int.units_eq_one_or (Equiv.Perm.sign p) with hs | hs <;> rw [hs]
  · rw [one_smul]; exact hp
  · rw [Units.neg_smul, one_smul, norm_neg]; exact hp

/- English proof (translation)
Rewrite using `[Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv, hd, inv_one, one_mul, Matrix.adjugate_apply]`. Apply `norm_det_le_one_of_entries` to reduce the goal to its premises. Introduce `a b`. Rewrite using `[Matrix.updateRow_apply]`. Use `split_ifs`.

Apply the tactic sequence `rw [Pi.single_apply] split_ifs <;> simp`. Conclude with `h _ _`.
-/
lemma norm_inv_entry_le_one {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n K)
    (h : ∀ i j, ‖M i j‖ ≤ 1) (hd : ‖M.det‖ = 1) (i j : n) : ‖M⁻¹ i j‖ ≤ 1 := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv,
    hd, inv_one, one_mul, Matrix.adjugate_apply]
  apply norm_det_le_one_of_entries
  intro a b
  rw [Matrix.updateRow_apply]
  split_ifs
  · rw [Pi.single_apply]
    split_ifs <;> simp
  · exact h _ _

end BasisSec

end Formalism.DworkPowerSeriesWeights
