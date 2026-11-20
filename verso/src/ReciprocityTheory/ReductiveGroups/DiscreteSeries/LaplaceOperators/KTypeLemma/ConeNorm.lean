import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.QuotientHighestWeightTensorStandard
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.KhwLowKSubRootEqZero

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem cone_norm_dot_root {n : ℕ} (l : Fin n → ℝ) (a b : Fin n) (c : ℝ) :
    ∑ i, l i * (c • root a b) i = c * (l a - l b) := by
  unfold root
  simp [Pi.single_apply, mul_sub, Finset.sum_sub_distrib]
  try ring

/- English proof (translation)
Replace the relevant objects with their definitions. Extract witnesses or component facts from the available result. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem cone_norm_dot_nonneg {n : ℕ} (l β : Fin n → ℝ) (hl : Antitone l) (hβ : InRootCone β) :
    0 ≤ dot l β := by
  unfold dot
  obtain ⟨m, rfl⟩ := hβ
  have hsw : ∑ i, l i * (∑ a, ∑ b, if a < b then (m a b : ℝ) • root a b else 0) i
      = ∑ a, ∑ b, ∑ i, l i * ((if a < b then (m a b : ℝ) • root a b else 0) i) := by
    simp only [Finset.sum_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
  rw [hsw]
  refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
  split_ifs with hab
  · rw [cone_norm_dot_root]
    exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (hl hab.le))
  · simp

/- English proof (translation)
Replace the relevant objects with their definitions. Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. A detailed English derivation is pending.
-/
theorem cone_norm_eq_zero {n : ℕ} (β : Fin n → ℝ) (h : nsq β ≤ 0) : β = 0 := by
  unfold nsq dot at h
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ β i * β i := fun i _ => mul_self_nonneg _
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp (le_antisymm h (Finset.sum_nonneg hnn))
  funext i
  exact mul_self_eq_zero.mp (h0 i (Finset.mem_univ _))

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Expand and normalize the polynomial expressions, which then agree. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem cone_norm (n : ℕ) : ConeNormStatement n := by
  intro lam β hl hβ h
  apply cone_norm_eq_zero
  have hd := cone_norm_dot_nonneg lam β hl hβ
  have hexp : nsq (lam + β) = nsq lam + 2 * dot lam β + nsq β := by
    unfold nsq dot
    simp only [Pi.add_apply]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  linarith

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
