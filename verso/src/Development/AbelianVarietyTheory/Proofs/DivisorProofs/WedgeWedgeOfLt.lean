import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar
open Matrix Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Pullback
open scoped ContDiff

set_option autoImplicit false

namespace GlobalTheory.TorsionForm.Pullback

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem sgn_erase_of_lt {m : ℕ} {i k : Fin m} (hik : i < k) (S : Finset (Fin m)) :
    sgn i (S.erase k) = sgn i S := by
  unfold sgn
  rw [Finset.filter_erase, Finset.erase_eq_of_notMem]
  simp only [Finset.mem_filter, not_and, not_lt]
  intro _; exact hik.le

/- English proof (translation)
Replace the relevant objects with their definitions. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem sgn_erase_of_gt {m : ℕ} {i k : Fin m} (hik : i < k) {S : Finset (Fin m)} (hi : i ∈ S) :
    sgn k (S.erase i) = -sgn k S := by
  unfold sgn
  have hm : i ∈ S.filter (· < k) := Finset.mem_filter.2 ⟨hi, hik⟩
  rw [Finset.filter_erase, Finset.card_erase_of_mem hm]
  obtain ⟨c, hc⟩ : ∃ c, (S.filter (· < k)).card = c + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (Finset.card_pos.2 ⟨i, hm⟩)).symm⟩
  rw [hc, Nat.add_sub_cancel, pow_succ]; ring

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem wedge_wedge_of_lt {m : ℕ} {i k : Fin m} (hik : i < k) (w : Ext m) :
    wedge i (wedge k w) = -wedge k (wedge i w) := by
  funext S
  have hne : i ≠ k := hik.ne
  simp only [wedge, Pi.neg_apply, Finset.mem_erase]
  by_cases hi : i ∈ S <;> by_cases hk : k ∈ S <;> simp [hi, hk, hne, hne.symm]
  rw [sgn_erase_of_lt hik, sgn_erase_of_gt hik hi, Finset.erase_right_comm]
  ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem wedge_anticomm : ∀ {m : ℕ} (i k : Fin m) (w : Ext m), wedge i (wedge k w) = -wedge k (wedge i w) := by
  intro m i k w
  rcases lt_trichotomy i k with h | rfl | h
  · exact wedge_wedge_of_lt h w
  · funext S
    simp [wedge]
  · rw [wedge_wedge_of_lt h w, neg_neg]

end GlobalTheory.TorsionForm.Pullback
