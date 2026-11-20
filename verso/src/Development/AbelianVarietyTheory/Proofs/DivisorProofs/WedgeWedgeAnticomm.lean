import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicConnectionAddSection
open Matrix Set Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm
open scoped Real ContDiff

namespace GlobalTheory.WedgeAnticomm

/- English proof (translation)
Unfold `sgn`. Rewrite using `[Finset.filter_erase]`. Use `split_ifs with h`. Establish `hm : i ∈ S.filter (· < k)` using `Finset.mem_filter.2 ⟨hi, h⟩`. Rewrite using `[Finset.card_erase_of_mem hm]`.

Establish `hpos : 0 < (S.filter (· < k)).card` using `Finset.card_pos.2 ⟨i, hm⟩`. Take `⟨c, hc⟩ : ∃ c, (S.filter (· < k)).card = c + 1` from `⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩`. Rewrite using `[hc, Nat.add_sub_cancel, pow_succ, mul_assoc]`. Evaluate the numerical expressions. Establish `hm : i ∉ S.filter (· < k)` using `fun h' => h (Finset.mem_filter.1 h').2`.

Rewrite using `[Finset.erase_eq_of_notMem hm, mul_one]`.
-/
theorem sgn_erase_of_mem {m : ℕ} {i : Fin m} (k : Fin m) {S : Finset (Fin m)} (hi : i ∈ S) :
    sgn k (S.erase i) = sgn k S * (if i < k then -1 else 1) := by
  unfold sgn
  rw [Finset.filter_erase]
  split_ifs with h
  · have hm : i ∈ S.filter (· < k) := Finset.mem_filter.2 ⟨hi, h⟩
    rw [Finset.card_erase_of_mem hm]
    have hpos : 0 < (S.filter (· < k)).card := Finset.card_pos.2 ⟨i, hm⟩
    obtain ⟨c, hc⟩ : ∃ c, (S.filter (· < k)).card = c + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
    rw [hc, Nat.add_sub_cancel, pow_succ, mul_assoc]; norm_num
  · have hm : i ∉ S.filter (· < k) := fun h' => h (Finset.mem_filter.1 h').2
    rw [Finset.erase_eq_of_notMem hm, mul_one]

/- English proof (translation)
Introduce `m i k w`. Use function extensionality and compare the values at `S`. Simplify using `only [wedge, Pi.neg_apply]`. Distinguish the cases in `hik : i = k`. Substitute `hik` using the available equality.

Simplify using the standard rewrite rules. Distinguish the cases in `hiS : i ∈ S`. Distinguish the cases in `hkS : k ∈ S`. Establish `hk' : k ∈ S.erase i` using `Finset.mem_erase.2 ⟨Ne.symm hik, hkS⟩`. Establish `hi' : i ∈ S.erase k` using `Finset.mem_erase.2 ⟨hik, hiS⟩`.

Rewrite using `[if_pos hiS, if_pos hk', if_pos hkS, if_pos hi', sgn_erase_of_mem k hiS, sgn_erase_of_mem i hkS, Finset.erase_right_comm]`. Break down `lt_or_gt_of_ne hik with h | h` into its components or cases. Rewrite using `[if_pos h, if_neg (not_lt.2 h.le)]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg (not_lt.2 h.le), if_pos h]`.

Expand and normalize the polynomial expressions, which then agree. Establish `: k ∉ S.erase i` using `fun h => hkS (Finset.mem_of_mem_erase h)`. Simplify using `[hiS, hkS, this]`. Establish `: i ∉ S.erase k` using `fun h => hiS (Finset.mem_of_mem_erase h)`. Simplify using `[hiS, this]`.
-/
theorem wedge_wedge_anticomm : ∀ {m : ℕ} (i k : Fin m) (w : Ext m),
    wedge i (wedge k w) = -wedge k (wedge i w) := by
  intro m i k w
  funext S
  simp only [wedge, Pi.neg_apply]
  by_cases hik : i = k
  · subst hik; simp
  by_cases hiS : i ∈ S
  · by_cases hkS : k ∈ S
    · have hk' : k ∈ S.erase i := Finset.mem_erase.2 ⟨Ne.symm hik, hkS⟩
      have hi' : i ∈ S.erase k := Finset.mem_erase.2 ⟨hik, hiS⟩
      rw [if_pos hiS, if_pos hk', if_pos hkS, if_pos hi', sgn_erase_of_mem k hiS,
        sgn_erase_of_mem i hkS, Finset.erase_right_comm]
      rcases lt_or_gt_of_ne hik with h | h
      · rw [if_pos h, if_neg (not_lt.2 h.le)]; ring
      · rw [if_neg (not_lt.2 h.le), if_pos h]; ring
    · have : k ∉ S.erase i := fun h => hkS (Finset.mem_of_mem_erase h)
      simp [hiS, hkS, this]
  · have : i ∉ S.erase k := fun h => hiS (Finset.mem_of_mem_erase h)
    simp [hiS, this]

end GlobalTheory.WedgeAnticomm
