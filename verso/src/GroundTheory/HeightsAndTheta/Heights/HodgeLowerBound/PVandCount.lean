import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsFlagGrassSteps
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

/- English proof (translation)
Rewrite using `[Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]`. Establish `h : ∀ b : Fin N, (∑ a : Fin N, if a < b then 1 else 0) = (b : ℕ)`. Introduce `b`. Rewrite using `[← Finset.card_filter, ← Fin.card_Iio b]`. Use `congr 1`.

Use extensionality with `a`. Simplify using the standard rewrite rules. Simplify using `only [h]`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun i => i) N, Finset.sum_range_id]`.
-/
theorem VandCount.card_lt (N : ℕ) :
    (Finset.univ.filter (fun ab : Fin N × Fin N => ab.1 < ab.2)).card = N * (N - 1) / 2 := by
  rw [Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]
  have h : ∀ b : Fin N, (∑ a : Fin N, if a < b then 1 else 0) = (b : ℕ) := by
    intro b
    rw [← Finset.card_filter, ← Fin.card_Iio b]
    congr 1
    ext a
    simp
  simp only [h]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) N, Finset.sum_range_id]

/- English proof (translation)
Establish `h1 : (Finset.univ.filter (fun a : Fin N => (a : ℕ) < j)).card = j`. Rewrite using `[Fin.card_filter_val_lt, min_eq_right hj]`. Establish `h2 : (Finset.univ.filter (fun a : Fin N => j ≤ (a : ℕ))).card = N - j`. Use `Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N))) (fun a : Fin N => (a : ℕ) < j)` as an intermediate fact. Simplify using `only [not_lt, Finset.card_univ, Fintype.card_fin] at this`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[← Finset.univ_product_univ, Finset.filter_product (fun a : Fin N => (a : ℕ) < j) (fun b : Fin N => j ≤ (b : ℕ)), Finset.card_product, h1, h2]`.
-/
theorem VandCount.card_cross (N j : ℕ) (hj : j ≤ N) :
    (Finset.univ.filter (fun ab : Fin N × Fin N => (ab.1 : ℕ) < j ∧ j ≤ (ab.2 : ℕ))).card = j * (N - j) := by
  have h1 : (Finset.univ.filter (fun a : Fin N => (a : ℕ) < j)).card = j := by
    rw [Fin.card_filter_val_lt, min_eq_right hj]
  have h2 : (Finset.univ.filter (fun a : Fin N => j ≤ (a : ℕ))).card = N - j := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N)))
      (fun a : Fin N => (a : ℕ) < j)
    simp only [not_lt, Finset.card_univ, Fintype.card_fin] at this
    omega
  rw [← Finset.univ_product_univ, Finset.filter_product (fun a : Fin N => (a : ℕ) < j)
    (fun b : Fin N => j ≤ (b : ℕ)), Finset.card_product, h1, h2]

/- English proof (translation)
Introduce `Ψ _ _ N j hj`. Unfold `dimN vandCount dimFl`. Establish `hc : Fintype.card (VandPair Ψ N j) = Fintype.card Ψ * (Finset.univ.filter (fun ab : Fin N × Fin N => ab.1 < ab.2 ∧ ((ab.1 : ℕ) < j ↔ (ab.2 : ℕ) < j))).card`. Rewrite using `[Fintype.card_subtype, ← Finset.card_univ (α := Ψ), ← Finset.card_product, Finset.univ_product_univ.symm, Finset.filter_product_right (fun ab : Fin N × Fin N => ab.1 < ab.2 ∧ ((ab.1 : ℕ) < j ↔ (ab.2 : ℕ) < j))]`. Establish `hsplit : (Finset.univ.filter (fun ab : Fin N × Fin N => ab.1 < ab.2)).card = (Finset.univ.filter (fun ab : Fin N × Fin N => ab.1 < ab.2 ∧ ((ab.1 : ℕ) < j ↔ (ab.2 : ℕ) < j))).card + (Finset.univ.filter (fun ab : Fin N × Fin N => (ab.1 : ℕ) < j ∧ j ≤ (ab.2 : ℕ))).card`.

Rewrite using `[← Finset.card_filter_add_card_filter_not (s := Finset.univ.filter (fun ab : Fin N × Fin N => ab.1 < ab.2)) (fun ab => ((ab.1 : ℕ) < j ↔ (ab.2 : ℕ) < j)), Finset.filter_filter, Finset.filter_filter]`. Use `congr 2`. Use extensionality with `ab`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨h1, h2⟩`. Distinguish the cases in `ha : (ab.1 : ℕ) < j`. Conclude with `⟨ha, by by_contra hb; exact h2 ⟨fun _ => by omega, fun _ => ha⟩⟩`. Conclude with `absurd ⟨fun h => absurd h ha, fun h => by omega⟩ h2`. Introduce and unpack `⟨h1, h2⟩`.

Conclude with `⟨by omega, fun h => by have := h.1 h1; omega⟩`. Rewrite using `[hc, ← VandCount.card_lt, hsplit, VandCount.card_cross N j hj]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem VandCount.proof : VandCount.Statement := by
  intro Ψ _ _ N j hj
  unfold dimN vandCount dimFl
  have hc : Fintype.card (VandPair Ψ N j) = Fintype.card Ψ *
      (Finset.univ.filter (fun ab : Fin N × Fin N =>
        ab.1 < ab.2 ∧ ((ab.1 : ℕ) < j ↔ (ab.2 : ℕ) < j))).card := by
    rw [Fintype.card_subtype, ← Finset.card_univ (α := Ψ), ← Finset.card_product, Finset.univ_product_univ.symm,
      Finset.filter_product_right (fun ab : Fin N × Fin N =>
        ab.1 < ab.2 ∧ ((ab.1 : ℕ) < j ↔ (ab.2 : ℕ) < j))]
  have hsplit : (Finset.univ.filter (fun ab : Fin N × Fin N => ab.1 < ab.2)).card =
      (Finset.univ.filter (fun ab : Fin N × Fin N =>
        ab.1 < ab.2 ∧ ((ab.1 : ℕ) < j ↔ (ab.2 : ℕ) < j))).card +
      (Finset.univ.filter (fun ab : Fin N × Fin N => (ab.1 : ℕ) < j ∧ j ≤ (ab.2 : ℕ))).card := by
    rw [← Finset.card_filter_add_card_filter_not (s := Finset.univ.filter
      (fun ab : Fin N × Fin N => ab.1 < ab.2)) (fun ab => ((ab.1 : ℕ) < j ↔ (ab.2 : ℕ) < j)),
      Finset.filter_filter, Finset.filter_filter]
    congr 2
    ext ab
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases ha : (ab.1 : ℕ) < j
      · exact ⟨ha, by by_contra hb; exact h2 ⟨fun _ => by omega, fun _ => ha⟩⟩
      · exact absurd ⟨fun h => absurd h ha, fun h => by omega⟩ h2
    · rintro ⟨h1, h2⟩
      exact ⟨by omega, fun h => by have := h.1 h1; omega⟩
  rw [hc, ← VandCount.card_lt, hsplit, VandCount.card_cross N j hj]
  ring

end GroundTheory.Heights₂.Heights.LowerBoundFree
