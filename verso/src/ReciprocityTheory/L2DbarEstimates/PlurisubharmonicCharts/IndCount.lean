import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.GROWCountStatement

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix

noncomputable section

universe u

open Finset

/- English proof (translation)
Unfold `multiLe`. Rewrite using `[Finset.mem_biUnion]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, hα⟩`. Rewrite `ha` using `[Finset.mem_range]`.

Rewrite `hα` using `[Nat.mem_antidiagonalTuple]`. Use linear arithmetic over natural numbers and integers. Introduce `h`. Conclude with `⟨∑ i, α i, Finset.mem_range.2 (by omega), Nat.mem_antidiagonalTuple.2 rfl⟩`.
-/
theorem mem_multiLe_iff {n j : ℕ} {α : Fin n → ℕ} : α ∈ multiLe n j ↔ ∑ i, α i ≤ j := by
  unfold multiLe
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨a, ha, hα⟩
    rw [Finset.mem_range] at ha
    rw [Nat.mem_antidiagonalTuple] at hα
    omega
  · intro h
    exact ⟨∑ i, α i, Finset.mem_range.2 (by omega), Nat.mem_antidiagonalTuple.2 rfl⟩

/- English proof (translation)
Rewrite using `[← Finset.card_sigma]`. Use `Finset.card_bij' (fun α _ => (⟨α 0, Fin.tail α⟩ : Σ _ : ℕ, Fin n → ℕ)) (fun p _ => (Fin.cons p.1 p.2 : Fin (n + 1) → ℕ)) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `α hα`. Simplify using `only [mem_multiLe_iff, Fin.sum_univ_succ] at hα`. Simplify using `only [Finset.mem_sigma, Finset.mem_range, mem_multiLe_iff, Fin.tail]`.

Conclude with `⟨by omega, by omega⟩`. Introduce and unpack `⟨a, β⟩ hp`. Simplify using `only [Finset.mem_sigma, Finset.mem_range, mem_multiLe_iff] at hp`. Simplify using `only [mem_multiLe_iff, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]`. Use linear arithmetic over natural numbers and integers.

Introduce `α _`. Conclude with `Fin.cons_self_tail α`. Introduce and unpack `⟨a, β⟩ _`. Simplify using `only [Fin.cons_zero, Fin.tail_cons]`.
-/
theorem card_multiLe_succ (n j : ℕ) :
    (multiLe (n + 1) j).card = ∑ a ∈ range (j + 1), (multiLe n (j - a)).card := by
  rw [← Finset.card_sigma]
  refine Finset.card_bij' (fun α _ => (⟨α 0, Fin.tail α⟩ : Σ _ : ℕ, Fin n → ℕ))
    (fun p _ => (Fin.cons p.1 p.2 : Fin (n + 1) → ℕ)) ?_ ?_ ?_ ?_
  · intro α hα
    simp only [mem_multiLe_iff, Fin.sum_univ_succ] at hα
    simp only [Finset.mem_sigma, Finset.mem_range, mem_multiLe_iff, Fin.tail]
    exact ⟨by omega, by omega⟩
  · rintro ⟨a, β⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_range, mem_multiLe_iff] at hp
    simp only [mem_multiLe_iff, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    omega
  · intro α _
    exact Fin.cons_self_tail α
  · rintro ⟨a, β⟩ _
    simp only [Fin.cons_zero, Fin.tail_cons]

/- English proof (translation)
Unfold `INDCountStatement`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `j`.

Establish `h : multiLe 0 j = {finZeroElim}`. Use extensionality with `α`. Simplify using `only [mem_multiLe_iff, Finset.mem_singleton, Fin.sum_univ_zero]`. Conclude with `⟨fun _ => funext fun i => i.elim0, fun _ => Nat.zero_le _⟩`. Rewrite using `[h, Finset.card_singleton]`.

Simplify using the standard rewrite rules. Consider the case `succ n ih`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero`.

Rewrite using `[card_multiLe_succ, Finset.sum_range_one, ih]`. Simplify using the standard rewrite rules. Consider the case `succ j ihj`. Rewrite using `[card_multiLe_succ, Finset.sum_range_succ']`. Simplify using `only [Nat.add_sub_add_right, Nat.sub_zero]`.

Rewrite using `[← card_multiLe_succ n j, ihj, ih (j + 1)]`. Establish `h1 : (j + (n + 1)).choose (n + 1) = (j + 1 + n).choose (n + 1)`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Establish `h2 : (j + 1 + (n + 1)).choose (n + 1) = (j + 1 + n).choose n + (j + 1 + n).choose (n + 1)`.

Rewrite using `[show j + 1 + (n + 1) = (j + 1 + n) + 1 by omega]`. Conclude with `Nat.choose_succ_succ' _ _`. Use linear arithmetic over natural numbers and integers.
-/
theorem ind_count : INDCountStatement := by
  unfold INDCountStatement
  intro n
  induction n with
  | zero =>
    intro j
    have h : multiLe 0 j = {finZeroElim} := by
      ext α
      simp only [mem_multiLe_iff, Finset.mem_singleton, Fin.sum_univ_zero]
      exact ⟨fun _ => funext fun i => i.elim0, fun _ => Nat.zero_le _⟩
    rw [h, Finset.card_singleton]
    simp
  | succ n ih =>
    intro j
    induction j with
    | zero =>
      rw [card_multiLe_succ, Finset.sum_range_one, ih]
      simp
    | succ j ihj =>
      rw [card_multiLe_succ, Finset.sum_range_succ']
      simp only [Nat.add_sub_add_right, Nat.sub_zero]
      rw [← card_multiLe_succ n j, ihj, ih (j + 1)]
      have h1 : (j + (n + 1)).choose (n + 1) = (j + 1 + n).choose (n + 1) := by
        congr 1
        omega
      have h2 : (j + 1 + (n + 1)).choose (n + 1) =
          (j + 1 + n).choose n + (j + 1 + n).choose (n + 1) := by
        rw [show j + 1 + (n + 1) = (j + 1 + n) + 1 by omega]
        exact Nat.choose_succ_succ' _ _
      omega

end

end ReciprocityTheory.L2DbarEstimates.Y
