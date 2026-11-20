import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackPullback
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.StepShape

/- English proof (translation)
Introduce `N j a b ca cb C hj hb hcase hca hcb hbd hv r c hcr hne`. Establish `hr` using `r.2`. Establish `hc` using `c.2`. Establish `ha` using `a.2`. Establish `hb'` using `b.2`.

Establish `hcb'` using `cb.2`. Establish `hlt : (c : ℕ) < r` using `hcr`. Establish `hba : b ≠ a`. Introduce `h`. Rewrite `hb` using `[h]`.

Use linear arithmetic over natural numbers and integers. Unfold `lastCol at hca`. Distinguish the cases in `hs : ((r : ℕ) < N - j ↔ (c : ℕ) < N - j)`. Use `swap`. Conclude with `hbd r c hs`.

Distinguish the cases in `hW : N - j ≤ (c : ℕ)`. Take `⟨i, hi⟩ : ∃ i : Fin N, (i : ℕ) = c - (N - j)` from `⟨⟨(c : ℕ) - (N - j), by omega⟩, rfl⟩`. Distinguish the cases in `hia : i = a`. Establish `hai : (a : ℕ) = c - (N - j)` using `by rw [← hia]; exact hi`. Rewrite `hca` using `[if_pos (by omega)]`.

Establish `hcc : c = ca` using `Fin.ext (by omega)`. Establish `hrcb : (r : ℕ) ≠ cb` using `fun h => hne ⟨Fin.ext h, hcc⟩`. Use `hv b ⟨by omega, by omega⟩ hba r c ?_ ?_` and prove the remaining obligations. Simplify using `only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]`. Rewrite using `[if_pos (by omega)]`.

Use linear arithmetic over natural numbers and integers. Simplify using `only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]`. Rewrite using `[if_pos (by omega)]`. Use linear arithmetic over natural numbers and integers. Use `hv i ⟨by omega, by omega⟩ hia r c ?_ ?_` and prove the remaining obligations.

Simplify using `only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]`. Rewrite using `[if_pos (by omega)]`. Use linear arithmetic over natural numbers and integers. Simplify using `only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]`. Rewrite using `[if_pos (by omega)]`.

Use linear arithmetic over natural numbers and integers. Take `⟨i, hi⟩ : ∃ i : Fin N, (i : ℕ) = j + c` from `⟨⟨j + (c : ℕ), by omega⟩, rfl⟩`. Distinguish the cases in `hia : i = a`. Establish `hai : (a : ℕ) = j + c` using `by rw [← hia]; exact hi`. Rewrite `hca` using `[if_neg (by omega)]`.

Establish `hcc : c = ca` using `Fin.ext (by omega)`. Establish `hrcb : (r : ℕ) ≠ cb` using `fun h => hne ⟨Fin.ext h, hcc⟩`. Use `hv b ⟨by omega, by omega⟩ hba r c ?_ ?_` and prove the remaining obligations. Simplify using `only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]`. Rewrite using `[if_neg (by omega)]`.

Use linear arithmetic over natural numbers and integers. Simplify using `only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]`. Rewrite using `[if_neg (by omega)]`. Use linear arithmetic over natural numbers and integers. Use `hv i ⟨by omega, by omega⟩ hia r c ?_ ?_` and prove the remaining obligations.

Simplify using `only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]`. Rewrite using `[if_neg (by omega)]`. Use linear arithmetic over natural numbers and integers. Simplify using `only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]`. Rewrite using `[if_neg (by omega)]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem upper_of_steps : ∀ (N j : ℕ) (a b ca cb : Fin N) (C : Matrix (Fin N) (Fin N) ℂ), j ≤ N → (b : ℕ) = a + 1 →
    ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsBlockDiag j C →
    (∀ i, IsProperStep N j i → i ≠ a → ∀ r c, c ∈ stepCols N j i → r ∉ stepCols N j i → C r c = 0) →
    ∀ r c, c < r → ¬ (r = cb ∧ c = ca) → C r c = 0 := by
  intro N j a b ca cb C hj hb hcase hca hcb hbd hv r c hcr hne
  have hr := r.2
  have hc := c.2
  have ha := a.2
  have hb' := b.2
  have hcb' := cb.2
  have hlt : (c : ℕ) < r := hcr
  have hba : b ≠ a := by
    intro h
    rw [h] at hb
    omega
  unfold lastCol at hca
  by_cases hs : ((r : ℕ) < N - j ↔ (c : ℕ) < N - j)
  swap
  · exact hbd r c hs
  by_cases hW : N - j ≤ (c : ℕ)
  · obtain ⟨i, hi⟩ : ∃ i : Fin N, (i : ℕ) = c - (N - j) := ⟨⟨(c : ℕ) - (N - j), by omega⟩, rfl⟩
    by_cases hia : i = a
    · have hai : (a : ℕ) = c - (N - j) := by rw [← hia]; exact hi
      rw [if_pos (by omega)] at hca
      have hcc : c = ca := Fin.ext (by omega)
      have hrcb : (r : ℕ) ≠ cb := fun h => hne ⟨Fin.ext h, hcc⟩
      refine hv b ⟨by omega, by omega⟩ hba r c ?_ ?_
      · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [if_pos (by omega)]
        omega
      · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [if_pos (by omega)]
        omega
    · refine hv i ⟨by omega, by omega⟩ hia r c ?_ ?_
      · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [if_pos (by omega)]
        omega
      · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [if_pos (by omega)]
        omega
  · obtain ⟨i, hi⟩ : ∃ i : Fin N, (i : ℕ) = j + c := ⟨⟨j + (c : ℕ), by omega⟩, rfl⟩
    by_cases hia : i = a
    · have hai : (a : ℕ) = j + c := by rw [← hia]; exact hi
      rw [if_neg (by omega)] at hca
      have hcc : c = ca := Fin.ext (by omega)
      have hrcb : (r : ℕ) ≠ cb := fun h => hne ⟨Fin.ext h, hcc⟩
      refine hv b ⟨by omega, by omega⟩ hba r c ?_ ?_
      · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [if_neg (by omega)]
        omega
      · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [if_neg (by omega)]
        omega
    · refine hv i ⟨by omega, by omega⟩ hia r c ?_ ?_
      · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [if_neg (by omega)]
        omega
      · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [if_neg (by omega)]
        omega

end GlobalTheory.CompanionTheory.Ar.PB.StepShape
