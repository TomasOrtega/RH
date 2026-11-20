import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.UpVApply
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl.SmallStep

/- English proof (translation)
Establish `h1` using `m.2`. Establish `h2` using `i.2`. Establish `h3` using `b.2`. Establish `h4` using `x.2`. Establish `h5 : (m : ℕ) ≤ i` using `hmi`.

Simplify using `only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at hb hb' hx ⊢`. Apply the tactic sequence `split_ifs at hb hb' hx ⊢ <;> omega`.
-/
theorem stepCols_subset_of_le {N j : ℕ} (hj : j ≤ N) {m i b x : Fin N} (hmi : m ≤ i)
    (hb : b ∈ stepCols N j m) (hb' : b ∈ stepCols N j i) (hx : x ∈ stepCols N j m) : x ∈ stepCols N j i := by
  have h1 := m.2
  have h2 := i.2
  have h3 := b.2
  have h4 := x.2
  have h5 : (m : ℕ) ≤ i := hmi
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at hb hb' hx ⊢
  split_ifs at hb hb' hx ⊢ <;> omega

/- English proof (translation)
Take `⟨⟨⟨τ, a, b⟩, hlt, hblk⟩, hsep⟩` from `q`. Take `⟨i, hk, hp, hb, ha⟩` from `id hsep`. Simplify using `only at hk hp hb ha hlt hblk ⊢`. Establish `hne : (pSteps j keep τ b).Nonempty` using `⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk, hp, hb⟩⟩`. Establish `hm : pStep j keep τ b ∈ pSteps j keep τ b`.

Unfold `pStep`. Rewrite using `[dif_pos hne]`. Conclude with `Finset.min'_mem _ _`. Establish `hmin : ∀ i' ∈ pSteps j keep τ b, pStep j keep τ b ≤ i'`. Introduce `i' hi'`.

Unfold `pStep`. Rewrite using `[dif_pos hne]`. Conclude with `Finset.min'_le _ _ hi'`. Take `⟨hmk, hmp, hmb⟩` from `(Finset.mem_filter.mp hm).2`. Use `⟨hmk, hmp, hmb, fun hx => ha (stepCols_subset_of_le hj (hmin i ?_) hmb hb hx), fun c => ⟨?_, ?_⟩⟩` and prove the remaining obligations.

Conclude with `Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk, hp, hb⟩`. Unfold `pMat lowMat`. Rewrite using `[dif_pos (⟨hlt, hblk⟩ : b < a ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j))]`. Unfold `cExt`. Rewrite using `[dif_pos hsep]`.

Introduce `x hx hxb`. Unfold `pMat lowMat`. Distinguish the cases in `hc : b < x ∧ ((x : ℕ) < N - j ↔ (b : ℕ) < N - j)`. Rewrite using `[dif_pos hc]`. Unfold `cExt`.

Use `dif_neg ?_` and prove the remaining obligations. Introduce and unpack `⟨i', hk', hp', hb', hx'⟩`. Conclude with `hx' (stepCols_subset_of_le hj (hmin i' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk', hp', hb'⟩)) hmb hb' hx)`. Rewrite using `[dif_neg hc, if_neg hxb]`.
-/
theorem pStep_reads (Ψ : Type) (N j : ℕ) (keep : Ψ × Fin N → Prop) (q : PIdx j keep) (hj : j ≤ N) :
    keep (q.1.1.1, pStep j keep q.1.1.1 q.1.1.2.2) ∧ IsProperStep N j (pStep j keep q.1.1.1 q.1.1.2.2) ∧
      q.1.1.2.2 ∈ stepCols N j (pStep j keep q.1.1.1 q.1.1.2.2) ∧
      q.1.1.2.1 ∉ stepCols N j (pStep j keep q.1.1.1 q.1.1.2.2) ∧
      ∀ c : PIdx j keep → ℂ, pMat keep c q.1.1.1 q.1.1.2.1 q.1.1.2.2 = c q ∧
        ∀ x ∈ stepCols N j (pStep j keep q.1.1.1 q.1.1.2.2), x ≠ q.1.1.2.2 →
          pMat keep c q.1.1.1 x q.1.1.2.2 = 0 := by
  obtain ⟨⟨⟨τ, a, b⟩, hlt, hblk⟩, hsep⟩ := q
  obtain ⟨i, hk, hp, hb, ha⟩ := id hsep
  dsimp only at hk hp hb ha hlt hblk ⊢
  have hne : (pSteps j keep τ b).Nonempty :=
    ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk, hp, hb⟩⟩
  have hm : pStep j keep τ b ∈ pSteps j keep τ b := by
    unfold pStep
    rw [dif_pos hne]
    exact Finset.min'_mem _ _
  have hmin : ∀ i' ∈ pSteps j keep τ b, pStep j keep τ b ≤ i' := by
    intro i' hi'
    unfold pStep
    rw [dif_pos hne]
    exact Finset.min'_le _ _ hi'
  obtain ⟨hmk, hmp, hmb⟩ := (Finset.mem_filter.mp hm).2
  refine ⟨hmk, hmp, hmb, fun hx => ha (stepCols_subset_of_le hj (hmin i ?_) hmb hb hx), fun c => ⟨?_, ?_⟩⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk, hp, hb⟩
  · unfold pMat lowMat
    rw [dif_pos (⟨hlt, hblk⟩ : b < a ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j))]
    unfold cExt
    rw [dif_pos hsep]
  · intro x hx hxb
    unfold pMat lowMat
    by_cases hc : b < x ∧ ((x : ℕ) < N - j ↔ (b : ℕ) < N - j)
    · rw [dif_pos hc]
      unfold cExt
      refine dif_neg ?_
      rintro ⟨i', hk', hp', hb', hx'⟩
      exact hx' (stepCols_subset_of_le hj
        (hmin i' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk', hp', hb'⟩)) hmb hb' hx)
    · rw [dif_neg hc, if_neg hxb]

end GlobalTheory.CompanionTheory.Ar.PB.PFl.SmallStep
