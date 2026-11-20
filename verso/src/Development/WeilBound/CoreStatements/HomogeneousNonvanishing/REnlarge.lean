import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSncModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace PositivityTheory.UnitarySelfGeneration

/- English proof (translation)
Introduce `e X _ _ _ A Θ L L' s s' th ph phT C₅ C t₀ hC5 hC ht0 hL hsub hrw hS hR hC2`. Establish `hnb : ∀ y, y ∉ bdry s' → y ∉ bdry s` using `fun y hy h => hy (hsub h)`. Establish `hpos : ∀ y, 0 < rW L s y`. Introduce `y`. Unfold `rW`.

Establish `h1` using `hL y`. Establish `h2` using `Real.exp_pos 1`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨hpot, hsm, hpsh, hb⟩` from `hS`. Take `⟨h0, h1, hf⟩` from `hR`.

Use `⟨⟨hpot, ?_, ?_, ?_⟩, ⟨h0, h1, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `j`. Conclude with `(hsm j).mono (fun z hz => ⟨hz.1, hnb _ hz.2⟩)`. Introduce `x j y hy w`. Conclude with `hpsh x j y ⟨hy.1, hy.2.1, hnb _ hy.2.2⟩ w`.

Introduce `y hy`. Take `⟨hlo, hhi⟩` from `hb y (hnb y hy)`. Use `⟨?_, hhi⟩` and prove the remaining obligations. Establish `hlog : Real.log (rW L s y) ≤ Real.log (rW L' s' y)` using `Real.log_le_log (hpos y) (hrw y hy)`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hlog hC5]`.

Introduce `t ht htt`. Take `⟨a1, a2, a3, a4, a5, a6, a7, a8⟩` from `hf t ht htt`. Establish `hte : t ≤ Real.exp (-1)` using `le_trans htt ht0`. Establish `h1t : Real.exp 1 ≤ 1 / t`. Rewrite using `[le_div_iff₀ ht]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hL1 : 1 ≤ Real.log (1 / t)`. Establish `h` using `Real.log_le_log (Real.exp_pos 1) h1t`. Rewrite `h` using `[Real.log_exp]`. Then use the resulting hypothesis. Establish `heps : 0 ≤ epsT C t`.

Unfold `epsT`. Conclude with `div_nonneg (mul_nonneg hC (Real.log_nonneg hL1)) (by linarith)`. Use `⟨a1, a2, fun y hy => a3 y (hnb y hy), a4, a5, ?_, ?_, a8⟩` and prove the remaining obligations. Introduce `y hy hle`. Conclude with `a6 y (hnb y hy) (le_trans (hrw y hy) hle)`.

Introduce `y hy`. Establish `h7` using `a7 y (hnb y hy)`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left (hrw y hy) heps]`. Introduce `j K hK hKc`. Conclude with `hC2 j K (fun z hz => ⟨(hK hz).1, hnb _ (hK hz).2⟩) hKc`.
-/
theorem r_enlarge : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (Θ L L' : LocPot X) (s s' : X → X → ℂ) (th : LocPot X) (ph : X → ℝ) (phT : ℝ → X → ℝ) (C₅ C t₀ : ℝ), 0 ≤ C₅ → 0 ≤ C → t₀ ≤ Real.exp (-1) → (∀ y, logNormSec L s y ≤ 0) → bdry s ⊆ bdry s' → (∀ y, y ∉ bdry s' → rW L s y ≤ rW L' s' y) → IsSingWeight A L s th ph C₅ → IsRegFamily A Θ L s th ph phT C t₀ → IsRegFamilyC2 A s ph phT → IsSingWeight A L' s' th ph C₅ ∧ IsRegFamily A Θ L' s' th ph phT C t₀ ∧ IsRegFamilyC2 A s' ph phT := by
  intro e X _ _ _ A Θ L L' s s' th ph phT C₅ C t₀ hC5 hC ht0 hL hsub hrw hS hR hC2
  have hnb : ∀ y, y ∉ bdry s' → y ∉ bdry s := fun y hy h => hy (hsub h)
  have hpos : ∀ y, 0 < rW L s y := by
    intro y
    unfold rW
    have h1 := hL y
    have h2 := Real.exp_pos 1
    linarith
  obtain ⟨hpot, hsm, hpsh, hb⟩ := hS
  obtain ⟨h0, h1, hf⟩ := hR
  refine ⟨⟨hpot, ?_, ?_, ?_⟩, ⟨h0, h1, ?_⟩, ?_⟩
  · intro j
    exact (hsm j).mono (fun z hz => ⟨hz.1, hnb _ hz.2⟩)
  · intro x j y hy w
    exact hpsh x j y ⟨hy.1, hy.2.1, hnb _ hy.2.2⟩ w
  · intro y hy
    obtain ⟨hlo, hhi⟩ := hb y (hnb y hy)
    refine ⟨?_, hhi⟩
    have hlog : Real.log (rW L s y) ≤ Real.log (rW L' s' y) := Real.log_le_log (hpos y) (hrw y hy)
    nlinarith [mul_le_mul_of_nonneg_left hlog hC5]
  · intro t ht htt
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hf t ht htt
    have hte : t ≤ Real.exp (-1) := le_trans htt ht0
    have h1t : Real.exp 1 ≤ 1 / t := by
      rw [le_div_iff₀ ht]
      calc Real.exp 1 * t ≤ Real.exp 1 * Real.exp (-1) := by gcongr
        _ = 1 := by rw [← Real.exp_add]; simp
    have hL1 : 1 ≤ Real.log (1 / t) := by
      have h := Real.log_le_log (Real.exp_pos 1) h1t
      rwa [Real.log_exp] at h
    have heps : 0 ≤ epsT C t := by
      unfold epsT
      exact div_nonneg (mul_nonneg hC (Real.log_nonneg hL1)) (by linarith)
    refine ⟨a1, a2, fun y hy => a3 y (hnb y hy), a4, a5, ?_, ?_, a8⟩
    · intro y hy hle
      exact a6 y (hnb y hy) (le_trans (hrw y hy) hle)
    · intro y hy
      have h7 := a7 y (hnb y hy)
      nlinarith [mul_le_mul_of_nonneg_left (hrw y hy) heps]
  · intro j K hK hKc
    exact hC2 j K (fun z hz => ⟨(hK hz).1, hnb _ (hK hz).2⟩) hKc

end PositivityTheory.UnitarySelfGeneration
