import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPosPartIndependent
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPosPartSplit
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.LogIntegrableOnOfLogIntegrable
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets

noncomputable section

/- English proof (translation)
Introduce `n d J A f φ E y hA hE hcov`. Establish `hfin` using `IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y`. Unfold `chartPosDens sheetSum`. Simplify using `only [finsum_mem_eq_finite_toFinset_sum _ hfin]`. Use `set T : ((Fin n → ℂ) → ℝ) → (Fin n → ℂ) → ℝ := fun g x => if h : ∃ s, IsSheetAt J A x s then max (g x * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ h.choose) y) 0 else 0 with hT`.

Establish `hT0 : ∀ g x, 0 ≤ T g x` using `fun g x => by`. Apply the tactic sequence `simp only [hT]; split_ifs <;> simp`. Establish `hpt : ∀ x ∈ hfin.toFinset, ENNReal.ofReal (T f x) = ∑' k, ENNReal.ofReal (T ((E k).indicator f) x)`. Introduce `x hx`. Establish `hx' : x ∈ fibre J A y` using `hfin.mem_toFinset.mp hx`.

Distinguish the cases in `hs : ∃ s, IsSheetAt J A x s`. Take `⟨k₀, hk₀⟩` from `hcov x hx' hs`. Rewrite using `[tsum_eq_single k₀]`. Simplify using `only [hT, dif_pos hs, Set.indicator_of_mem hk₀]`. Introduce `k hk`.

Establish `hxk : x ∉ E k` using `fun hxk => Set.disjoint_left.mp (hE hk) hxk hk₀`. Simplify using `[hT, dif_pos hs, Set.indicator_of_notMem hxk]`. Simplify using `[hT, dif_neg hs]`. Rewrite using `[ENNReal.ofReal_sum_of_nonneg (fun x _ => hT0 f x), Finset.sum_congr rfl hpt, ← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]`. Conclude with `tsum_congr fun k => (ENNReal.ofReal_sum_of_nonneg (fun x _ => hT0 _ x)).symm`.
-/
theorem PosPartSplit.proof : PosPartSplit.Statement := by
  classical
  intro n d J A f φ E y hA hE hcov
  have hfin := IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y
  unfold chartPosDens sheetSum
  simp only [finsum_mem_eq_finite_toFinset_sum _ hfin]

  set T : ((Fin n → ℂ) → ℝ) → (Fin n → ℂ) → ℝ := fun g x =>
    if h : ∃ s, IsSheetAt J A x s then
      max (g x * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ h.choose) y) 0 else 0 with hT
  have hT0 : ∀ g x, 0 ≤ T g x := fun g x => by
    simp only [hT]; split_ifs <;> simp
  have hpt : ∀ x ∈ hfin.toFinset,
      ENNReal.ofReal (T f x) = ∑' k, ENNReal.ofReal (T ((E k).indicator f) x) := by
    intro x hx
    have hx' : x ∈ fibre J A y := hfin.mem_toFinset.mp hx
    by_cases hs : ∃ s, IsSheetAt J A x s
    · obtain ⟨k₀, hk₀⟩ := hcov x hx' hs
      rw [tsum_eq_single k₀]
      · simp only [hT, dif_pos hs, Set.indicator_of_mem hk₀]
      · intro k hk
        have hxk : x ∉ E k := fun hxk => Set.disjoint_left.mp (hE hk) hxk hk₀
        simp [hT, dif_pos hs, Set.indicator_of_notMem hxk]
    · simp [hT, dif_neg hs]
  rw [ENNReal.ofReal_sum_of_nonneg (fun x _ => hT0 f x), Finset.sum_congr rfl hpt,
    ← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  exact tsum_congr fun k => (ENNReal.ofReal_sum_of_nonneg (fun x _ => hT0 _ x)).symm

end

end GroundTheory.Heights₂.Heights
