import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsIrreducibleConnected
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IrreducibleConnected.StatementsBasicOpen
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Apply `hh` to reduce the goal to its premises. Establish `hv : h ∈ vanishingIdeal ℂ (zeroLocus ℂ W)`. Rewrite using `[mem_vanishingIdeal_iff]`.

Introduce `x hx`. Simplify `hcon x hx` using `[coe_aeval_eq_eval]`. Rewrite `hv` using `[vanishingIdeal_zeroLocus_eq_radical (K := ℂ), hW.isRadical.radical]`. Then use the resulting hypothesis.
-/
theorem IrreducibleConnected.exists_ne_zero {σ : Type} [Fintype σ] {W : Ideal (MvPolynomial σ ℂ)}
    (hW : W.IsPrime) {h : MvPolynomial σ ℂ} (hh : h ∉ W) :
    ∃ x ∈ zeroLocus ℂ W, eval x h ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hh
  have hv : h ∈ vanishingIdeal ℂ (zeroLocus ℂ W) := by
    rw [mem_vanishingIdeal_iff]
    intro x hx
    simpa [coe_aeval_eq_eval] using hcon x hx
  rwa [vanishingIdeal_zeroLocus_eq_radical (K := ℂ), hW.isRadical.radical] at hv

/- English proof (translation)
Introduce `σ _ W J hW`. Use `set D : MvPolynomial σ ℂ → Set (σ → ℂ) := fun g => zeroLocus ℂ W \ {x : σ → ℂ | eval x g = 0} with hD`. Establish `hU : zeroLocus ℂ W \ zeroLocus ℂ J = ⋃ g ∈ {g | g ∈ J ∧ g ∉ W}, D g`. Use extensionality with `x`. Simplify using `only [Set.mem_sdiff, Set.mem_iUnion, Set.mem_ofPred_eq, hD, mem_zeroLocus_iff, exists_prop]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hxW, hxJ⟩ push Not at hxJ`. Take `⟨g, hgJ, hg⟩` from `hxJ`. Conclude with `⟨g, ⟨hgJ, fun hgW => hg (hxW g hgW)⟩, hxW, hg⟩`. Introduce and unpack `⟨g, ⟨hgJ, -⟩, hxW, hg⟩`.

Conclude with `⟨hxW, fun h => hg (h g hgJ)⟩`. Rewrite using `[hU]`. Use `IsPreconnected.biUnion_of_reflTransGen (fun g hg => hB σ W g hW hg.2) ?_` and prove the remaining obligations. Introduce `g hg g' hg'`. Use `Relation.ReflTransGen.single ⟨?_, hg⟩` and prove the remaining obligations.

Establish `hgg' : g * g' ∉ W` using `fun hm => (hW.mem_or_mem hm).elim hg.2 hg'.2`. Take `⟨x, hxW, hx⟩` from `IrreducibleConnected.exists_ne_zero hW hgg'`. Rewrite `hx` using `[map_mul]`. Conclude with `⟨x, ⟨hxW, left_ne_zero_of_mul hx⟩, ⟨hxW, right_ne_zero_of_mul hx⟩⟩`.
-/
theorem IrreducibleConnected.proof (hB : IrreducibleBasicOpenConnected.Statement) :
    IrreducibleConnected.Statement := by
  intro σ _ W J hW
  set D : MvPolynomial σ ℂ → Set (σ → ℂ) := fun g => zeroLocus ℂ W \ {x : σ → ℂ | eval x g = 0} with hD
  have hU : zeroLocus ℂ W \ zeroLocus ℂ J = ⋃ g ∈ {g | g ∈ J ∧ g ∉ W}, D g := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_iUnion, Set.mem_ofPred_eq, hD, mem_zeroLocus_iff,
      exists_prop]
    constructor
    · rintro ⟨hxW, hxJ⟩
      push Not at hxJ
      obtain ⟨g, hgJ, hg⟩ := hxJ
      exact ⟨g, ⟨hgJ, fun hgW => hg (hxW g hgW)⟩, hxW, hg⟩
    · rintro ⟨g, ⟨hgJ, -⟩, hxW, hg⟩
      exact ⟨hxW, fun h => hg (h g hgJ)⟩
  rw [hU]
  refine IsPreconnected.biUnion_of_reflTransGen (fun g hg => hB σ W g hW hg.2) ?_
  intro g hg g' hg'
  refine Relation.ReflTransGen.single ⟨?_, hg⟩
  have hgg' : g * g' ∉ W := fun hm => (hW.mem_or_mem hm).elim hg.2 hg'.2
  obtain ⟨x, hxW, hx⟩ := IrreducibleConnected.exists_ne_zero hW hgg'
  rw [map_mul] at hx
  exact ⟨x, ⟨hxW, left_ne_zero_of_mul hx⟩, ⟨hxW, right_ne_zero_of_mul hx⟩⟩

end GroundTheory.Heights₂.Heights.HilbertSamuel
