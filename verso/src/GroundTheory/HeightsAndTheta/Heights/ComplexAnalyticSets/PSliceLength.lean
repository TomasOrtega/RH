import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceLength
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceReducedGeneral
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceMultGeneral
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVanishNearPoint
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

/- English proof (translation)
Introduce `n d J W u hJ hdim hu hW`. Establish `hWp : W.IsPrime` using `hW.1.1`. Take `⟨f₁, hf₁W, hf₁⟩` from `hR n d J W u hJ hdim hu hW`. Take `⟨f₂, hf₂W, hf₂⟩` from `hM n d J W u hJ hdim hu hW`. Establish `hf : f₁ * f₂ ∉ W` using `fun h => (hWp.mem_or_mem h).elim hf₁W hf₂W`.

Establish `hUo : IsOpen {x : Fin n → ℂ | eval x (f₁ * f₂) ≠ 0}` using `isOpen_ne_fun (MvPolynomial.continuous_eval (p := f₁ * f₂)) continuous_const`. Use `⟨{x | eval x (f₁ * f₂) ≠ 0}, hUo, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Rewrite using `[mem_closure_iff_nhds]`. Introduce `t ht`.

Assume the negation of the conclusion as `hempty`. Rewrite `hempty` using `[Set.not_nonempty_iff_eq_empty]`. Apply `hf` to reduce the goal to its premises. Use `hV n W (f₁ * f₂) x hWp hx ?_` and prove the remaining obligations. Use `filter_upwards [ht] with y hyt hyW`.

Assume the negation of the conclusion as `hne`. Establish `hy : y ∈ t ∩ (zeroSet W ∩ {x | eval x (f₁ * f₂) ≠ 0})` using `⟨hyt, hyW, hne⟩`. Rewrite `hy` using `[hempty]`. Conclude with `hy`. Introduce and unpack `q ⟨hqW, hqf⟩`.

Rewrite `hqf` using `[Set.mem_ofPred_eq, map_mul, mul_ne_zero_iff]`. Take `⟨O₁, hO₁o, hO₁d, hO₁⟩` from `hf₁ q hqW hqf.1`. Take `⟨O₂, -, hO₂d, hO₂⟩` from `hf₂ q hqW hqf.2`. Conclude with `(hO₁d.inter_of_isOpen_left hO₂d hO₁o).mono fun L hL => ⟨hO₁ L hL.1, hO₂ L hL.2⟩`.
-/
theorem SliceLength.proof (hV : IndefiniteRowSideFullHecke.ComplexSets.VanishNearPoint.Statement)
    (hR : SliceReducedGeneral.Statement) (hM : SliceMultGeneral.Statement) :
    SliceLength.Statement := by
  intro n d J W u hJ hdim hu hW
  have hWp : W.IsPrime := hW.1.1
  obtain ⟨f₁, hf₁W, hf₁⟩ := hR n d J W u hJ hdim hu hW
  obtain ⟨f₂, hf₂W, hf₂⟩ := hM n d J W u hJ hdim hu hW
  have hf : f₁ * f₂ ∉ W := fun h => (hWp.mem_or_mem h).elim hf₁W hf₂W
  have hUo : IsOpen {x : Fin n → ℂ | eval x (f₁ * f₂) ≠ 0} :=
    isOpen_ne_fun (MvPolynomial.continuous_eval (p := f₁ * f₂)) continuous_const
  refine ⟨{x | eval x (f₁ * f₂) ≠ 0}, hUo, ?_, ?_⟩
  ·
    intro x hx
    rw [mem_closure_iff_nhds]
    intro t ht
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    apply hf
    refine hV n W (f₁ * f₂) x hWp hx ?_
    filter_upwards [ht] with y hyt hyW
    by_contra hne
    have hy : y ∈ t ∩ (zeroSet W ∩ {x | eval x (f₁ * f₂) ≠ 0}) := ⟨hyt, hyW, hne⟩
    rw [hempty] at hy
    exact hy
  ·
    rintro q ⟨hqW, hqf⟩
    rw [Set.mem_ofPred_eq, map_mul, mul_ne_zero_iff] at hqf
    obtain ⟨O₁, hO₁o, hO₁d, hO₁⟩ := hf₁ q hqW hqf.1
    obtain ⟨O₂, -, hO₂d, hO₂⟩ := hf₂ q hqW hqf.2
    exact (hO₁d.inter_of_isOpen_left hO₂d hO₁o).mono fun L hL => ⟨hO₁ L hL.1, hO₂ L hL.2⟩

end GroundTheory.Heights₂.Heights
