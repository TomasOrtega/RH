import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development

open MeasureTheory PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.UnitFL

/- English proof (translation)
Introduce `hL2 hN4`. Unfold `PositivityTheory.Rg.Tf.Loc.Z2`. Introduce `k E _ _ _ _ _ _ _ _ _ _ _ _ hun σ hgen n _ _ _ _ μE μk _ _ _ _ γ μγ _ hnot _`. Establish `hno : ∀ g : GL (Fin n) k, g⁻¹ * γ * g ∉ unitGL (n` using `Fin n) k := by`. Introduce `g hg`.

Take `⟨c, -, -, hc⟩` from `hN4 k E hun σ hgen n γ (hL2.1 k n γ ⟨g, hg⟩)`. Conclude with `hnot ⟨c, 1, by simpa using hc⟩`. Establish `hzero : (fun g : GL (Fin n) k => unitFn (n` using `Fin n) k (g⁻¹ * γ * g)) = fun _ => 0 := by`. Use function extensionality and compare the values at `g`. Conclude with `Set.indicator_of_notMem (hno g) _`.

Unfold `orbIntegral quotLIntegral`. Rewrite using `[hzero]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem unit_fundamental_lemma_second : PositivityTheory.Rg.Tf.Loc.L2 → PositivityTheory.Rg.Tf.Loc.N4 → PositivityTheory.Rg.Tf.Loc.Z2 := by
  intro hL2 hN4
  unfold PositivityTheory.Rg.Tf.Loc.Z2
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ hun σ hgen n _ _ _ _ μE μk _ _ _ _ γ μγ _ hnot _
  have hno : ∀ g : GL (Fin n) k, g⁻¹ * γ * g ∉ unitGL (n := Fin n) k := by
    intro g hg
    obtain ⟨c, -, -, hc⟩ := hN4 k E hun σ hgen n γ (hL2.1 k n γ ⟨g, hg⟩)
    exact hnot ⟨c, 1, by simpa using hc⟩
  have hzero : (fun g : GL (Fin n) k => unitFn (n := Fin n) k (g⁻¹ * γ * g)) = fun _ => 0 := by
    funext g
    exact Set.indicator_of_notMem (hno g) _
  unfold orbIntegral quotLIntegral
  rw [hzero]
  split_ifs <;> simp

end GlobalTheory.CompanionTheory.UnitFL
