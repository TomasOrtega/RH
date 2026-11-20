import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuBesselLoc
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QuotInv
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QuotSetU

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace Formalism.L2.SG.Pf.WuBL

/- English proof (translation)
Introduce `k r z hz hT μG μS ν hG hS hq Vp _ W hWc hW0 hWS y hy`. Take `⟨hGg, hSg, hSG, hRG, hRS⟩` from `quotient_measure_unitary_group k r z hz hT`. Establish `hset : PI.QuotientSetting (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (Formalism.QuantumDeterminants.Sset k r z) μG μS ν` using `⟨hGg, hSg, hSG, hG, hS, hRG μG hG, hRS μS hS, hq⟩`. Set `G : Set (Formalism.QuantumDeterminants.Mt k r)` to `{x | Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)}`. Establish `hGc : IsClosed G` using `hGg.1.preimage continuous_id`.

Set `F : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞` to `fun x => ((‖W (Matrix.of x)‖₊ : ℝ≥0∞)) ^ 2`. Establish `hFG : F = G.piecewise F (fun _ => 0)`. Use function extensionality and compare the values at `x`. Distinguish the cases in `hx : x ∈ G`. Simplify using `[Set.piecewise, hx]`.

Simplify using `[Set.piecewise, hx, F, hW0 (Matrix.of x) hx]`. Establish `hcont : ContinuousOn F G`. Establish `hW' : ContinuousOn (fun x : Formalism.QuantumDeterminants.Mt k r => W (Matrix.of x)) G` using `hWc.comp continuous_id.continuousOn (fun x hx => hx)`. Conclude with `(ENNReal.continuous_pow 2).comp_continuousOn (ENNReal.continuous_coe.comp_continuousOn hW'.nnnorm)`. Establish `hmeas : Measurable F`.

Rewrite using `[hFG]`. Conclude with `hcont.measurable_piecewise continuousOn_const hGc.measurableSet`. Establish `hinv : ∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, ∀ x : Formalism.QuantumDeterminants.Mt k r, Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) → F (fun i j => (s * Matrix.of x) i j) = F x`. Introduce `s hs x hx`. Establish `h2 : ‖W (s * Matrix.of x)‖₊ = ‖W (Matrix.of x)‖₊` using `NNReal.eq (hWS s hs (Matrix.of x) hx)`.

Express the relevant statement in the definitionally equal form `((‖W (s * Matrix.of x)‖₊ : ℝ≥0∞)) ^ 2 = _`. Rewrite using `[h2]`. Conclude with `quotient_invariant (2 * r + k + 1) _ _ μG μS ν hset F hmeas hinv y hy`.
-/
theorem l2RightTranslation_thm : L2RightTranslation := by
  classical
  intro k r z hz hT μG μS ν hG hS hq Vp _ W hWc hW0 hWS y hy
  obtain ⟨hGg, hSg, hSG, hRG, hRS⟩ := quotient_measure_unitary_group k r z hz hT
  have hset : PI.QuotientSetting (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (Formalism.QuantumDeterminants.Sset k r z) μG μS ν :=
    ⟨hGg, hSg, hSG, hG, hS, hRG μG hG, hRS μS hS, hq⟩
  let G : Set (Formalism.QuantumDeterminants.Mt k r) := {x | Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)}
  have hGc : IsClosed G := hGg.1.preimage continuous_id
  let F : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞ := fun x => ((‖W (Matrix.of x)‖₊ : ℝ≥0∞)) ^ 2
  have hFG : F = G.piecewise F (fun _ => 0) := by
    funext x
    by_cases hx : x ∈ G
    · simp [Set.piecewise, hx]
    · simp [Set.piecewise, hx, F, hW0 (Matrix.of x) hx]
  have hcont : ContinuousOn F G := by
    have hW' : ContinuousOn (fun x : Formalism.QuantumDeterminants.Mt k r => W (Matrix.of x)) G :=
      hWc.comp continuous_id.continuousOn (fun x hx => hx)
    exact (ENNReal.continuous_pow 2).comp_continuousOn (ENNReal.continuous_coe.comp_continuousOn hW'.nnnorm)
  have hmeas : Measurable F := by
    rw [hFG]
    exact hcont.measurable_piecewise continuousOn_const hGc.measurableSet
  have hinv : ∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, ∀ x : Formalism.QuantumDeterminants.Mt k r,
      Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) →
      F (fun i j => (s * Matrix.of x) i j) = F x := by
    intro s hs x hx
    have h2 : ‖W (s * Matrix.of x)‖₊ = ‖W (Matrix.of x)‖₊ := NNReal.eq (hWS s hs (Matrix.of x) hx)
    change ((‖W (s * Matrix.of x)‖₊ : ℝ≥0∞)) ^ 2 = _
    rw [h2]
  exact quotient_invariant (2 * r + k + 1) _ _ μG μS ν hset F hmeas hinv y hy

end Formalism.L2.SG.Pf.WuBL
