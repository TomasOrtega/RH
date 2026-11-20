import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Formalism.LocalRingCardinality.HeightBoundGeFourthPowerRank
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.ConcreteSettingExists
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
open Formalism.BasicNotions

namespace GlobalTheory.Core.Rk.GapOfNodes

/- English proof (translation)
Introduce `D H`. Establish `hN : D.R.N D.R.m = D.R.rankX' + 1` using `factXm D.R`. Use `⟨D.R.N D.R.m, hN.ge, fun τ i hi => ?_⟩` and prove the remaining obligations. Establish `h` using `H D.u₀ τ i.1 hi`. Rewrite `h` using `[D.hcW_b D.u₀ τ]`.

Simplify using `only [Fin.eta] at h`. Establish `ht : (0 : ℝ) ≤ (D.R.t : ℝ)` using `by positivity`. Establish `hc : (0 : ℝ) ≤ ((D.R.N D.R.m : ℕ) : ℝ) ^ 3` using `by positivity`. Establish `key : (((D.R.t : ℚ) + 2 * ((D.R.N D.R.m : ℕ) : ℚ) ^ 3 + 1 : ℚ) : ℝ) ≤ (((D.hc τ).b ⟨i.1 + 1, hi⟩ - (D.hc τ).b i : ℚ) : ℝ)`. Use `push_cast`.

Move the coercions through the operations in `at h`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `key` after adjusting the coercions.
-/
theorem harishChandraNodesFarApart_of_cubic_node_gap : ∀ D : D7, D.NodeGap (4 * ((D.R.N D.R.m : ℕ) : ℝ) ^ 3 + 2 * D.R.t + 6) →
    GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D := by
  intro D H
  have hN : D.R.N D.R.m = D.R.rankX' + 1 := factXm D.R
  refine ⟨D.R.N D.R.m, hN.ge, fun τ i hi => ?_⟩
  have h := H D.u₀ τ i.1 hi
  rw [D.hcW_b D.u₀ τ] at h
  simp only [Fin.eta] at h
  have ht : (0 : ℝ) ≤ (D.R.t : ℝ) := by positivity
  have hc : (0 : ℝ) ≤ ((D.R.N D.R.m : ℕ) : ℝ) ^ 3 := by positivity
  have key : (((D.R.t : ℚ) + 2 * ((D.R.N D.R.m : ℕ) : ℚ) ^ 3 + 1 : ℚ) : ℝ) ≤
      (((D.hc τ).b ⟨i.1 + 1, hi⟩ - (D.hc τ).b i : ℚ) : ℝ) := by
    push_cast
    push_cast at h
    linarith
  exact_mod_cast key

end GlobalTheory.Core.Rk.GapOfNodes
