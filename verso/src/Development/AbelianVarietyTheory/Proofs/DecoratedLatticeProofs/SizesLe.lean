import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.ConcreteSettingExists
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotInhAbsOfGamLe
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Formalism.LocalRingCardinality.HeightBoundGeFourthPowerRank
open Formalism.BasicNotions Formalism.MainNotions.S GlobalTheory.Core.Rk

namespace GlobalTheory.Core.Rk.HdGap

/- English proof (translation)
Unfold `bOne`. Rewrite using `[dif_pos (by omega)]`. Both sides reduce to the same expression.
-/
theorem bOne_eq (D : D7) (τ : D.what₂.Tau) (j : ℕ) (hj : j < D.R.m) :
    bOne D τ (j + 1) = (((D.hc τ).b ⟨j, hj⟩ : ℚ) : ℝ) := by
  unfold bOne
  rw [dif_pos (by omega)]
  rfl

/- English proof (translation)
Take `⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hg, -⟩` from `H`. Establish `h` using `hg τ (j + 1) (by omega) (by omega)`. Rewrite `h` using `[bOne_eq D τ (j + 1) hj, bOne_eq D τ j (by omega)]`. Then use the resulting hypothesis.
-/
theorem gap_of {D : D7} {L C' Cl Cg cb Cu cT CT : ℝ} (H : GlobalTheory.Core.Deg.HypL D L C' Cl Cg cb Cu cT CT)
    (τ : D.what₂.Tau) (j : ℕ) (hj : j + 1 < D.R.m) :
    Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L ≤
      (((D.hc τ).b ⟨j + 1, hj⟩ : ℚ) : ℝ) - (((D.hc τ).b ⟨j, by omega⟩ : ℚ) : ℝ) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hg, -⟩ := H
  have h := hg τ (j + 1) (by omega) (by omega)
  rwa [bOne_eq D τ (j + 1) hj, bOne_eq D τ j (by omega)] at h

/- English proof (translation)
Take `⟨hL, -, hmf, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hClm, -⟩` from `H`. Establish `hm : 1801 ≤ D.R.m` using `by exact_mod_cast hCl.trans hClm`. Establish `hk` using `D.R.m_add_three_le_k`. Use `⟨?_, by unfold Ranks.r; omega⟩` and prove the remaining obligations. Establish `hf1 : (1 : ℝ) ≤ (D.R.f : ℝ)`.

Establish `: 1 ≤ D.R.f` using `le_trans (Nat.one_le_pow _ _ (by omega)) hmf`. Conclude with `this` after adjusting the coercions. Establish `hf5 : (1 : ℝ) ≤ (D.R.f : ℝ) ^ 5` using `one_le_pow₀ hf1`. Establish `hr : (0 : ℝ) ≤ (D.R.r : ℝ) ^ 19` using `by positivity`. Establish `h1 : 1 ≤ (D.R.f : ℝ) ^ 5 * L` using `by nlinarith`.

Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul_of_nonneg_left h1` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities. Use `_ = _ := by ring`.
-/
theorem scale_of {D : D7} {L C' Cl Cg cb Cu cT CT : ℝ} (hCl : 1801 ≤ Cl)
    (H : GlobalTheory.Core.Deg.HypL D L C' Cl Cg cb Cu cT CT) :
    1801 * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L ∧ 1801 ≤ D.R.r := by
  obtain ⟨hL, -, hmf, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hClm, -⟩ := H
  have hm : 1801 ≤ D.R.m := by exact_mod_cast hCl.trans hClm
  have hk := D.R.m_add_three_le_k
  refine ⟨?_, by unfold Ranks.r; omega⟩
  have hf1 : (1 : ℝ) ≤ (D.R.f : ℝ) := by
    have : 1 ≤ D.R.f := le_trans (Nat.one_le_pow _ _ (by omega)) hmf
    exact_mod_cast this
  have hf5 : (1 : ℝ) ≤ (D.R.f : ℝ) ^ 5 := one_le_pow₀ hf1
  have hr : (0 : ℝ) ≤ (D.R.r : ℝ) ^ 19 := by positivity
  have h1 : 1 ≤ (D.R.f : ℝ) ^ 5 * L := by nlinarith
  calc 1801 * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 := by nlinarith
    _ = Cl * (D.R.r : ℝ) ^ 19 * 1 := by ring
    _ ≤ Cl * (D.R.r : ℝ) ^ 19 * ((D.R.f : ℝ) ^ 5 * L) := by
        apply mul_le_mul_of_nonneg_left h1; nlinarith
    _ = _ := by ring

end GlobalTheory.Core.Rk.HdGap
