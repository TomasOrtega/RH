import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordBoxStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RoundedSizesSumLeParametersPageHeightStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordThickOrStatement

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

/- English proof (translation)
Take `⟨-, -, hw, -, -, -⟩` from `hB`. Establish `hs : W.sz i ≤ (W.b : ℤ) + W.η`. Break down `hT i with h | h` into its components or cases. Conclude with `h.2`. Use linear arithmetic over natural numbers and integers.

Unfold `WordData.Mi WordData.hi`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem WordData.Mi_add_hi_le_two_mul {n : ℕ} (W : WordData n) (hB : W.Box) (hT : W.ThickOr) (i : ZMod n) :
    W.Mi i + W.hi i ≤ 2 * (W.b + W.η + W.S) := by
  obtain ⟨-, -, hw, -, -, -⟩ := hB
  have hs : W.sz i ≤ (W.b : ℤ) + W.η := by
    rcases hT i with h | h
    · exact h.2
    · omega
  unfold WordData.Mi WordData.hi
  split_ifs <;> omega

/- English proof (translation)
Establish `h1` using `WordData.Mi_add_hi_le_two_mul _ (GlobalTheory.T.twistedDualOrbitPageWord_box L C j ε τ φ hR) (GlobalTheory.T.twistedDualOrbitPageWord_thickOr L C j ε τ φ hR) i`. Establish `h2` using `GlobalTheory.T.sum_roundedSizes_le_height L C hR`. Establish `h3 : (((pageWord L j ε τ φ).Mi i + (pageWord L j ε τ φ).hi i : ℕ) : ℝ) ≤ ((2 * (bHat L + etaHat L + sHat L) : ℕ) : ℝ)` using `Nat.cast_le.mpr h1`. Use `h3.trans ?_` and prove the remaining obligations. Use `push_cast`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem pageWord_Mi_add_hi_le {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG)
    (hR : Roomy L C) (i : ZMod (orderOf φ)) :
    (((pageWord L j ε τ φ).Mi i + (pageWord L j ε τ φ).hi i : ℕ) : ℝ) ≤ 2 * hPage L := by
  have h1 := WordData.Mi_add_hi_le_two_mul _ (GlobalTheory.T.twistedDualOrbitPageWord_box L C j ε τ φ hR) (GlobalTheory.T.twistedDualOrbitPageWord_thickOr L C j ε τ φ hR) i
  have h2 := GlobalTheory.T.sum_roundedSizes_le_height L C hR
  have h3 : (((pageWord L j ε τ φ).Mi i + (pageWord L j ε τ φ).hi i : ℕ) : ℝ)
      ≤ ((2 * (bHat L + etaHat L + sHat L) : ℕ) : ℝ) := Nat.cast_le.mpr h1
  refine h3.trans ?_
  push_cast
  linarith

end GlobalTheory.HTW
