import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParametersRoundedSizeBoundWindowStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MaxNonThickSizeShiftedValueAndBoundsStatement

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

/- English proof (translation)
Establish `hlow` using `(GlobalTheory.T.roundedSizeBound_window L C' hR).1`. Take `⟨-, hw2, hG⟩` from `GlobalTheory.T.maxNonThickSizeShifted_value_and_bounds L C' hR`. Take `⟨h100, -, -, -, -, hbig⟩` from `hR`. Establish `hw0 : (0 : ℝ) ≤ (wHat D : ℝ)` using `Nat.cast_nonneg _`. Establish `heta` using `L.etaSz_pos`.

Establish `ht : (0 : ℝ) ≤ (D.R.t : ℝ)` using `Nat.cast_nonneg _`. Establish `hhalf : ((D.R.t : ℝ) + 1) / 2 ≤ L.sc.b'` using `by linarith`. Establish `hb0 : 0 ≤ L.sc.b'` using `by linarith`. Establish `hjN : (j + 1) * 2 ≤ D.host.Lw` using `by omega`. Establish `hjL : ((j : ℝ) + 1) * 2 ≤ (D.host.Lw : ℝ)` using `by exact_mod_cast hjN`.

Establish `hj0 : (0 : ℝ) ≤ (j : ℝ) + 1` using `by positivity`. Use `push_cast`. Establish `s1 : C * ((j : ℝ) + 1) * ((wHat D : ℝ) + sHat L + etaHat L + 1) ≤ C * ((j : ℝ) + 1) * (2 * L.sc.b')` using `mul_le_mul_of_nonneg_left hG (mul_nonneg hC hj0)`. Establish `s2 : C * ((j : ℝ) + 1) * (2 * L.sc.b') ≤ C' * ((j : ℝ) + 1) * L.sc.b'`. Use `mul_le_mul_of_nonneg_right hCC (mul_nonneg hj0 hb0)` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Establish `s3 : C' * ((j : ℝ) + 1) * L.sc.b' + L.sc.b' ≤ C' * ((D.host.Lw : ℝ) + 1) * L.sc.b'`. Establish `hk : C' * ((j : ℝ) + 1) + 1 ≤ C' * ((D.host.Lw : ℝ) + 1)` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem mul_small_le_bHat {D : D7} (L : SizeData₂ D) (C C' : ℝ) (j : ℕ) (hR : Roomy L C') (hC : 0 ≤ C)
    (hCC : 2 * C ≤ C') (hj : 2 * j + 2 ≤ D.host.Lw) :
    C * ((j : ℝ) + 1) * (((wHat D + sHat L + etaHat L : ℕ) : ℝ) + 1) ≤ (bHat L : ℝ) := by
  have hlow := (GlobalTheory.T.roundedSizeBound_window L C' hR).1
  obtain ⟨-, hw2, hG⟩ := GlobalTheory.T.maxNonThickSizeShifted_value_and_bounds L C' hR
  obtain ⟨h100, -, -, -, -, hbig⟩ := hR
  have hw0 : (0 : ℝ) ≤ (wHat D : ℝ) := Nat.cast_nonneg _
  have heta := L.etaSz_pos
  have ht : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
  have hhalf : ((D.R.t : ℝ) + 1) / 2 ≤ L.sc.b' := by linarith
  have hb0 : 0 ≤ L.sc.b' := by linarith
  have hjN : (j + 1) * 2 ≤ D.host.Lw := by omega
  have hjL : ((j : ℝ) + 1) * 2 ≤ (D.host.Lw : ℝ) := by exact_mod_cast hjN
  have hj0 : (0 : ℝ) ≤ (j : ℝ) + 1 := by positivity
  push_cast
  have s1 : C * ((j : ℝ) + 1) * ((wHat D : ℝ) + sHat L + etaHat L + 1)
      ≤ C * ((j : ℝ) + 1) * (2 * L.sc.b') :=
    mul_le_mul_of_nonneg_left hG (mul_nonneg hC hj0)
  have s2 : C * ((j : ℝ) + 1) * (2 * L.sc.b') ≤ C' * ((j : ℝ) + 1) * L.sc.b' := by
    have := mul_le_mul_of_nonneg_right hCC (mul_nonneg hj0 hb0)
    nlinarith
  have s3 : C' * ((j : ℝ) + 1) * L.sc.b' + L.sc.b' ≤ C' * ((D.host.Lw : ℝ) + 1) * L.sc.b' := by
    have hk : C' * ((j : ℝ) + 1) + 1 ≤ C' * ((D.host.Lw : ℝ) + 1) := by nlinarith
    nlinarith
  linarith

end GlobalTheory.HTW
