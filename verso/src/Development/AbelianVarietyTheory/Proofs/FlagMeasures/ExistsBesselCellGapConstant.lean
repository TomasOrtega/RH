import Formalism.SharpRestriction.CuspSpanNormBounds.IsPtRepTrDat
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
import Formalism.SharpRestriction.CuspSpanNormBounds.SBridge
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPlacesEqTrace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.JEqOrbInt
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

namespace GlobalTheory.GapConstant

set_option maxHeartbeats 2000000 in
/- English proof (translation)
Establish `hk' : (1 : ℝ) ≤ k` using `by exact_mod_cast hk`. Establish `hr0 : (0 : ℝ) ≤ r` using `Nat.cast_nonneg r`. Establish `hs : ((2 * r + 2 : ℕ) : ℝ) = 2 * ((r : ℝ) + 1)` using `by push_cast; ring`. Establish `h3 : ((3 * (r + 1) : ℕ) : ℝ) = 3 * ((r : ℝ) + 1)` using `by push_cast; ring`. Establish `hNdef : ((2 * r + k + 1 : ℕ) : ℝ) = 2 * (r : ℝ) + k + 1` using `by push_cast; ring`.

Rewrite using `[hs, h3]`. Use `set P : ℝ := (r : ℝ) + 1 with hPdef`. Use `set N : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hNd`. Establish `hP1 : 1 ≤ P` using `by linarith`. Establish `hN2 : 2 * P ≤ N` using `by rw [hNdef]; linarith`.

Establish `hN1 : 1 ≤ N` using `by linarith`. Establish `h2P : 0 < 2 * P` using `by linarith`. Establish `hsq : 0 < Real.sqrt (2 * P)` using `Real.sqrt_pos.mpr h2P`. Establish `hsq1 : 1 ≤ Real.sqrt (2 * P)` using `Real.one_le_sqrt.mpr (by linarith)`. Establish `hrp : (2 * P) ^ ((9 : ℝ) / 2) = (2 * P) ^ 4 * Real.sqrt (2 * P)`.

Rewrite using `[Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add h2P]`. Evaluate the numerical expressions. Rewrite using `[hrp]`. Use `set X : ℝ := 3 * P * N ^ 2 + N ^ 3 with hX`. Establish `ha : Formalism.FourierDecayAlt.ThreeDimData.aOf r (1000 * ((2 * P) ^ 4 * Real.sqrt (2 * P)) * X) = 2000 * P ^ 4 * X`.

Unfold `Formalism.FourierDecayAlt.ThreeDimData.aOf`. Rewrite using `[← hPdef]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hAS : Formalism.FourierDecayAlt.ThreeDimData.AS k r ≤ 2 * P * N ^ 2`.

Unfold `Formalism.FourierDecayAlt.ThreeDimData.AS Formalism.FourierDecayAlt.ThreeDimData.dN`. Establish `e : ((2 * r + k : ℕ) : ℝ) = 2 * (r : ℝ) + k` using `by push_cast; ring`. Rewrite using `[e]`. Establish `hd0 : 0 ≤ (r : ℝ) * ((r : ℝ) - 1) + 2 * (r : ℝ) * ((k : ℝ) + 1) + (r : ℝ) ^ 2` using `by nlinarith`. Establish `hd : (r : ℝ) * ((r : ℝ) - 1) + 2 * (r : ℝ) * ((k : ℝ) + 1) + (r : ℝ) ^ 2 ≤ 2 * P * N`.

Rewrite using `[hNdef]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hm : 2 * (r : ℝ) + k ≤ N` using `by rw [hNdef]; linarith`. Combine the equalities or inequalities in the displayed calculation. Establish `hAS0 : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AS k r`.

Unfold `Formalism.FourierDecayAlt.ThreeDimData.AS Formalism.FourierDecayAlt.ThreeDimData.dN`. Apply `mul_nonneg (Nat.cast_nonneg _)` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities. Establish `hAG : Formalism.FourierDecayAlt.ThreeDimData.AG k r ≤ 4 * N * P`. Unfold `Formalism.FourierDecayAlt.ThreeDimData.AG`.

Establish `: (k : ℝ) + r ≤ N` using `by rw [hNdef]; linarith`. Use the polynomial consequences of the given equalities and inequalities. Establish `hAG0 : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AG k r`. Unfold `Formalism.FourierDecayAlt.ThreeDimData.AG`. Check the signs of the components of the expression.

Establish `hM : Formalism.FourierDecayAlt.ThreeDimData.Mexp r ≤ 2 * P ^ 2`. Unfold `Formalism.FourierDecayAlt.ThreeDimData.Mexp`. Rewrite using `[hPdef]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hM0 : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.Mexp r` using `by unfold Formalism.FourierDecayAlt.ThreeDimData.Mexp; positivity`.

Establish `hP35 : P ^ 3 ≤ P ^ 5` using `pow_le_pow_right₀ hP1 (by norm_num)`. Establish `hP15 : P ≤ P ^ 5` using `by simpa using pow_le_pow_right₀ hP1 (show 1 ≤ 5 by norm_num)`. Establish `hP25 : P ^ 2 ≤ P ^ 5` using `pow_le_pow_right₀ hP1 (by norm_num)`. Establish `hP5 : 1 ≤ P ^ 5` using `one_le_pow₀ hP1`. Establish `hN12 : N ≤ N ^ 2` using `by nlinarith`.

Establish `hN21 : 1 ≤ N ^ 2` using `by nlinarith`. Establish `hN2_0 : 0 ≤ N ^ 2` using `by positivity`. Establish `hP50 : 0 ≤ P ^ 5` using `by positivity`. Establish `hbig : 6000 * P ^ 5 * N ^ 2 ≤ 2000 * P ^ 4 * X`. Rewrite using `[hX]`.

Establish `: 0 ≤ P ^ 4 * N ^ 3` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Establish `m1 : P ^ 3 * N ^ 2 ≤ P ^ 5 * N ^ 2` using `mul_le_mul_of_nonneg_right hP35 hN2_0`. Establish `m2 : P ^ 3 * N ≤ P ^ 5 * N ^ 2` using `mul_le_mul hP35 hN12 (by positivity) hP50`. Establish `m3 : P * N ≤ P ^ 5 * N ^ 2` using `mul_le_mul hP15 hN12 (by positivity) hP50`.

Establish `m4 : (1 : ℝ) ≤ P ^ 5 * N ^ 2` using `one_le_mul_of_one_le_of_one_le hP5 hN21`. Establish `m5 : P * N ^ 2 ≤ P ^ 5 * N ^ 2` using `mul_le_mul_of_nonneg_right hP15 hN2_0`. Establish `m6 : P ^ 2 * N ^ 2 ≤ P ^ 5 * N ^ 2` using `mul_le_mul_of_nonneg_right hP25 hN2_0`. Establish `hprod : Formalism.FourierDecayAlt.ThreeDimData.Mexp r * (Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r) ≤ (2 * P ^ 2) * (2 * P * N ^ 2 + 4 * N * P)` using `mul_le_mul hM (show Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r ≤ 2 * P * N ^ 2 + 4 * N * P by linarith) (add_nonneg hAS0 hAG0) (by nlinarith)`. Establish `hprod2 : ((r : ℝ) + 1) ^ 2 * (Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r) ≤ P ^ 2 * (2 * P * N ^ 2 + 4 * N * P)` using `mul_le_mul_of_nonneg_left (by linarith) (by positivity)`.

Establish `hsqN : 0 ≤ (2 * P) ^ 4 * Real.sqrt (2 * P) - 1`. Establish `: 1 ≤ (2 * P) ^ 4` using `one_le_pow₀ (by linarith)`. Use the polynomial consequences of the given equalities and inequalities. Use `⟨⟨hk, ?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Establish `hX3 : N ^ 3 ≤ X` using `by rw [hX]; nlinarith`.

Establish `hN3 : 0 ≤ N ^ 3` using `by positivity`. Establish `: X ≤ ((2 * P) ^ 4 * Real.sqrt (2 * P)) * X` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[ha]`. Establish `e : 2 * Formalism.FourierDecayAlt.ThreeDimData.Mexp r * (Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r) = 2 * (Formalism.FourierDecayAlt.ThreeDimData.Mexp r * (Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAl …` using `by ring`.

Rewrite using `[e]`. Establish `: (2 * P ^ 2) * (2 * P * N ^ 2 + 4 * N * P) = 4 * (P ^ 3 * N ^ 2) + 8 * (P ^ 3 * N)` using `by ring`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[ha]`. Establish `e : (9 : ℝ) * ((r : ℝ) + 1) * N ^ 2 = 9 * (P * N ^ 2)` using `by rw [← hPdef]; ring`.

Rewrite using `[e]`. Use the polynomial consequences of the given equalities and inequalities. Unfold `GlobalTheory.CellAmp.GapCell`. Rewrite using `[ha]`. Establish `e : 10 * ((r : ℝ) + 1) ^ 2 * (Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r) = 10 * (((r : ℝ) + 1) ^ 2 * (Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r))` using `by ring`.

Rewrite using `[e]`. Establish `: P ^ 2 * (2 * P * N ^ 2 + 4 * N * P) = 2 * (P ^ 3 * N ^ 2) + 4 * (P ^ 3 * N)` using `by ring`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem gap_thresholds (k r : ℕ) (hk : 1 ≤ k) :
    Formalism.FourierDecayAlt.ThreeDimData.GapOK k r (1000 * ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
              (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3)) ∧
      GlobalTheory.CellAmp.GapCell k r (1000 * ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
        (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3)) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hs : ((2 * r + 2 : ℕ) : ℝ) = 2 * ((r : ℝ) + 1) := by push_cast; ring
  have h3 : ((3 * (r + 1) : ℕ) : ℝ) = 3 * ((r : ℝ) + 1) := by push_cast; ring
  have hNdef : ((2 * r + k + 1 : ℕ) : ℝ) = 2 * (r : ℝ) + k + 1 := by push_cast; ring
  rw [hs, h3]
  set P : ℝ := (r : ℝ) + 1 with hPdef
  set N : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hNd
  have hP1 : 1 ≤ P := by linarith
  have hN2 : 2 * P ≤ N := by rw [hNdef]; linarith
  have hN1 : 1 ≤ N := by linarith
  have h2P : 0 < 2 * P := by linarith
  have hsq : 0 < Real.sqrt (2 * P) := Real.sqrt_pos.mpr h2P
  have hsq1 : 1 ≤ Real.sqrt (2 * P) := Real.one_le_sqrt.mpr (by linarith)
  have hrp : (2 * P) ^ ((9 : ℝ) / 2) = (2 * P) ^ 4 * Real.sqrt (2 * P) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add h2P]
    norm_num
  rw [hrp]
  set X : ℝ := 3 * P * N ^ 2 + N ^ 3 with hX
  have ha : Formalism.FourierDecayAlt.ThreeDimData.aOf r (1000 * ((2 * P) ^ 4 * Real.sqrt (2 * P)) * X) = 2000 * P ^ 4 * X := by
    unfold Formalism.FourierDecayAlt.ThreeDimData.aOf
    rw [← hPdef]
    field_simp
    ring

  have hAS : Formalism.FourierDecayAlt.ThreeDimData.AS k r ≤ 2 * P * N ^ 2 := by
    unfold Formalism.FourierDecayAlt.ThreeDimData.AS Formalism.FourierDecayAlt.ThreeDimData.dN
    have e : ((2 * r + k : ℕ) : ℝ) = 2 * (r : ℝ) + k := by push_cast; ring
    rw [e]
    have hd0 : 0 ≤ (r : ℝ) * ((r : ℝ) - 1) + 2 * (r : ℝ) * ((k : ℝ) + 1) + (r : ℝ) ^ 2 := by nlinarith
    have hd : (r : ℝ) * ((r : ℝ) - 1) + 2 * (r : ℝ) * ((k : ℝ) + 1) + (r : ℝ) ^ 2 ≤ 2 * P * N := by
      rw [hNdef]; nlinarith
    have hm : 2 * (r : ℝ) + k ≤ N := by rw [hNdef]; linarith
    calc (2 * (r : ℝ) + k) * ((r : ℝ) * ((r : ℝ) - 1) + 2 * (r : ℝ) * ((k : ℝ) + 1) + (r : ℝ) ^ 2)
        ≤ N * (2 * P * N) := mul_le_mul hm hd hd0 (by linarith)
      _ = 2 * P * N ^ 2 := by ring
  have hAS0 : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AS k r := by
    unfold Formalism.FourierDecayAlt.ThreeDimData.AS Formalism.FourierDecayAlt.ThreeDimData.dN
    apply mul_nonneg (Nat.cast_nonneg _); nlinarith
  have hAG : Formalism.FourierDecayAlt.ThreeDimData.AG k r ≤ 4 * N * P := by
    unfold Formalism.FourierDecayAlt.ThreeDimData.AG
    have : (k : ℝ) + r ≤ N := by rw [hNdef]; linarith
    nlinarith
  have hAG0 : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AG k r := by
    unfold Formalism.FourierDecayAlt.ThreeDimData.AG; positivity
  have hM : Formalism.FourierDecayAlt.ThreeDimData.Mexp r ≤ 2 * P ^ 2 := by
    unfold Formalism.FourierDecayAlt.ThreeDimData.Mexp; rw [hPdef]; nlinarith
  have hM0 : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.Mexp r := by unfold Formalism.FourierDecayAlt.ThreeDimData.Mexp; positivity

  have hP35 : P ^ 3 ≤ P ^ 5 := pow_le_pow_right₀ hP1 (by norm_num)
  have hP15 : P ≤ P ^ 5 := by simpa using pow_le_pow_right₀ hP1 (show 1 ≤ 5 by norm_num)
  have hP25 : P ^ 2 ≤ P ^ 5 := pow_le_pow_right₀ hP1 (by norm_num)
  have hP5 : 1 ≤ P ^ 5 := one_le_pow₀ hP1
  have hN12 : N ≤ N ^ 2 := by nlinarith
  have hN21 : 1 ≤ N ^ 2 := by nlinarith
  have hN2_0 : 0 ≤ N ^ 2 := by positivity
  have hP50 : 0 ≤ P ^ 5 := by positivity
  have hbig : 6000 * P ^ 5 * N ^ 2 ≤ 2000 * P ^ 4 * X := by
    rw [hX]
    have : 0 ≤ P ^ 4 * N ^ 3 := by positivity
    nlinarith
  have m1 : P ^ 3 * N ^ 2 ≤ P ^ 5 * N ^ 2 := mul_le_mul_of_nonneg_right hP35 hN2_0
  have m2 : P ^ 3 * N ≤ P ^ 5 * N ^ 2 := mul_le_mul hP35 hN12 (by positivity) hP50
  have m3 : P * N ≤ P ^ 5 * N ^ 2 := mul_le_mul hP15 hN12 (by positivity) hP50
  have m4 : (1 : ℝ) ≤ P ^ 5 * N ^ 2 := one_le_mul_of_one_le_of_one_le hP5 hN21
  have m5 : P * N ^ 2 ≤ P ^ 5 * N ^ 2 := mul_le_mul_of_nonneg_right hP15 hN2_0
  have m6 : P ^ 2 * N ^ 2 ≤ P ^ 5 * N ^ 2 := mul_le_mul_of_nonneg_right hP25 hN2_0
  have hprod : Formalism.FourierDecayAlt.ThreeDimData.Mexp r * (Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r) ≤
      (2 * P ^ 2) * (2 * P * N ^ 2 + 4 * N * P) :=
    mul_le_mul hM (show Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r ≤ 2 * P * N ^ 2 + 4 * N * P by linarith)
      (add_nonneg hAS0 hAG0) (by nlinarith)
  have hprod2 : ((r : ℝ) + 1) ^ 2 * (Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r) ≤
      P ^ 2 * (2 * P * N ^ 2 + 4 * N * P) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hsqN : 0 ≤ (2 * P) ^ 4 * Real.sqrt (2 * P) - 1 := by
    have : 1 ≤ (2 * P) ^ 4 := one_le_pow₀ (by linarith)
    nlinarith
  refine ⟨⟨hk, ?_, ?_, ?_⟩, ?_⟩
  · have hX3 : N ^ 3 ≤ X := by rw [hX]; nlinarith
    have hN3 : 0 ≤ N ^ 3 := by positivity
    have : X ≤ ((2 * P) ^ 4 * Real.sqrt (2 * P)) * X := by nlinarith
    nlinarith
  · rw [ha]
    have e : 2 * Formalism.FourierDecayAlt.ThreeDimData.Mexp r * (Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r) =
      2 * (Formalism.FourierDecayAlt.ThreeDimData.Mexp r * (Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r)) := by ring
    rw [e]
    have : (2 * P ^ 2) * (2 * P * N ^ 2 + 4 * N * P) = 4 * (P ^ 3 * N ^ 2) + 8 * (P ^ 3 * N) := by ring
    nlinarith
  · rw [ha]
    have e : (9 : ℝ) * ((r : ℝ) + 1) * N ^ 2 = 9 * (P * N ^ 2) := by rw [← hPdef]; ring
    rw [e]
    nlinarith
  · unfold GlobalTheory.CellAmp.GapCell
    rw [ha]
    have e : 10 * ((r : ℝ) + 1) ^ 2 * (Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r) =
      10 * (((r : ℝ) + 1) ^ 2 * (Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r)) := by ring
    rw [e]
    have : P ^ 2 * (2 * P * N ^ 2 + 4 * N * P) = 2 * (P ^ 3 * N ^ 2) + 4 * (P ^ 3 * N) := by ring
    nlinarith

/- English proof (translation)
Use `⟨1000, fun D ε lam hg => ⟨_, hg, ?_⟩⟩` and prove the remaining obligations. Establish `hk : 1 ≤ D.R.k` using `by have := D.R.m_add_three_le_k; omega`. Conclude with `gap_thresholds D.R.k D.R.rS hk`.
-/
theorem gap_constant_exists : ∃ Cgf : ℝ, ∀ (D : Formalism.BasicNotions.D7) (ε : Fin (2 * D.R.rS + D.R.k + 1) → Bool) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ), Formalism.QuantumDeterminants.GapAtLeast ε lam (Cgf * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) * (((3 * (D.R.rS + 1) : ℕ) : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 2 + ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 3)) → ∃ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h ∧ Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h ∧ GlobalTheory.CellAmp.GapCell D.R.k D.R.rS h := by
  refine ⟨1000, fun D ε lam hg => ⟨_, hg, ?_⟩⟩
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  exact gap_thresholds D.R.k D.R.rS hk

end GlobalTheory.GapConstant
