import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.CarchAt
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.QatOfBridgeAlt
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsBoundedByPowerOfAtLeastTwoInvD4ep0

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.BasicNotions Formalism.L2.LamCM GlobalTheory.ArcCM

namespace GlobalTheory.ArcCM.Room

/- English proof (translation)
Establish `hKz : K * z ≤ K * P` using `mul_le_mul_of_nonneg_left hP (by linarith)`. Establish `hKP : 0 ≤ K * P` using `by nlinarith`. Establish `hMP : 0 ≤ M * P` using `mul_nonneg hM (by linarith)`. Establish `hpi` using `Real.pi_le_four`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Establish `h1 : lc / 2 + lL + lr + lR ≤ (1 + 2 * K + M) * P` using `by nlinarith`. Establish `h2` using `mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ s)`. Establish `h3 : 1 ≤ P * s` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities. Use `mul_le_mul_of_nonneg_right ?_ (by linarith)` and prove the remaining obligations.

Use the polynomial consequences of the given equalities and inequalities. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem assemble (K M P z s lc lL lr lR lo ld ln : ℝ) (hz : 1 ≤ z) (hP : z ≤ P) (hK : 1 ≤ K) (hM : 0 ≤ M)
    (hs : 1 ≤ s) (hc : lc ≤ K * z) (hL : lL ≤ M * P) (hr : lr ≤ K * z) (hR : lR ≤ z) (ho : lo ≤ K * z)
    (hd : ld ≤ K * z) (hn : ln ≤ M * P) :
    4 * Real.pi + (lc / 2 + lL + lr + lR) * s ≤ (17 + 2 * K + M) * P * s ∧
    ((1 + lo) / 2 + (1 / 2) * lL) * s ≤ (17 + 2 * K + M) * P * s ∧
    ld + ln ≤ (17 + 2 * K + M) * P := by
  have hKz : K * z ≤ K * P := mul_le_mul_of_nonneg_left hP (by linarith)
  have hKP : 0 ≤ K * P := by nlinarith
  have hMP : 0 ≤ M * P := mul_nonneg hM (by linarith)
  have hpi := Real.pi_le_four
  refine ⟨?_, ?_, ?_⟩
  · have h1 : lc / 2 + lL + lr + lR ≤ (1 + 2 * K + M) * P := by nlinarith
    have h2 := mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ s)
    have h3 : 1 ≤ P * s := by nlinarith
    nlinarith
  · refine mul_le_mul_of_nonneg_right ?_ (by linarith)
    nlinarith
  · nlinarith

/- English proof (translation)
The claim follows from `Real.log_le_self hx`.
-/
theorem log_le_self' {x : ℝ} (hx : 0 ≤ x) : Real.log x ≤ x := Real.log_le_self hx

end GlobalTheory.ArcCM.Room
