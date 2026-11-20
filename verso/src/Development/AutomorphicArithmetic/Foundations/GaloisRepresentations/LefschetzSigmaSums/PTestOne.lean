import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HeckeTraceSemi
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.TraceDefinitePairsEqAutomorphicTrace
open UpperTheory.Gal.LocalSmoothExtension

/- English proof (translation)
Introduce `p _ G`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `GlobalTheory.LKMid.isTest_indicator _ _ (by`. Introduce and unpack `_ ⟨k, hk, rfl⟩`. Rewrite using `[GlobalTheory.LKCx.sigG_one]`.

Conclude with `hk)`. Conclude with `GlobalTheory.LKDef.HeckeTraceExample.indicator_bi _`.
-/
theorem UpperTheory.Gal.LocalSmoothExtension.testOne_of :
    TestOne := by
  intro p _ G
  refine ⟨?_, ?_⟩
  · exact GlobalTheory.LKMid.isTest_indicator _ _ (by
      rintro _ ⟨k, hk, rfl⟩
      rw [GlobalTheory.LKCx.sigG_one]
      exact hk)
  · exact GlobalTheory.LKDef.HeckeTraceExample.indicator_bi _
