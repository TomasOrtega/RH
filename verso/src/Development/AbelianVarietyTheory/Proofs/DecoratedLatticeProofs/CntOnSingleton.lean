import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RowsPtAt
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyStatementOfItemsFourSeven
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.SBridge
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.MinkowskiDividesFactorialOfBound
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneLeSizeZ
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EquivIntegral
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CntClLeEncardMul
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneLeProdReal
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeanCountPrimitiveSublatticesOverGenus
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeanPrimitiveCorankOneSublatticesBound
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsRawMassAndGenusMass
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma GlobalTheory.Core.Deg

namespace GlobalTheory.Core.Deg

/- English proof (translation)
Introduce `hM c Cg cb Cu cT CT`. Take `⟨C1a, hC1⟩` from `GlobalTheory.Mass.PrimMeanRow.main 1 one_pos`. Take `⟨c3, hC3⟩` from `GlobalTheory.LoopC.PairMean.main Cg cb Cu cT CT c 1 3 (max C1a 0) (le_max_right _ _)`. Take `⟨cH, -, hHH⟩` from `GlobalTheory.GramHeight.height_bounds Cg cb Cu cT CT c 1`. Take `⟨cS, hSW⟩` from `GlobalTheory.LoopC.GenericMean.main Cg cb Cu cT CT c 1`.

Take `⟨c4, hC4⟩` from `GlobalTheory.LoopC.Partner.partners_le Cg cb Cu cT CT c 1`. Use `⟨c3, cH, cS, c4, 1, fun C0 hC0 C' Cl _ hl D large₂ u => ?_⟩` and prove the remaining obligations. Rewrite `hC0` using `[Set.mem_singleton_iff]`. Substitute `hC0` using the available equality. Use `⟨fun C hC => ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `hC3 C hC _ _ u u _ _ hl (GlobalTheory.Mass.RowsRawMass.main _ u) (hC1 _ (le_max_left _ _) _ _ u u _ _ Cg cb Cu cT CT C0 1 hl)`. Conclude with `hHH _ _ u u _ _ hl`. Conclude with `hSW _ _ u u _ _ hl (GlobalTheory.Mass.PrimMeanCorankOne.main _ _ u u _ _ Cg cb Cu cT CT C0 1 (Formalism.MainNotions.BridgeLemma.mass_ratio_of_siegel_cm_unramified hM _))`. Conclude with `hC4 _ _ u u _ _ hl`.
-/
theorem cntOn_singleton : Formalism.HermitianLatticesTheory.SiegelMassRatio → ∀ c : ℝ, CntOn {c} := by
  intro hM c Cg cb Cu cT CT
  obtain ⟨C1a, hC1⟩ := GlobalTheory.Mass.PrimMeanRow.main 1 one_pos
  obtain ⟨c3, hC3⟩ := GlobalTheory.LoopC.PairMean.main Cg cb Cu cT CT c 1 3 (max C1a 0) (le_max_right _ _)
  obtain ⟨cH, -, hHH⟩ := GlobalTheory.GramHeight.height_bounds Cg cb Cu cT CT c 1
  obtain ⟨cS, hSW⟩ := GlobalTheory.LoopC.GenericMean.main Cg cb Cu cT CT c 1
  obtain ⟨c4, hC4⟩ := GlobalTheory.LoopC.Partner.partners_le Cg cb Cu cT CT c 1
  refine ⟨c3, cH, cS, c4, 1, fun C0 hC0 C' Cl _ hl D large₂ u => ?_⟩
  rw [Set.mem_singleton_iff] at hC0
  subst hC0
  refine ⟨fun C hC => ?_, ?_, ?_, ?_⟩
  · exact hC3 C hC _ _ u u _ _ hl (GlobalTheory.Mass.RowsRawMass.main _ u)
      (hC1 _ (le_max_left _ _) _ _ u u _ _ Cg cb Cu cT CT C0 1 hl)
  · exact hHH _ _ u u _ _ hl
  · exact hSW _ _ u u _ _ hl
      (GlobalTheory.Mass.PrimMeanCorankOne.main _ _ u u _ _ Cg cb Cu cT CT C0 1 (Formalism.MainNotions.BridgeLemma.mass_ratio_of_siegel_cm_unramified hM _))
  · exact hC4 _ _ u u _ _ hl

end GlobalTheory.Core.Deg
