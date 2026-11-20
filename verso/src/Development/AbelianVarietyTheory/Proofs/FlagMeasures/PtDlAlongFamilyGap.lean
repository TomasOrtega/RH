import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Mathlib
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
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyStatementOfItemsFourSeven
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeadingMinorLineUnitAmplitudesLargeGapsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SizesLargeOfPowerBounds
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AmpKF0IffGapIn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CompactCellConvergence.CellConvergence
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory.FamDlGap

/- English proof (translation)
Introduce `_ hH _ Cg cb Cu cT CT C0 C1`. Establish `hA : GlobalTheory.GapIn.AmpKF0` using `GlobalTheory.NoPr.Model.ampKF0_iff_gapIn.mp GlobalTheory.NoPr.Model.ampKF0_holds`. Establish `hCC : GlobalTheory.CellAmp.CellConv` using `Formalism.MainNotions.S.Pv.AmpDDPf.cell_convergence`. Take `⟨C, hC⟩` from `GlobalTheory.T.leadingMinor_line_unitAmplitudes_largeGaps hH hA hCC Cg cb Cu cT CT C0 C1`. Use `⟨C, 1000, fun eps Fm _ hCl _ Cn => ?_⟩` and prove the remaining obligations.

Take `⟨m₀, hm⟩` from `hC Cn`. Take `⟨x0, hx0⟩` from `GlobalTheory.family_sizes_eventually_large eps Fm (max m₀ 1)`. Use `⟨x0, fun x hx i => ?_⟩` and prove the remaining obligations. Take `⟨-, hm1, -, -, hrd, -⟩` from `hx0 x hx i`. Establish `hmm : m₀ ≤ ((Fm.D x i).R.m : ℝ)` using `(le_max_left _ _).trans hm1`.

Establish `hm1' : (1 : ℝ) ≤ ((Fm.D x i).R.m : ℝ)` using `(le_max_right _ _).trans hm1`. Establish `hbig : GlobalTheory.Amp.Big (Fm.D x i) (Fm.L x i) (sCl Fm) m₀` using `⟨hrd, by nlinarith, hmm⟩`. Introduce `hH0`. Conclude with `hm (Fm.D x i) (Fm.L x i) (sC' Fm) (sCl Fm) hCl hbig (Fm.ties x i).cdScale_tie hH0`.
-/
theorem ptDl_along_family_gap : Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS → ∀ Cg cb Cu cT CT C0 C1 : ℝ, ∃ C thr : ℝ, ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT → ∀ Cn : ℝ, OwnEv Fm fun C' Cl x i => VanishingOnXAndXPlusBranching.adm2 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 C := by
  intro _ hH _ Cg cb Cu cT CT C0 C1
  have hA : GlobalTheory.GapIn.AmpKF0 := GlobalTheory.NoPr.Model.ampKF0_iff_gapIn.mp GlobalTheory.NoPr.Model.ampKF0_holds
  have hCC : GlobalTheory.CellAmp.CellConv := Formalism.MainNotions.S.Pv.AmpDDPf.cell_convergence
  obtain ⟨C, hC⟩ := GlobalTheory.T.leadingMinor_line_unitAmplitudes_largeGaps hH hA hCC Cg cb Cu cT CT C0 C1
  refine ⟨C, 1000, fun eps Fm _ hCl _ Cn => ?_⟩
  obtain ⟨m₀, hm⟩ := hC Cn
  obtain ⟨x0, hx0⟩ := GlobalTheory.family_sizes_eventually_large eps Fm (max m₀ 1)
  refine ⟨x0, fun x hx i => ?_⟩
  obtain ⟨-, hm1, -, -, hrd, -⟩ := hx0 x hx i
  have hmm : m₀ ≤ ((Fm.D x i).R.m : ℝ) := (le_max_left _ _).trans hm1
  have hm1' : (1 : ℝ) ≤ ((Fm.D x i).R.m : ℝ) := (le_max_right _ _).trans hm1
  have hbig : GlobalTheory.Amp.Big (Fm.D x i) (Fm.L x i) (sCl Fm) m₀ :=
    ⟨hrd, by nlinarith, hmm⟩
  intro hH0
  exact hm (Fm.D x i) (Fm.L x i) (sC' Fm) (sCl Fm) hCl hbig (Fm.ties x i).cdScale_tie hH0

end GlobalTheory.FamDlGap
