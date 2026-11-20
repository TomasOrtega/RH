import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateKernelAtPoint
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LieInj
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.PlaceShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
open GlobalTheory GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.PDivGroup Matrix TensorProduct NumberField CategoryTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HTKernel.hodgeTateKernelAtPoint` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHodgeTateKernelAtPoint.lean&line=64#L64)
-/
theorem _root_.GlobalTheory.T.hodge_tate_kernel_at_point : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.HodgeTateKernelAtPoint := by
  first | exact @GlobalTheory.HTKernel.hodgeTateKernelAtPoint | exact GlobalTheory.HTKernel.hodgeTateKernelAtPoint | (intros; apply GlobalTheory.HTKernel.hodgeTateKernelAtPoint <;> assumption)
