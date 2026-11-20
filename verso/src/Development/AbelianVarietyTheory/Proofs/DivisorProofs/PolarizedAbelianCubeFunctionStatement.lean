import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizedAbelianCubeFunction
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreNotInClosure
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
open GlobalTheory GlobalTheory.HTLat GlobalTheory.PDivGroup GlobalTheory.WeilIntegral GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel TensorProduct CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ChTor CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPolarizedAbelianCubeFunction.lean&line=190#L190)
-/
theorem _root_.GlobalTheory.T.polarized_abelian_cube_function : ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (A : Out.PolAV (Sp C)), HasCubeFn A := by
  first | exact @GlobalTheory.WeilIntegral.hasCubeFn | exact GlobalTheory.WeilIntegral.hasCubeFn | (intros; apply GlobalTheory.WeilIntegral.hasCubeFn <;> assumption)
