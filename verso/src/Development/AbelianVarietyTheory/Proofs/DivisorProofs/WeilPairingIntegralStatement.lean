import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingIntegral
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreNotInClosure
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
open GlobalTheory GlobalTheory.HTLat GlobalTheory.PDivGroup GlobalTheory.WeilIntegral GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel TensorProduct CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ChTor CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.WeilIntegral.Local.weilIntegralLocal_of_cubes` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FWeilPairingIntegral.lean&line=145#L145)
-/
theorem _root_.GlobalTheory.T.weil_pairing_integral : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), HasCubeFn P.A → HasTrivialisingOpen P → TranslatesInto P → CubeValuesIntegral P → WeilIntegralLocal P := by
  first | exact @GlobalTheory.WeilIntegral.Local.weilIntegralLocal_of_cubes | exact GlobalTheory.WeilIntegral.Local.weilIntegralLocal_of_cubes | (intros; apply GlobalTheory.WeilIntegral.Local.weilIntegralLocal_of_cubes <;> assumption)
