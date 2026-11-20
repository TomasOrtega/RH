import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PartialColumnFourierInversionSchwartzBruhat
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingPiCurry
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.ColFourier
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FPartialColumnFourierInversionSchwartzBruhat.lean&line=32#L32)
-/
theorem _root_.GlobalTheory.T.partialColumnFourier_inversion_schwartzBruhat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (A C : Type) [Fintype A] [DecidableEq A] [DecidableEq C] (ψ : AddChar k Circle) (m : Measure k), HasConductor ψ 1 → IsUnitVol m → ∀ (P : Finset C), ∀ Ξ ∈ SB (Matrix A C k), fourierInt ψ⁻¹ m P (fourierInt ψ m P Ξ) = Ξ := by
  first | exact @GlobalTheory.ColFourier.fourierInt_inv_fourierInt | exact GlobalTheory.ColFourier.fourierInt_inv_fourierInt | (intros; apply GlobalTheory.ColFourier.fourierInt_inv_fourierInt <;> assumption)
