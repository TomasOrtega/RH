import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PartialColumnFourierEqFiniteFourierSumDepth
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingPiCurry
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.ColFourier
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FPartialColumnFourierEqFiniteFourierSumDepth.lean&line=62#L62)
-/
theorem _root_.GlobalTheory.T.partialColumnFourier_eq_finiteFourierSum_depth : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (A C : Type) [Fintype A] [DecidableEq A] [DecidableEq C] (ψ : AddChar k Circle) (m : Measure k) (ϖ : kˣ), IsUnif ϖ → HasConductor ψ 1 → IsUnitVol m → ∀ (P : Finset C) (n : ℕ) (Φ : Matrix A C k → ℂ), IsNatDatum ϖ n Φ → fourierInt ψ m P Φ = fourierSum ψ ϖ n P Φ := by
  first | exact @GlobalTheory.ColFourier.fourierInt_eq_fourierSum | exact GlobalTheory.ColFourier.fourierInt_eq_fourierSum | (intros; apply GlobalTheory.ColFourier.fourierInt_eq_fourierSum <;> assumption)
