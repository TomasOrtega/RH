import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaussianTermMeasurableAndStabilizerInvariant
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.StabUnfold.gaussAt_meas_inv` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FGaussianTermMeasurableAndStabilizerInvariant.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.gaussianTerm_measurable_and_stabilizer_invariant : ∀ (I : AutInst) (x : Fin I.n → I.E), IsOpen {h : I.Gf | x ∈ lamX I (1, h)} ∧ (∀ v, Measurable fun g : Formalism.REAL.UJ (I.ε v) => ENNReal.ofReal (gauss ((uMat g)⁻¹ *ᵥ infVec I v x))) ∧ (∀ h g : I.Gf, I.fmat h *ᵥ afVec I x = afVec I x → (x ∈ lamX I (1, h * g) ↔ x ∈ lamX I (1, g))) ∧ (∀ g : I.Gf, ∀ k ∈ I.Kset, x ∈ lamX I (1, g * k) ↔ x ∈ lamX I (1, g)) ∧ ∀ v (h g : Formalism.REAL.UJ (I.ε v)), uMat h *ᵥ infVec I v x = infVec I v x → (uMat (h * g))⁻¹ *ᵥ infVec I v x = (uMat g)⁻¹ *ᵥ infVec I v x := by
  first | exact @GlobalTheory.StabUnfold.gaussAt_meas_inv | exact GlobalTheory.StabUnfold.gaussAt_meas_inv | (intros; apply GlobalTheory.StabUnfold.gaussAt_meas_inv <;> assumption)
