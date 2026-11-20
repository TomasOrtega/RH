import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryReductionPolynomialHeightBound
import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.DenomBound
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FHeightProofs%2FUnitaryReductionPolynomialHeightBound.lean&line=383#L383)
-/
theorem _root_.GlobalTheory.T.unitary_reduction_polynomial_height_bound : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D), IsInfFam θ → OrthoSmall D.host.E → DenomBound θ V → ∃ (d : ℕ) (C : ℝ) (M : ℕ), 0 < d ∧ ∀ g : GA D V, ∃ γ ∈ GQ V, BddDen V d (γ * g) ∧ normInf θ V γ ≤ C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g : ℝ) ^ M := by
  first | exact @GlobalTheory.SmoothForms.Reduce.reduction | exact GlobalTheory.SmoothForms.Reduce.reduction | (intros; apply GlobalTheory.SmoothForms.Reduce.reduction <;> assumption)
