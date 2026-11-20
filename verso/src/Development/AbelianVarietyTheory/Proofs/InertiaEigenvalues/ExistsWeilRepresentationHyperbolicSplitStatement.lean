import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeilRepresentationHyperbolicSplit
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.JR.weil_hyperbolic` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsWeilRepresentationHyperbolicSplit.lean&line=46#L46)
-/
theorem _root_.GlobalTheory.T.exists_weilRepresentation_hyperbolic_split : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → IsField A.K → ¬ IsField A.L → ∀ (x : A.Kˣ) (μ : Measure A.L), SelfDual μ (A.kerL ψ x) → ∃ W, A.IsWeil ψ x A.etaK μ 1 W := by
  first | exact @GlobalTheory.JR.weil_hyperbolic | exact GlobalTheory.JR.weil_hyperbolic | (intros; apply GlobalTheory.JR.weil_hyperbolic <;> assumption)
