import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotLocallyFiniteQuadraticMulAddDegreeNonraising
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChosenSeries
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FNotLocallyFiniteQuadraticMulAddDegreeNonraising.lean&line=28#L28)
-/
theorem _root_.GlobalTheory.T.not_locallyFinite_quadraticMul_add_degreeNonraising : ∀ (σ : Type) [Finite σ] (Q : MvPolynomial σ ℂ) (L : Module.End ℂ (MvPolynomial σ ℂ)), Q ≠ 0 → Q.IsHomogeneous 2 → (∀ P, (L P).totalDegree ≤ P.totalDegree) → ∀ φ : MvPolynomial σ ℂ, φ ≠ 0 → ∀ F : Submodule ℂ (MvPolynomial σ ℂ), FiniteDimensional ℂ F → ¬ ∀ n : ℕ, ((LinearMap.mulLeft ℂ Q + L) ^ n) φ ∈ F := by
  first | exact @GlobalTheory.Chain.RealIt.not_locallyFinite_mulLeft_add | exact GlobalTheory.Chain.RealIt.not_locallyFinite_mulLeft_add | (intros; apply GlobalTheory.Chain.RealIt.not_locallyFinite_mulLeft_add <;> assumption)
