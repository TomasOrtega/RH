import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MoyalOrthogonalityHeisenbergThetaFunctions
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MoyalTheta.orthogonality` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FMoyalOrthogonalityHeisenbergThetaFunctions.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.moyal_orthogonality_heisenberg_thetaFunctions : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (v : VolM D T.rank S.rank) f f₀, IsThetaFunO ψ S T f → IsThetaFunO ψ S T f₀ → Integrable (fun w => thPair v.μ v.𝓕 f (heisO ψ S T w f₀)) v.μ ∧ ∀ x, ∫ w, thPair v.μ v.𝓕 f (heisO ψ S T w f₀) * heisO ψ S T w f₀ x ∂v.μ = thPair v.μ v.𝓕 f₀ f₀ * f x := by
  first | exact @GlobalTheory.MoyalTheta.orthogonality | exact GlobalTheory.MoyalTheta.orthogonality | (intros; apply GlobalTheory.MoyalTheta.orthogonality <;> assumption)
