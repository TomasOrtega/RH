import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealThetaIntertwinerAdjointIsRealThetaIntertwine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FRealThetaIntertwinerAdjointIsRealThetaIntertwine.lean&line=724#L724)
-/
theorem _root_.GlobalTheory.T.realThetaIntertwiner_adjoint_isRealThetaIntertwiner : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (Z P : Type) [AddCommGroup P] [Module ℂ P] (θ : InfFam D) (ω : GA D V × GA D W →* Module.End ℂ (Z → ℂ)) (ω' : GA D W × GA D V →* Module.End ℂ (Z → ℂ)) (pt : P → Z → ℂ) (It : P →ₗ[ℂ] SmT M →ₗ[ℂ] SmT M') (Tp : P → SmT M' →ₗ[ℂ] SmT M), (∀ g h, ω' (h, g) = ω (g, h)) → GlobalTheory.Grid.IsIntw θ M' M ω' pt It → (∀ (p : P) (v : M.Vec) (w : M'.Vec), ellT M' (fun τ => w τ) (inclT M' (It p (PiTensorProduct.tprod ℂ v))) = starRingEnd ℂ (ellT M (fun τ => v τ) (inclT M (Tp p (PiTensorProduct.tprod ℂ w))))) → IsIntwF θ M M' ω pt Tp := by
  first | exact @GlobalTheory.Adopt.realThetaIntertwiner_adjoint_isRealThetaIntertwiner | exact GlobalTheory.Adopt.realThetaIntertwiner_adjoint_isRealThetaIntertwiner | (intros; apply GlobalTheory.Adopt.realThetaIntertwiner_adjoint_isRealThetaIntertwiner <;> assumption)
