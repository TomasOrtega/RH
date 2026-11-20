import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetUnitaryStabiliserSelfDualLatticeNormOne
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntegralDetOfStable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmulLatMatOf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDatumPeriodIdealFgAndSelfDual
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FDetUnitaryStabiliserSelfDualLatticeNormOne.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.det_unitaryStabiliser_selfDualLattice_normOne : ∀ (D : D7) (X : Fields) (s : Seam D X) (χ : TaylorLogMetric.IdE D → ℂ), s.Ok → TaylorLogMetric.IsChi D χ → ∀ (n : ℕ) (N' : Submodule (𝓞 X.E) (Sp X.E n)), IsSDLat D.host.E n (s.lat N') → ∀ γ : UF X.E n, gmap γ.1 N' = N' → ((LinearEquiv.det γ.1 : X.Eˣ) : X.E) * star ((LinearEquiv.det γ.1 : X.Eˣ) : X.E) = 1 ∧ IsIntegral ℤ ((LinearEquiv.det γ.1 : X.Eˣ) : X.E) ∧ ∏ τ, TaylorLogMetric.embT D τ (s.iE ((LinearEquiv.det γ.1 : X.Eˣ) : X.E)) = 1 := by
  first | exact @GlobalTheory.DetFields.det_of_stab | exact GlobalTheory.DetFields.det_of_stab | (intros; apply GlobalTheory.DetFields.det_of_stab <;> assumption)
