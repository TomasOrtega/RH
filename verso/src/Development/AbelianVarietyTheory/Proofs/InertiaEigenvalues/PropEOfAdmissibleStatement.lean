import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PropEOfAdmissible
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ToricFactor.propE` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FPropEOfAdmissible.lean&line=420#L420)
-/
theorem _root_.GlobalTheory.T.propE_of_admissible : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (N0 : X.Tw → ℕ), adm9 X N0 → adm10 X → PropE X N0 := by
  first | exact @GlobalTheory.ToricFactor.propE | exact GlobalTheory.ToricFactor.propE | (intros; apply GlobalTheory.ToricFactor.propE <;> assumption)
