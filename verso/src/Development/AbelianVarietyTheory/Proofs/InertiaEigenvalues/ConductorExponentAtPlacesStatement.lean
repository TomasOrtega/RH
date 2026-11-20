import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConductorExponentAtPlaces
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LamTie.expIn_cond0` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FConductorExponentAtPlaces.lean&line=101#L101)
-/
theorem _root_.GlobalTheory.T.conductor_exponent_at_places : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (q0 : ℕ) (w0 : HeightOneSpectrum (𝓞 H.E)), PlacesOk H q0 w0 → ∀ w : HeightOneSpectrum (𝓞 H.E), (Over4 H w → expIn (cond0 H w0) (below w) = 2) ∧ (below w = below w0 → ¬ Over4 H w ∧ expIn (cond0 H w0) (below w) = 1) ∧ (¬ Over4 H w → below w ≠ below w0 → expIn (cond0 H w0) (below w) = 0) := by
  first | exact @GlobalTheory.LamTie.expIn_cond0 | exact GlobalTheory.LamTie.expIn_cond0 | (intros; apply GlobalTheory.LamTie.expIn_cond0 <;> assumption)
